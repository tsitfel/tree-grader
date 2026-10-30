/* ============================================================
 *  cruntime.js — C 인터프리터 런타임 (메모리 모델 · 평가기 · 표준 라이브러리)
 * ============================================================ */
'use strict';

if (typeof require !== 'undefined' && typeof module !== 'undefined') {
  const F = require('./cfront.js');
  Object.assign(globalThis, F);
}

const MEM_SIZE = 16 * 1024 * 1024;
const NULL_GUARD = 0x1000;
const STATIC_BASE = 0x1000;
const STATIC_END = 0x400000;      // 4MB 정적 영역
const STACK_BASE = 0x400000;
const STACK_END = 0x800000;       // 4MB 스택
const HEAP_BASE = 0x800000;
const HEAP_END = MEM_SIZE;        // 8MB 힙
const FN_BASE = 0xF0000000;
const FILE_STDIN = 0xE0000001, FILE_STDOUT = 0xE0000002, FILE_STDERR = 0xE0000003;
const RED_ZONE = 8;

class ExitSignal { constructor(code) { this.code = code; } }

function rtError(ekind, msg, line) {
  const e = new CError('runtime', msg, line);
  e.ekind = ekind;
  return e;
}

function alignUp(x, a) { return Math.ceil(x / a) * a; }

/* 수식을 사람이 읽을 수 있는 문자열로 (오류 메시지용) */
function exprText(e) {
  if (!e) return '';
  switch (e.kind) {
    case 'ident': return e.name;
    case 'num': return String(e.v);
    case 'str': return '"..."';
    case 'member': return exprText(e.e) + (e.arrow ? '->' : '.') + e.name;
    case 'index': return exprText(e.a) + '[' + exprText(e.i) + ']';
    case 'unary': return e.op + exprText(e.e);
    case 'call': return exprText(e.f) + '(...)';
    case 'cast': return '(' + typeName(e.type) + ')' + exprText(e.e);
    case 'binary': return exprText(e.l) + ' ' + e.op + ' ' + exprText(e.r);
    case 'assign': return exprText(e.l) + ' ' + e.op + ' ' + exprText(e.r);
    case 'postinc': return exprText(e.e) + e.op;
    case 'preinc': return e.op + exprText(e.e);
    case 'sizeof': return 'sizeof(...)';
    case 'cond': return exprText(e.c) + ' ? ... : ...';
    case 'comma': return exprText(e.l) + ', ' + exprText(e.r);
  }
  return '?';
}

class Runtime {
  constructor(unit, env, opts) {
    this.unit = unit;
    this.env = env;
    this.opts = Object.assign({ maxSteps: 5000000, maxOutput: 1 << 20, timeLimitMs: 4000, maxDepth: 1000 }, opts || {});
    this.buf = new ArrayBuffer(MEM_SIZE);
    this.dv = new DataView(this.buf);
    this.u8 = new Uint8Array(this.buf);
    this.shadow = new Uint8Array(MEM_SIZE);
    this.staticTop = STATIC_BASE;
    this.sp = STACK_BASE;
    this.heapTop = HEAP_BASE;
    this.hStart = []; this.hSize = []; this.hLive = [];
    this.funcs = new Map();      // name -> {kind:'user', node} | {kind:'builtin', ...}
    this.fnById = [];            // id -> func entry
    this.globals = new Map();    // name -> {addr, type}
    this.scopes = [this.globals];
    this.statics = new Map();    // decl node -> addr
    this.strAddr = new Map();    // string literal node id -> addr
    this.steps = 0;
    this.depth = 0;
    this.line = 0;
    this.out = []; this.err = [];
    this.outLen = 0;
    this.inBuf = new Uint8Array(0); this.inPos = 0; this.eofReads = 0;
    this.randState = 1;
    this.startTime = 0;
    this.exitCode = 0;
    this.installBuiltins();
  }

  /* ---------- 메모리 접근 ---------- */
  describeAddr(addr) {
    if (addr === 0) return 'NULL 포인터';
    if (addr < NULL_GUARD) return `NULL 포인터에서 ${addr}바이트 떨어진 위치(NULL 포인터의 멤버 접근)`;
    return `주소 0x${addr.toString(16)}`;
  }
  checkAccess(addr, size, write, what) {
    if (addr < NULL_GUARD) {
      throw rtError('null-deref', `${what ? what + ': ' : ''}${this.describeAddr(addr)}를 ${write ? '쓰기' : '읽기'} 위해 역참조했습니다. 포인터가 NULL(외부노드의 자식 등)인지 먼저 확인해야 합니다.`, this.line);
    }
    if (addr >= STACK_BASE && addr + size <= STACK_END) {
      if (addr >= this.sp) throw rtError('dead-stack', `${what ? what + ': ' : ''}이미 소멸된 지역변수의 메모리(${this.describeAddr(addr)})에 접근했습니다. 함수가 끝나면 사라지는 지역변수의 주소를 반환·저장했는지 확인하세요.`, this.line);
      return;
    }
    if (addr >= STATIC_BASE && addr + size <= this.staticTop) return;
    if (addr >= HEAP_BASE && addr < HEAP_END) {
      const idx = this.findBlock(addr);
      if (idx < 0 || addr + size > this.hStart[idx] + this.hSize[idx]) {
        if (idx >= 0 && addr < this.hStart[idx] + this.hSize[idx] + RED_ZONE + 8) {
          throw rtError('heap-oob', `${what ? what + ': ' : ''}malloc으로 할당한 ${this.hSize[idx]}바이트 블록의 범위를 벗어나 ${write ? '썼' : '읽었'}습니다 (블록 시작 +${addr - this.hStart[idx]}, ${size}바이트). sizeof(구조체) 대신 sizeof(포인터)만큼 할당했거나, 배열 인덱스가 범위를 넘었는지 확인하세요.`, this.line);
        }
        throw rtError('invalid-addr', `${what ? what + ': ' : ''}할당되지 않은 힙 메모리(${this.describeAddr(addr)})에 접근했습니다. 초기화되지 않은 포인터나 잘못된 포인터 연산이 원인일 수 있습니다.`, this.line);
      }
      if (!this.hLive[idx]) throw rtError('use-after-free', `${what ? what + ': ' : ''}free()로 이미 해제된 메모리(${this.describeAddr(addr)})를 ${write ? '썼' : '읽었'}습니다. free 한 노드의 포인터를 그 뒤에 다시 사용하지 않는지(예: free 후 w->parent 접근) 확인하세요.`, this.line);
      return;
    }
    if (addr >= FN_BASE) throw rtError('invalid-addr', `${what ? what + ': ' : ''}함수 주소를 데이터 메모리처럼 접근했습니다.`, this.line);
    if (addr >= FILE_STDIN - 8 && addr <= FILE_STDERR + 8) throw rtError('invalid-addr', `${what ? what + ': ' : ''}FILE 포인터(stdin/stdout/stderr)를 역참조했습니다.`, this.line);
    throw rtError('invalid-addr', `${what ? what + ': ' : ''}유효하지 않은 메모리 주소(${this.describeAddr(addr)})에 접근했습니다. 초기화되지 않은 포인터(쓰레기값)를 사용했는지 확인하세요.`, this.line);
  }
  findBlock(addr) {
    let lo = 0, hi = this.hStart.length - 1, ans = -1;
    while (lo <= hi) { const m = (lo + hi) >> 1; if (this.hStart[m] <= addr) { ans = m; lo = m + 1; } else hi = m - 1; }
    return ans;
  }
  checkInit(addr, size, what) {
    for (let k = 0; k < size; k++) {
      if (!this.shadow[addr + k]) {
        throw rtError('uninit', `${what ? "'" + what + "' 은(는) " : ''}값이 저장된 적 없는(초기화되지 않은) 메모리를 읽었습니다. 변수/구조체 멤버에 값을 넣기 전에 사용했는지 확인하세요 (예: 새 노드의 parent·left·right·height 설정 누락, 변수 선언 후 초기화 누락).`, this.line);
      }
    }
  }
  load(addr, t, what) {
    const size = t.size;
    this.checkAccess(addr, size, false, what);
    this.checkInit(addr, size, what);
    const dv = this.dv;
    switch (t.k) {
      case 'int':
        switch (size) {
          case 1: return t.signed ? dv.getInt8(addr) : dv.getUint8(addr);
          case 2: return t.signed ? dv.getInt16(addr, true) : dv.getUint16(addr, true);
          case 4: return t.signed ? dv.getInt32(addr, true) : dv.getUint32(addr, true);
          case 8: return Number(t.signed ? dv.getBigInt64(addr, true) : dv.getBigUint64(addr, true));
        }
        break;
      case 'float': return size === 4 ? dv.getFloat32(addr, true) : dv.getFloat64(addr, true);
      case 'ptr': return dv.getUint32(addr, true);
    }
    throw rtError('type', `타입 ${typeName(t)} 의 값을 읽을 수 없습니다.`, this.line);
  }
  store(addr, t, v, what) {
    const size = t.size;
    this.checkAccess(addr, size, true, what);
    const dv = this.dv;
    switch (t.k) {
      case 'int':
        switch (size) {
          case 1: dv.setUint8(addr, v & 0xff); break;
          case 2: dv.setUint16(addr, v & 0xffff, true); break;
          case 4: dv.setUint32(addr, v >>> 0, true); break;
          case 8: dv.setBigInt64(addr, BigInt.asIntN(64, BigInt(Math.trunc(v))), true); break;
        }
        break;
      case 'float': if (size === 4) dv.setFloat32(addr, v, true); else dv.setFloat64(addr, v, true); break;
      case 'ptr': dv.setUint32(addr, v >>> 0, true); break;
      default: throw rtError('type', `타입 ${typeName(t)} 의 값을 저장할 수 없습니다.`, this.line);
    }
    this.shadow.fill(1, addr, addr + size);
  }
  copyBytes(dst, src, size, what) {
    this.checkAccess(src, size, false, what);
    this.checkAccess(dst, size, true, what);
    this.u8.copyWithin(dst, src, src + size);
    this.shadow.copyWithin(dst, src, src + size);
  }
  zeroInit(addr, size) { this.u8.fill(0, addr, addr + size); this.shadow.fill(1, addr, addr + size); }
  readCString(addr, what, maxLen = 1 << 20) {
    const bytes = [];
    for (let i = 0; i < maxLen; i++) {
      this.checkAccess(addr + i, 1, false, what);
      this.checkInit(addr + i, 1, what);
      const b = this.u8[addr + i];
      if (b === 0) return bytes;
      bytes.push(b);
    }
    throw rtError('invalid-addr', `${what || '문자열'} 의 끝(NUL 문자)을 찾을 수 없습니다.`, this.line);
  }
  writeCString(addr, bytes, what) {
    this.checkAccess(addr, bytes.length + 1, true, what);
    for (let i = 0; i < bytes.length; i++) this.u8[addr + i] = bytes[i];
    this.u8[addr + bytes.length] = 0;
    this.shadow.fill(1, addr, addr + bytes.length + 1);
  }

  allocStatic(size, align) {
    const a = alignUp(this.staticTop, Math.max(align || 1, 1));
    if (a + size > STATIC_END) throw rtError('out-of-memory', '전역/정적 변수 영역(4MB)이 부족합니다. 배열 크기를 확인하세요.', this.line);
    this.staticTop = a + size;
    return a;
  }
  allocStack(size, align) {
    const a = alignUp(this.sp, Math.max(align || 1, 1));
    if (a + size > STACK_END) throw rtError('stack-overflow', '스택 메모리(4MB)를 초과했습니다. 재귀 호출이 끝나지 않거나(종료 조건 확인) 지역 배열이 너무 큽니다.', this.line);
    this.sp = a + size;
    this.shadow.fill(0, a, a + size);
    return a;
  }
  heapAlloc(size) {
    size = Math.max(0, Math.trunc(size));
    const a = alignUp(this.heapTop, 8);
    const total = alignUp(Math.max(size, 1) + RED_ZONE, 8);
    if (a + total > HEAP_END) throw rtError('out-of-memory', `힙 메모리(8MB)가 부족합니다 (malloc 요청 ${size}바이트). 반복문 안에서 malloc 이 무한히 호출되는지 확인하세요.`, this.line);
    this.heapTop = a + total;
    this.hStart.push(a); this.hSize.push(size); this.hLive.push(true);
    this.shadow.fill(0, a, a + total);
    return a;
  }
  heapFree(addr) {
    if (addr === 0) return;
    const idx = this.findBlock(addr);
    if (addr < HEAP_BASE || addr >= HEAP_END || idx < 0 || this.hStart[idx] !== addr) {
      if (addr >= STACK_BASE && addr < STACK_END) throw rtError('bad-free', `free(): 지역변수(스택)의 주소를 free 했습니다. free 는 malloc 으로 받은 주소에만 사용할 수 있습니다.`, this.line);
      if (idx >= 0 && addr < this.hStart[idx] + this.hSize[idx]) throw rtError('bad-free', `free(): malloc 으로 받은 시작 주소가 아닌 블록 중간 주소를 free 했습니다.`, this.line);
      throw rtError('bad-free', `free(): malloc 으로 할당한 주소가 아닌 값(${this.describeAddr(addr)})을 free 했습니다. 초기화되지 않은 포인터인지 확인하세요.`, this.line);
    }
    if (!this.hLive[idx]) throw rtError('double-free', `free(): 이미 해제된 메모리를 다시 free 했습니다 (double free). 같은 노드를 두 번 free 하지 않는지 확인하세요.`, this.line);
    this.hLive[idx] = false;
  }

  /* ---------- 출력/입력 ---------- */
  writeOut(bytes, isErr) {
    const arr = isErr ? this.err : this.out;
    for (let i = 0; i < bytes.length; i++) arr.push(bytes[i]);
    if (!isErr) {
      this.outLen += bytes.length;
      if (this.outLen > this.opts.maxOutput) throw rtError('output-limit', `출력이 너무 많습니다 (${(this.opts.maxOutput / 1024) | 0}KB 초과). 무한 반복 출력인지 확인하세요.`, this.line);
    }
  }
  writeStr(s, isErr) { this.writeOut(Array.from(new TextEncoder().encode(s)), isErr); }
  inPeek() { return this.inPos < this.inBuf.length ? this.inBuf[this.inPos] : -1; }
  inNext() { if (this.inPos < this.inBuf.length) return this.inBuf[this.inPos++]; this.eofReads++; return -1; }

  /* ---------- 준비 ---------- */
  installBuiltins() { installStdlib(this); }
  registerFn(name, entry) {
    entry.id = FN_BASE + this.fnById.length;
    entry.name = name;
    this.fnById.push(entry);
    this.funcs.set(name, entry);
    return entry;
  }
  fnByAddr(v) {
    const idx = v - FN_BASE;
    if (idx >= 0 && idx < this.fnById.length) return this.fnById[idx];
    return null;
  }

  tick() {
    if ((++this.steps & 0x3ff) === 0) {
      if (this.steps > this.opts.maxSteps) throw rtError('timeout', `실행 단계가 ${this.opts.maxSteps.toLocaleString()}회를 넘었습니다 (시간 초과). 반복문이 끝나지 않거나(무한 루프) 'q' 명령 처리가 빠졌는지 확인하세요.`, this.line);
      if (Date.now() - this.startTime > this.opts.timeLimitMs) throw rtError('timeout', `실행 시간이 ${this.opts.timeLimitMs / 1000}초를 넘었습니다 (시간 초과). 반복문이 끝나지 않거나(무한 루프) 'q' 명령 처리가 빠졌는지 확인하세요.`, this.line);
    }
  }

  run(input) {
    this.startTime = Date.now();
    this.inBuf = new TextEncoder().encode(input || '');
    this.inPos = 0;
    try {
      this.link();
      const main = this.funcs.get('main');
      if (!main || main.kind !== 'user') throw rtError('no-main', 'main 함수가 정의되지 않았습니다. 프로그램은 main 함수에서 시작합니다.', 0);
      const ft = main.node.type;
      const args = [];
      if (ft.params.length >= 1) args.push({ t: TY.int, v: 1 });
      if (ft.params.length >= 2) {
        const sa = this.allocStatic(5, 1); this.writeCString(sa, [109, 97, 105, 110], 'argv');
        const av = this.allocStatic(8, 4); this.store(av, ptrTo(TY.char), sa); this.store(av + 4, ptrTo(TY.char), 0);
        args.push({ t: ptrTo(ptrTo(TY.char)), v: av });
      }
      const r = this.callUser(main, args, main.node.line);
      this.exitCode = (ft.ret.k === 'void') ? 0 : (r.v | 0);
    } catch (e) {
      if (e instanceof ExitSignal) { this.exitCode = e.code; }
      else throw e;
    }
    return this.exitCode;
  }

  link() {
    const unit = this.unit;
    // 문자열 리터럴
    for (const s of unit.stringLits) {
      const a = this.allocStatic(s.bytes.length + 1, 1);
      this.writeCString(a, s.bytes, 'string literal');
      this.strAddr.set(s.id, a);
    }
    // 함수 등록 (정의가 먼저 보여야 호출 전 선언 없이도 동작)
    for (const d of unit.decls) {
      if (d.kind === 'func') {
        if (this.funcs.has(d.name) && this.funcs.get(d.name).kind === 'user' && this.funcs.get(d.name).node) {
          throw new CError('compile', `함수 '${d.name}' 가 두 번 정의되었습니다.`, d.line);
        }
        if (this.funcs.has(d.name) && this.funcs.get(d.name).kind === 'builtin') {
          // 사용자가 표준 함수를 재정의하면 사용자 정의를 우선
          const e = this.funcs.get(d.name); e.kind = 'user'; e.node = d; e.type = d.type;
          continue;
        }
        const existing = this.funcs.get(d.name);
        if (existing) { existing.node = d; existing.type = d.type; existing.kind = 'user'; }
        else this.registerFn(d.name, { kind: 'user', node: d, type: d.type });
      } else if (d.kind === 'funcdecl') {
        if (!this.funcs.has(d.name)) this.registerFn(d.name, { kind: 'user', node: null, type: d.type });
      }
    }
    // 식별자 검사 (선언되지 않은 이름을 실행 전에 잡는다)
    this.checkIdentifiers();
    // 전역 변수
    for (const d of unit.decls) {
      if (d.kind === 'var') {
        if (this.globals.has(d.name)) {
          if (d.storage === 'extern' || !d.init) continue;
        }
        const addr = this.allocStatic(d.type.size, d.type.align);
        this.zeroInit(addr, d.type.size);
        this.globals.set(d.name, { addr, type: d.type });
        if (d.init) { this.line = d.line; this.initObject(addr, d.type, d.init, d.name); }
      }
    }
    for (const [name, f] of this.funcs) {
      if (f.kind === 'user' && !f.node && f.referenced) throw new CError('compile', `함수 '${name}' 가 선언만 되고 정의되지 않았습니다.`, f.refLine || 0);
    }
  }

  checkIdentifiers() {
    const rt = this;
    const unit = this.unit;
    const globalNames = new Map();
    for (const d of unit.decls) if (d.kind === 'var') globalNames.set(d.name, d.type);
    const typeOfIdent = (name, scopes) => {
      for (let i = scopes.length - 1; i >= 0; i--) if (scopes[i].has(name)) return scopes[i].get(name);
      return globalNames.get(name) || null;
    };
    const checkScanfArgs = (e, scopes) => {
      if (e.f.kind !== 'ident') return;
      const first = { scanf: 1, scanf_s: 1, fscanf: 2, sscanf: 2, fscanf_s: 2, sscanf_s: 2 }[e.f.name];
      if (first == null || typeOfIdent(e.f.name, scopes)) return;
      for (let i = first; i < e.args.length; i++) {
        const a = e.args[i];
        if (a.kind !== 'ident') continue;
        const t = typeOfIdent(a.name, scopes);
        if (t && (t.k === 'int' || t.k === 'float'))
          throw new CError('compile', `${e.f.name}() 의 ${i + 1}번째 인자 '${a.name}' 은(는) ${typeName(t)} 변수입니다. 입력값을 저장하려면 변수의 주소를 넘겨야 하므로 '&${a.name}' 으로 써야 합니다.`, e.line);
      }
    };
    const checkExpr = (e, scopes) => {
      if (!e) return;
      switch (e.kind) {
        case 'ident': {
          for (let i = scopes.length - 1; i >= 0; i--) if (scopes[i].has(e.name)) return;
          if (globalNames.has(e.name)) return;
          if (rt.funcs.has(e.name)) { const f = rt.funcs.get(e.name); f.referenced = true; if (!f.refLine) f.refLine = e.line; return; }
          if (rt.globals.has(e.name)) return;
          let hint = '';
          const low = e.name.toLowerCase();
          const cands = [];
          for (const s of scopes) for (const n of s.keys()) cands.push(n);
          for (const n of globalNames.keys()) cands.push(n);
          for (const n of rt.funcs.keys()) cands.push(n);
          const near = cands.filter(n => n.toLowerCase() === low || editDistance(n, e.name) <= 2 && n.length > 2);
          if (near.length) hint = ` 비슷한 이름: ${[...new Set(near)].slice(0, 3).map(n => "'" + n + "'").join(', ')}.`;
          else if (['isInternal', 'isExternal', 'isRoot', 'sibling', 'inOrderSucc', 'expandExternal', 'reduceExternal', 'treeSearch', 'restructure'].includes(e.name)) hint = ` 교재의 함수 ${e.name}() 을 직접 구현해야 합니다.`;
          throw new CError('compile', `선언되지 않은 식별자 '${e.name}' 를 사용했습니다.${hint}`, e.line);
        }
        case 'num': case 'str': return;
        case 'member': checkExpr(e.e, scopes); return;
        case 'index': checkExpr(e.a, scopes); checkExpr(e.i, scopes); return;
        case 'unary': case 'preinc': case 'postinc': checkExpr(e.e, scopes); return;
        case 'cast': checkExpr(e.e, scopes); return;
        case 'sizeof': if (e.e) checkExpr(e.e, scopes); return;
        case 'binary': case 'assign': case 'comma': checkExpr(e.l, scopes); checkExpr(e.r, scopes); return;
        case 'cond': checkExpr(e.c, scopes); checkExpr(e.a, scopes); checkExpr(e.b, scopes); return;
        case 'call': checkExpr(e.f, scopes); for (const a of e.args) checkExpr(a, scopes); checkScanfArgs(e, scopes); return;
        case 'initlist': for (const it of e.items) checkExpr(it, scopes); return;
      }
    };
    const checkStmt = (s, scopes) => {
      if (!s) return;
      switch (s.kind) {
        case 'block': { scopes.push(new Map()); for (const st of s.stmts) checkStmt(st, scopes); scopes.pop(); return; }
        case 'decl': for (const d of s.decls) { if (d.kind === 'var') { scopes[scopes.length - 1].set(d.name, d.type); if (d.init) checkExpr(d.init, scopes); } } return;
        case 'expr': checkExpr(s.expr, scopes); return;
        case 'if': checkExpr(s.cond, scopes); checkStmt(s.then, scopes); checkStmt(s.els, scopes); return;
        case 'while': case 'dowhile': checkExpr(s.cond, scopes); checkStmt(s.body, scopes); return;
        case 'for': scopes.push(new Map()); checkStmt(s.init, scopes); checkExpr(s.cond, scopes); checkExpr(s.step, scopes); checkStmt(s.body, scopes); scopes.pop(); return;
        case 'switch': checkExpr(s.expr, scopes); checkStmt(s.body, scopes); return;
        case 'case': case 'default': checkStmt(s.stmt, scopes); return;
        case 'return': checkExpr(s.expr, scopes); return;
      }
    };
    for (const d of unit.decls) {
      if (d.kind === 'func') {
        const ps = new Map(d.type.params.map(p => [p.name, p.type]));
        checkStmt(d.body, [ps]);
      } else if (d.kind === 'var' && d.init) checkExpr(d.init, []);
    }
  }

  /* ---------- 변수 ---------- */
  lookup(name) {
    for (let i = this.scopes.length - 1; i >= 0; i--) { const v = this.scopes[i].get(name); if (v) return v; }
    return null;
  }
  declareLocal(d) {
    const scope = this.scopes[this.scopes.length - 1];
    if (d.isStatic) {
      let addr = this.statics.get(d);
      if (addr == null) {
        addr = this.allocStatic(d.type.size, d.type.align);
        this.zeroInit(addr, d.type.size);
        this.statics.set(d, addr);
        if (d.init) this.initObject(addr, d.type, d.init, d.name);
      }
      scope.set(d.name, { addr, type: d.type });
      return;
    }
    const addr = this.allocStack(d.type.size, d.type.align);
    scope.set(d.name, { addr, type: d.type });
    if (d.init) this.initObject(addr, d.type, d.init, d.name);
  }
  initObject(addr, t, init, what) {
    if (init.kind === 'initlist') {
      this.zeroInit(addr, t.size);
      const pos = this.initFromList(addr, t, init.items, 0, what);
      if (pos < init.items.length) throw new CError('compile', `'${what}' 의 초기값이 너무 많습니다 (${init.items.length}개).`, init.line);
      return;
    }
    if (t.k === 'arr') {
      if (init.kind === 'str' && t.of.k === 'int' && t.of.size === 1) {
        if (init.bytes.length > t.n) throw new CError('compile', `문자열 초기값이 배열 '${what}' 의 크기(${t.n})보다 깁니다.`, init.line);
        this.zeroInit(addr, t.size);
        for (let i = 0; i < init.bytes.length; i++) this.u8[addr + i] = init.bytes[i];
        return;
      }
      throw new CError('compile', `배열 '${what}' 은 { } 목록으로 초기화해야 합니다.`, init.line);
    }
    this.initScalar(addr, t, init, what);
  }
  initScalar(addr, t, init, what) {
    if (init.kind === 'initlist') { this.initObject(addr, t, init, what); return; }
    const v = this.evalR(init);
    if (t.k === 'struct') {
      if (v.t.k !== 'struct' || v.t !== t) throw rtError('type', `'${what}' (${typeName(t)}) 에 ${typeName(v.t)} 값을 넣을 수 없습니다.`, init.line);
      this.copyBytes(addr, v.v, t.size, what);
      return;
    }
    this.store(addr, t, this.convert(v, t, init.line, what).v, what);
  }
  // 중괄호 생략(brace elision)을 지원하는 집합체 초기화. 소비한 항목 수 위치를 반환
  initFromList(addr, t, items, pos, what) {
    if (t.k === 'arr') {
      const et = t.of;
      for (let i = 0; i < t.n && pos < items.length; i++) {
        const it = items[pos];
        const ea = addr + i * et.size;
        if (it.kind === 'initlist') { this.initObject(ea, et, it, `${what}[${i}]`); pos++; }
        else if (et.k === 'arr' && it.kind === 'str' && et.of.k === 'int' && et.of.size === 1) { this.initObject(ea, et, it, `${what}[${i}]`); pos++; }
        else if (et.k === 'arr' || (et.k === 'struct' && !(it.kind !== 'initlist' && this.typeOfSafe(it) === et))) pos = this.initFromList(ea, et, items, pos, `${what}[${i}]`);
        else { this.initScalar(ea, et, it, `${what}[${i}]`); pos++; }
      }
      return pos;
    }
    if (t.k === 'struct') {
      const fields = t.union ? t.fields.slice(0, 1) : t.fields;
      for (const f of fields) {
        if (pos >= items.length) break;
        const it = items[pos];
        const fa = addr + f.offset;
        if (it.kind === 'initlist') { this.initObject(fa, f.type, it, `${what}.${f.name}`); pos++; }
        else if (f.type.k === 'arr' && it.kind === 'str' && f.type.of.k === 'int' && f.type.of.size === 1) { this.initObject(fa, f.type, it, `${what}.${f.name}`); pos++; }
        else if (f.type.k === 'arr' || (f.type.k === 'struct' && this.typeOfSafe(it) !== f.type)) pos = this.initFromList(fa, f.type, items, pos, `${what}.${f.name}`);
        else { this.initScalar(fa, f.type, it, `${what}.${f.name}`); pos++; }
      }
      return pos;
    }
    if (pos < items.length) { this.initScalar(addr, t, items[pos], what); pos++; }
    return pos;
  }
  typeOfSafe(e) { try { return this.typeOf(e); } catch (err) { return null; } }

  /* ---------- 형 변환 ---------- */
  convert(val, to, line, what) {
    this.useCheck(val, line);
    const from = val.t;
    if (to.k === 'void') return { t: TY.void, v: 0 };
    if (from.k === 'void') throw rtError('type', `void 값(값을 반환하지 않는 함수의 결과)을 ${what ? "'" + what + "' 에 " : ''}사용했습니다.`, line || this.line);
    if (from.k === 'struct' || to.k === 'struct') {
      if (from === to) return val;
      throw rtError('type', `${typeName(from)} 값을 ${typeName(to)} 으로 변환할 수 없습니다${what ? " ('" + what + "')" : ''}. 구조체 자체가 아니라 구조체 포인터(->)를 쓰려던 것은 아닌지 확인하세요.`, line || this.line);
    }
    if (from.k === 'arr' || from.k === 'fn') throw rtError('type', `${typeName(from)} 값을 ${typeName(to)} 으로 변환할 수 없습니다.`, line || this.line);
    let v = val.v;
    if (to.k === 'int') {
      if (from.k === 'ptr' && !val.fromCast)
        throw rtError('type', `포인터 값(${typeName(from)})을 정수 ${typeName(to)}${what ? " ('" + what + "')" : ''} 에 넣었습니다. 노드 포인터가 아니라 노드의 키(->key)를 넣어야 하는지 확인하세요.`, line || this.line);
      if (from.k === 'float') { if (!isFinite(v)) v = 0; v = Math.trunc(v); }
      return { t: to, v: wrapInt(v, to) };
    }
    if (to.k === 'float') return { t: to, v: to.size === 4 ? Math.fround(v) : +v };
    if (to.k === 'ptr') {
      if (from.k === 'float') throw rtError('type', `실수 값을 포인터 ${typeName(to)} 에 넣을 수 없습니다.`, line || this.line);
      if (from.k === 'int' && v !== 0 && !val.fromCast)
        throw rtError('type', `정수 값 ${v} 을(를) 포인터 ${typeName(to)}${what ? " ('" + what + "')" : ''} 에 넣었습니다. 키 값과 노드 포인터를 혼동했거나 & 가 빠졌는지 확인하세요.`, line || this.line);
      return { t: to, v: v >>> 0 };
    }
    throw rtError('type', `${typeName(from)} 값을 ${typeName(to)} 으로 변환할 수 없습니다.`, line || this.line);
  }
  useCheck(val, line) {
    if (val && val.noReturn) throw rtError('no-return', `함수 '${val.noReturn}' (반환형 ${typeName(val.t)}) 이 return 문 없이 끝났는데 그 반환값을 사용했습니다. 모든 경로에서 값을 반환하는지 확인하세요 (예: 재귀 호출 결과를 return 하지 않음, else 분기 누락).`, line || this.line);
  }
  truthy(val) {
    this.useCheck(val);
    if (val.t.k === 'struct') throw rtError('type', `구조체 값은 조건식에 쓸 수 없습니다.`, this.line);
    if (val.t.k === 'void') throw rtError('type', `void 값(값을 반환하지 않는 함수의 결과)을 조건식에 사용했습니다. 함수의 반환형과 return 문을 확인하세요.`, this.line);
    return val.v !== 0;
  }

  /* ---------- 수식 평가 ---------- */
  // 왼값: {addr, t}
  evalL(e) {
    switch (e.kind) {
      case 'ident': {
        const v = this.lookup(e.name);
        if (v) return { addr: v.addr, t: v.type, name: e.name };
        if (this.funcs.has(e.name)) return { fn: this.funcs.get(e.name), t: this.funcs.get(e.name).type || fnType(TY.int, [], true), name: e.name };
        throw rtError('undeclared', `선언되지 않은 식별자 '${e.name}' 입니다.`, e.line);
      }
      case 'str': return { addr: this.strAddr.get(e.id), t: arrOf(TY.char, e.bytes.length + 1) };
      case 'member': {
        let base, st;
        if (e.arrow) {
          const p = this.evalR(e.e);
          this.useCheck(p, e.line);
          if (p.t.k !== 'ptr') {
            if (p.t.k === 'struct') throw rtError('type', `'${exprText(e.e)}' 은(는) 포인터가 아니라 구조체이므로 '->' 대신 '.' 을 써야 합니다.`, e.line);
            throw rtError('type', `'${exprText(e.e)}' (${typeName(p.t)}) 은(는) 구조체 포인터가 아니므로 '->' 를 쓸 수 없습니다.`, e.line);
          }
          st = p.t.to;
          if (st.k !== 'struct') throw rtError('type', `'${exprText(e.e)}' 은(는) 구조체를 가리키는 포인터가 아닙니다 (${typeName(p.t)}).`, e.line);
          base = p.v;
          if (base < NULL_GUARD) throw rtError('null-deref', `'${exprText(e.e)}' 이(가) NULL 인데 멤버 '${e.name}' 에 접근했습니다. 외부노드(잎)의 자식은 NULL 이므로, 접근 전에 isExternal 검사 등으로 NULL 여부를 확인해야 합니다.`, e.line);
        } else {
          const lv = this.evalL(e.e);
          if (lv.t.k === 'ptr') throw rtError('type', `'${exprText(e.e)}' 은(는) 포인터이므로 '.' 대신 '->' 를 써야 합니다.`, e.line);
          if (lv.t.k !== 'struct') throw rtError('type', `'${exprText(e.e)}' (${typeName(lv.t)}) 은(는) 구조체가 아니므로 멤버 '${e.name}' 에 접근할 수 없습니다.`, e.line);
          st = lv.t; base = lv.addr;
        }
        if (!st.complete) throw rtError('type', `${typeName(st)} 이 정의되지 않았습니다.`, e.line);
        const f = st.fields.find(f => f.name === e.name);
        if (!f) {
          const names = st.fields.map(f => f.name).join(', ');
          throw rtError('type', `${typeName(st)} 에는 멤버 '${e.name}' 이(가) 없습니다. (멤버: ${names})`, e.line);
        }
        return { addr: base + f.offset, t: f.type, name: exprText(e) };
      }
      case 'index': {
        let a = this.evalR(e.a), i = this.evalR(e.i);
        this.useCheck(a, e.line); this.useCheck(i, e.line);
        if (a.t.k === 'int' && i.t.k === 'ptr') { const tmp = a; a = i; i = tmp; }
        if (a.t.k !== 'ptr') throw rtError('type', `'${exprText(e.a)}' (${typeName(a.t)}) 은(는) 배열/포인터가 아니므로 [ ] 를 쓸 수 없습니다.`, e.line);
        if (i.t.k !== 'int') throw rtError('type', `배열 인덱스는 정수여야 합니다 (${typeName(i.t)}).`, e.line);
        const el = a.t.to;
        if (el.k === 'void') throw rtError('type', `void* 는 인덱싱할 수 없습니다.`, e.line);
        if (a.arrN != null && (i.v < 0 || i.v >= a.arrN)) throw rtError('array-oob', `배열 '${exprText(e.a)}' (크기 ${a.arrN}) 의 범위를 벗어난 인덱스 ${i.v} 에 접근했습니다.`, e.line);
        return { addr: (a.v + i.v * el.size) >>> 0, t: el, name: exprText(e) };
      }
      case 'unary':
        if (e.op === '*') {
          const p = this.evalR(e.e);
          this.useCheck(p, e.line);
          if (p.t.k !== 'ptr') throw rtError('type', `'${exprText(e.e)}' (${typeName(p.t)}) 은(는) 포인터가 아니므로 * 로 역참조할 수 없습니다.`, e.line);
          if (p.t.to.k === 'fn') { const f = this.fnByAddr(p.v); if (!f) throw rtError('invalid-addr', '유효하지 않은 함수 포인터입니다.', e.line); return { fn: f, t: p.t.to, name: exprText(e) }; }
          if (p.t.to.k === 'void') throw rtError('type', `void* 는 역참조할 수 없습니다. 먼저 형변환하세요.`, e.line);
          if (p.v < NULL_GUARD) throw rtError('null-deref', `NULL 포인터 '${exprText(e.e)}' 를 역참조(*)했습니다.`, e.line);
          return { addr: p.v, t: p.t.to, name: exprText(e) };
        }
        break;
      case 'assign': case 'preinc': {
        // (a = b) 또는 (++a) 는 C 에서 왼값이 아니지만, 결과 저장 위치를 돌려주면 ++*p 등도 처리 가능
        const r = this.evalR(e);
        if (r.lv) return r.lv;
        break;
      }
      case 'cast': {
        throw rtError('type', `형변환 결과 '(${typeName(e.type)})${exprText(e.e)}' 에는 대입할 수 없습니다. 변수에 대입하거나 괄호 위치를 확인하세요.`, e.line);
      }
      case 'call': throw rtError('type', `함수 호출 결과 '${exprText(e)}' 에는 대입할 수 없습니다 (왼쪽에 변수가 와야 합니다).`, e.line);
      case 'binary': throw rtError('type', `수식 '${exprText(e)}' 에는 대입할 수 없습니다. '=' 왼쪽에는 변수·배열 원소·멤버가 와야 합니다. (비교 '==' 를 '=' 로 잘못 썼는지도 확인)`, e.line);
      case 'num': throw rtError('type', `상수 '${e.v}' 에는 대입할 수 없습니다. ('==' 를 '=' 로 잘못 썼는지 확인)`, e.line);
    }
    throw rtError('type', `'${exprText(e)}' 은(는) 대입하거나 주소를 취할 수 있는 대상이 아닙니다.`, e.line);
  }

  // 오른값: {t, v}
  evalR(e) {
    switch (e.kind) {
      case 'num': return { t: e.type, v: e.v };
      case 'ident': case 'member': case 'index': return this.loadLv(this.evalL(e), e);
      case 'call': return this.evalCall(e);
      case 'binary': return this.evalBinary(e);
      case 'assign': return this.evalAssign(e);
      case 'unary': return this.evalUnary(e);
      case 'cast': return this.evalCast(e);
      case 'cond': return this.truthy(this.evalR(e.c)) ? this.evalR(e.a) : this.evalR(e.b);
      case 'comma': this.evalR(e.l); return this.evalR(e.r);
      case 'preinc': case 'postinc': return this.evalIncDec(e);
      case 'sizeof': return this.evalSizeof(e);
      case 'str': return { t: ptrTo(TY.char), v: this.strAddr.get(e.id) };
    }
    throw rtError('other', `평가할 수 없는 수식입니다: ${exprText(e)}`, e.line);
  }
  evalUnary(e) {
    if (e.op === '*') { const lv = this.evalL(e); return this.loadLv(lv, e); }
    if (e.op === '&') {
      if (e.e.kind === 'ident' || e.e.kind === 'member' || e.e.kind === 'index' || e.e.kind === 'str' || (e.e.kind === 'unary' && e.e.op === '*')) {
        const lv = this.evalL(e.e);
        if (lv.fn) return { t: ptrTo(lv.t), v: lv.fn.id };
        return { t: ptrTo(lv.t), v: lv.addr };
      }
      throw rtError('type', `'${exprText(e.e)}' 의 주소(&)는 구할 수 없습니다. 변수·배열 원소·멤버만 가능합니다.`, e.line);
    }
    const v = this.evalR(e.e);
    this.useCheck(v, e.line);
    if (e.op === '!') { if (v.t.k === 'struct' || v.t.k === 'void') throw rtError('type', `'!' 은 ${typeName(v.t)} 에 쓸 수 없습니다.`, e.line); return { t: TY.int, v: v.v === 0 ? 1 : 0 }; }
    if (v.t.k !== 'int' && v.t.k !== 'float') throw rtError('type', `단항 '${e.op}' 은 ${typeName(v.t)} 에 쓸 수 없습니다.`, e.line);
    if (e.op === '-') { const t = promote(v.t); return { t, v: t.k === 'float' ? -v.v : wrapInt(-v.v, t) }; }
    if (e.op === '+') { const t = promote(v.t); return { t, v: v.v }; }
    if (e.op === '~') { if (v.t.k !== 'int') throw rtError('type', `'~' 은 정수에만 쓸 수 있습니다.`, e.line); const t = promote(v.t); return { t, v: wrapInt(~v.v, t) }; }
    throw rtError('other', `알 수 없는 단항 연산자 '${e.op}' 입니다.`, e.line);
  }
  evalCast(e) {
    const v = this.evalR(e.e);
    const r = this.convert(v, e.type, e.line);
    return { t: r.t, v: r.v, fromCast: true };
  }
  evalSizeof(e) {
    const t = e.type || this.typeOf(e.e);
    if (t.k === 'arr' && t.incomplete) throw rtError('type', 'sizeof: 크기를 알 수 없는 배열입니다.', e.line);
    if (t.k === 'fn') throw rtError('type', 'sizeof: 함수에는 쓸 수 없습니다.', e.line);
    return { t: TY.uint, v: t.k === 'void' ? 1 : t.size };
  }
  evalIncDec(e) {
    const lv = this.evalL(e.e);
    if (lv.fn) throw rtError('type', '함수에는 ++/-- 를 쓸 수 없습니다.', e.line);
    const cur = this.loadLv(lv, e.e);
    let nv;
    if (cur.t.k === 'ptr') nv = (cur.v + (e.op === '++' ? 1 : -1) * elemSize(cur.t, e.line)) >>> 0;
    else if (cur.t.k === 'int') nv = wrapInt(cur.v + (e.op === '++' ? 1 : -1), cur.t);
    else if (cur.t.k === 'float') nv = cur.v + (e.op === '++' ? 1 : -1);
    else throw rtError('type', `${typeName(cur.t)} 에는 ++/-- 를 쓸 수 없습니다.`, e.line);
    this.store(lv.addr, lv.t, nv, lv.name);
    return { t: cur.t, v: e.kind === 'preinc' ? nv : cur.v, lv };
  }

  loadLv(lv, e) {
    if (lv.fn) return { t: ptrTo(lv.t), v: lv.fn.id };
    const t = lv.t;
    if (t.k === 'arr') return { t: ptrTo(t.of), v: lv.addr, arrN: t.n };
    if (t.k === 'struct') return { t, v: lv.addr };
    if (t.k === 'fn') return { t: ptrTo(t), v: lv.addr };
    return { t, v: this.load(lv.addr, t, lv.name || exprText(e)) };
  }

  typeOf(e) {
    switch (e.kind) {
      case 'num': return e.type;
      case 'str': return arrOf(TY.char, e.bytes.length + 1);
      case 'ident': { const v = this.lookup(e.name); if (v) return v.type; const f = this.funcs.get(e.name); if (f) return ptrTo(f.type); throw rtError('undeclared', `선언되지 않은 식별자 '${e.name}' 입니다.`, e.line); }
      case 'cast': return e.type;
      case 'sizeof': return TY.uint;
      case 'member': {
        const bt = this.typeOf(e.e);
        const st = e.arrow ? (bt.k === 'ptr' ? bt.to : null) : bt;
        if (!st || st.k !== 'struct') throw rtError('type', `'${exprText(e.e)}' 은(는) 구조체(포인터)가 아닙니다.`, e.line);
        const f = st.fields.find(f => f.name === e.name);
        if (!f) throw rtError('type', `${typeName(st)} 에는 멤버 '${e.name}' 이(가) 없습니다.`, e.line);
        return f.type;
      }
      case 'index': { const at = this.typeOf(e.a); if (at.k === 'arr') return at.of; if (at.k === 'ptr') return at.to; throw rtError('type', `'${exprText(e.a)}' 은(는) 배열이 아닙니다.`, e.line); }
      case 'unary': {
        if (e.op === '*') { const pt = this.typeOf(e.e); if (pt.k === 'ptr') return pt.to; if (pt.k === 'arr') return pt.of; throw rtError('type', `'${exprText(e.e)}' 은(는) 포인터가 아닙니다.`, e.line); }
        if (e.op === '&') return ptrTo(this.typeOf(e.e));
        if (e.op === '!') return TY.int;
        return promote(this.typeOf(e.e));
      }
      case 'call': {
        const ft = e.f.kind === 'ident' && this.funcs.get(e.f.name) ? this.funcs.get(e.f.name).type : null;
        if (ft) return ft.ret || TY.int;
        const pt = this.typeOf(e.f); return pt.k === 'ptr' && pt.to.k === 'fn' ? pt.to.ret : TY.int;
      }
      case 'assign': return this.typeOf(e.l);
      case 'preinc': case 'postinc': return this.typeOf(e.e);
      case 'cond': return this.typeOf(e.a);
      case 'comma': return this.typeOf(e.r);
      case 'binary': {
        const op = e.op;
        if (['==', '!=', '<', '>', '<=', '>=', '&&', '||'].includes(op)) return TY.int;
        const a = this.typeOf(e.l), b = this.typeOf(e.r);
        const pa = a.k === 'arr' ? ptrTo(a.of) : a, pb = b.k === 'arr' ? ptrTo(b.of) : b;
        if (pa.k === 'ptr' && pb.k === 'ptr') return TY.int;
        if (pa.k === 'ptr') return pa; if (pb.k === 'ptr') return pb;
        return arithType(pa, pb);
      }
    }
    // 마지막 수단: 실제로 평가
    return this.evalR(e).t;
  }

  evalAssign(e) {
    const lv = this.evalL(e.l);
    if (lv.fn) throw rtError('type', `함수 '${lv.name}' 에는 대입할 수 없습니다.`, e.line);
    if (lv.t.k === 'arr') throw rtError('type', `배열 '${exprText(e.l)}' 전체에는 대입할 수 없습니다. 원소별로 대입하거나 strcpy 등을 사용하세요.`, e.line);
    const what = lv.name || exprText(e.l);
    if (e.op === '=') {
      const rv = this.evalR(e.r);
      if (lv.t.k === 'struct') {
        if (rv.t !== lv.t) throw rtError('type', `'${what}' (${typeName(lv.t)}) 에 ${typeName(rv.t)} 값을 대입할 수 없습니다. 구조체와 구조체 포인터를 혼동했는지 확인하세요.`, e.line);
        this.copyBytes(lv.addr, rv.v, lv.t.size, what);
        return { t: lv.t, v: lv.addr, lv };
      }
      if (rv.t.k === 'struct') throw rtError('type', `'${what}' (${typeName(lv.t)}) 에 구조체 ${typeName(rv.t)} 값을 대입할 수 없습니다. 구조체의 주소(&)나 포인터를 대입해야 하는지 확인하세요.`, e.line);
      if (lv.t.k === 'ptr' && rv.t.k === 'ptr' && !ptrCompatible(lv.t, rv.t) && !rv.fromCast) {
        if (rv.t.to.k === 'struct' && lv.t.to.k === 'ptr' || lv.t.to.k === 'struct' && rv.t.to.k === 'ptr')
          throw rtError('type', `'${what}' (${typeName(lv.t)}) 에 ${typeName(rv.t)} 값을 대입했습니다. 포인터의 단계(*)가 다릅니다 (예: node* 변수에 node** 값, 또는 그 반대).`, e.line);
      }
      if (lv.t.k === 'int' && rv.t.k === 'ptr' && !rv.fromCast && lv.t.size < 4)
        throw rtError('type', `'${what}' (${typeName(lv.t)}) 에 포인터 값을 대입했습니다.`, e.line);
      const cv = this.convert(rv, lv.t, e.line, what);
      this.store(lv.addr, lv.t, cv.v, what);
      return { t: lv.t, v: cv.v, lv };
    }
    const op = e.op.slice(0, -1);
    const cur = this.loadLv(lv, e.l);
    const rv = this.evalR(e.r);
    const res = this.binop(op, cur, rv, e.line);
    const cv = this.convert(res, lv.t, e.line, what);
    this.store(lv.addr, lv.t, cv.v, what);
    return { t: lv.t, v: cv.v, lv };
  }

  evalBinary(e) {
    if (e.op === '&&') { const a = this.evalR(e.l); if (!this.truthy(a)) return { t: TY.int, v: 0 }; const b = this.evalR(e.r); return { t: TY.int, v: this.truthy(b) ? 1 : 0 }; }
    if (e.op === '||') { const a = this.evalR(e.l); if (this.truthy(a)) return { t: TY.int, v: 1 }; const b = this.evalR(e.r); return { t: TY.int, v: this.truthy(b) ? 1 : 0 }; }
    const a = this.evalR(e.l), b = this.evalR(e.r);
    return this.binop(e.op, a, b, e.line, e);
  }

  binop(op, a, b, line, e) {
    this.useCheck(a, line); this.useCheck(b, line);
    const ta = a.t, tb = b.t;
    if (ta.k === 'struct' || tb.k === 'struct') throw rtError('type', `구조체 값에는 연산자 '${op}' 를 쓸 수 없습니다 (${e ? exprText(e) : ''}). 구조체의 멤버나 포인터를 비교·연산하세요.`, line);
    if (ta.k === 'void' || tb.k === 'void') throw rtError('type', `void 값(값을 반환하지 않는 함수의 결과)에 연산자 '${op}' 를 쓸 수 없습니다.`, line);
    // 포인터 연산
    if (ta.k === 'ptr' || tb.k === 'ptr') {
      switch (op) {
        case '+':
          if (ta.k === 'ptr' && tb.k === 'int') return { t: ta, v: (a.v + b.v * elemSize(ta, line)) >>> 0 };
          if (tb.k === 'ptr' && ta.k === 'int') return { t: tb, v: (b.v + a.v * elemSize(tb, line)) >>> 0 };
          throw rtError('type', `포인터끼리 더할 수 없습니다 (${e ? exprText(e) : ''}).`, line);
        case '-':
          if (ta.k === 'ptr' && tb.k === 'int') return { t: ta, v: (a.v - b.v * elemSize(ta, line)) >>> 0 };
          if (ta.k === 'ptr' && tb.k === 'ptr') return { t: TY.int, v: Math.trunc((a.v - b.v) / elemSize(ta, line)) | 0 };
          throw rtError('type', `잘못된 포인터 뺄셈입니다 (${e ? exprText(e) : ''}).`, line);
        case '==': case '!=': case '<': case '>': case '<=': case '>=': {
          if ((ta.k === 'ptr' && tb.k === 'int') || (tb.k === 'ptr' && ta.k === 'int')) {
            const iv = ta.k === 'int' ? a : b;
            if (iv.v !== 0 && !iv.fromCast) throw rtError('type', `포인터와 정수 ${iv.v} 를 비교했습니다 (${e ? exprText(e) : ''}). 포인터는 NULL 이나 다른 포인터와만 비교해야 합니다. (키 값과 노드 포인터를 혼동했는지 확인)`, line);
          }
          if (ta.k === 'float' || tb.k === 'float') throw rtError('type', `포인터와 실수를 비교할 수 없습니다.`, line);
          const x = a.v >>> 0, y = b.v >>> 0;
          let r;
          switch (op) { case '==': r = x === y; break; case '!=': r = x !== y; break; case '<': r = x < y; break; case '>': r = x > y; break; case '<=': r = x <= y; break; default: r = x >= y; }
          return { t: TY.int, v: r ? 1 : 0 };
        }
        default:
          throw rtError('type', `포인터에는 연산자 '${op}' 를 쓸 수 없습니다 (${e ? exprText(e) : ''}). 포인터가 가리키는 값(->key 등)을 연산하려던 것인지 확인하세요.`, line);
      }
    }
    // 산술
    const t = arithType(ta, tb);
    let x = a.v, y = b.v;
    if (t.k === 'float') {
      switch (op) {
        case '+': return { t, v: x + y }; case '-': return { t, v: x - y }; case '*': return { t, v: x * y };
        case '/': return { t, v: x / y };
        case '%': throw rtError('type', `'%' 연산은 정수에만 쓸 수 있습니다. (fmod 사용)`, line);
        case '==': return { t: TY.int, v: x === y ? 1 : 0 }; case '!=': return { t: TY.int, v: x !== y ? 1 : 0 };
        case '<': return { t: TY.int, v: x < y ? 1 : 0 }; case '>': return { t: TY.int, v: x > y ? 1 : 0 };
        case '<=': return { t: TY.int, v: x <= y ? 1 : 0 }; case '>=': return { t: TY.int, v: x >= y ? 1 : 0 };
        default: throw rtError('type', `실수에는 연산자 '${op}' 를 쓸 수 없습니다.`, line);
      }
    }
    switch (op) {
      case '+': return { t, v: wrapInt(x + y, t) };
      case '-': return { t, v: wrapInt(x - y, t) };
      case '*': return { t, v: t.size <= 4 ? wrapInt(t.signed ? Math.imul(x | 0, y | 0) : (Math.imul(x, y) >>> 0), t) : wrapInt(x * y, t) };
      case '/': if (y === 0) throw rtError('div-zero', `0으로 나눴습니다 (${e ? exprText(e) : ''}).`, line); return { t, v: wrapInt(Math.trunc(x / y), t) };
      case '%': if (y === 0) throw rtError('div-zero', `0으로 나눈 나머지(%)를 구했습니다 (${e ? exprText(e) : ''}).`, line); return { t, v: wrapInt(x % y, t) };
      case '<<': return { t, v: wrapInt(t.size <= 4 ? (x << (y & 31)) : x * Math.pow(2, y), t) };
      case '>>': return { t, v: wrapInt(t.signed ? (x >> (y & 31)) : (x >>> (y & 31)), t) };
      case '&': return { t, v: wrapInt(t.size <= 4 ? (x & y) : Number(BigInt(x) & BigInt(y)), t) };
      case '|': return { t, v: wrapInt(t.size <= 4 ? (x | y) : Number(BigInt(x) | BigInt(y)), t) };
      case '^': return { t, v: wrapInt(t.size <= 4 ? (x ^ y) : Number(BigInt(x) ^ BigInt(y)), t) };
      case '==': return { t: TY.int, v: x === y ? 1 : 0 }; case '!=': return { t: TY.int, v: x !== y ? 1 : 0 };
      case '<': return { t: TY.int, v: x < y ? 1 : 0 }; case '>': return { t: TY.int, v: x > y ? 1 : 0 };
      case '<=': return { t: TY.int, v: x <= y ? 1 : 0 }; case '>=': return { t: TY.int, v: x >= y ? 1 : 0 };
    }
    throw rtError('other', `알 수 없는 연산자 '${op}' 입니다.`, line);
  }

  evalCall(e) {
    this.line = e.line;
    const fn = this.resolveCallee(e);
    const args = this.evalArgs(e, fn);
    if (fn.kind === 'builtin') { this.tick(); return fn.impl(args, e, fn); }
    // 사용자 함수 호출 (callUser 와 같은 내용을 인라인: JS 스택 프레임 수를 줄여 깊은 재귀를 수용)
    if (this.depth >= this.opts.maxDepth) throw rtError('stack-overflow', `함수 호출 깊이가 ${this.opts.maxDepth}을 넘었습니다 (스택 오버플로). 재귀 함수 '${fn.name}' 의 종료 조건을 확인하세요 (예: 외부노드에서 멈추는지).`, e.line);
    const savedScopes = this.scopes, savedSp = this.sp;
    this.scopes = [this.globals, new Map()];
    this.depth++;
    let r;
    try {
      this.bindParams(fn, args, e.line);
      const stmts = fn.node.body.stmts;
      for (let i = 0; i < stmts.length; i++) { r = this.exec(stmts[i]); if (r) break; }
    } catch (err) {
      this.scopes = savedScopes; this.sp = savedSp; this.depth--;
      throw err;
    }
    this.scopes = savedScopes; this.sp = savedSp; this.depth--; this.line = e.line;
    return this.finishCall(fn, r, e.line);
  }
  resolveCallee(e) {
    if (e.f.kind === 'ident') {
      const v = this.lookup(e.f.name);
      if (!v) {
        const fn = this.funcs.get(e.f.name);
        if (!fn) throw rtError('undeclared', `선언되지 않은 함수 '${e.f.name}' 를 호출했습니다.`, e.line);
        if (fn.kind === 'user' && !fn.node) throw rtError('undeclared', `함수 '${fn.name}' 가 선언만 되고 정의되지 않았습니다.`, e.line);
        return fn;
      }
      if (v.type.k === 'ptr' && v.type.to.k === 'fn') {
        const fn = this.fnByAddr(this.load(v.addr, v.type, e.f.name));
        if (!fn) throw rtError('invalid-addr', `'${e.f.name}' 은(는) 유효한 함수를 가리키지 않습니다.`, e.line);
        return fn;
      }
      throw rtError('type', `'${e.f.name}' 은(는) 함수가 아니라 변수(${typeName(v.type)})입니다. 같은 이름의 변수와 함수가 있는지 확인하세요.`, e.line);
    }
    const fv = this.evalR(e.f);
    if (fv.t.k !== 'ptr' || fv.t.to.k !== 'fn') throw rtError('type', `'${exprText(e.f)}' 은(는) 함수가 아닙니다 (${typeName(fv.t)}).`, e.line);
    const fn = this.fnByAddr(fv.v);
    if (!fn) throw rtError('invalid-addr', `유효하지 않은 함수 포인터를 호출했습니다.`, e.line);
    if (fn.kind === 'user' && !fn.node) throw rtError('undeclared', `함수 '${fn.name}' 가 선언만 되고 정의되지 않았습니다.`, e.line);
    return fn;
  }
  evalArgs(e, fn) {
    const args = new Array(e.args.length);
    for (let i = 0; i < e.args.length; i++) {
      const a = this.evalR(e.args[i]);
      if (a.t.k === 'void') throw rtError('type', `함수 '${fn.name}' 의 ${i + 1}번째 인자가 void 값입니다 (값을 반환하지 않는 함수의 결과를 넘겼습니다).`, e.line);
      args[i] = a;
    }
    return args;
  }
  // 사용자 함수 호출: 스택 프레임을 작게 유지하기 위해 인자 바인딩과 반환 처리는 별도 함수로 분리
  callUser(fn, args, line, e) {
    if (this.depth >= this.opts.maxDepth) throw rtError('stack-overflow', `함수 호출 깊이가 ${this.opts.maxDepth}을 넘었습니다 (스택 오버플로). 재귀 함수 '${fn.name}' 의 종료 조건을 확인하세요 (예: 외부노드에서 멈추는지).`, line);
    const savedScopes = this.scopes, savedSp = this.sp, savedLine = this.line;
    this.scopes = [this.globals, new Map()];
    this.depth++;
    this.tick();
    let r;
    try {
      this.bindParams(fn, args, line);
      r = this.execBlockNoScope(fn.node.body);
    } catch (err) {
      this.scopes = savedScopes; this.sp = savedSp; this.depth--;
      throw err;
    }
    this.scopes = savedScopes; this.sp = savedSp; this.depth--; this.line = savedLine;
    return this.finishCall(fn, r, line);
  }
  bindParams(fn, args, line) {
    const ft = fn.node.type;
    if (!ft.oldStyle && args.length !== ft.params.length)
      throw rtError('arg-count', `함수 '${fn.name}' 은(는) 인자 ${ft.params.length}개를 받지만 ${args.length}개를 전달했습니다. (${line}번째 줄, 함수 정의는 ${fn.node.line}번째 줄)`, line);
    const scope = this.scopes[1];
    for (let i = 0; i < ft.params.length; i++) {
      const p = ft.params[i];
      const pt = p.type;
      const addr = this.allocStack(pt.size, pt.align);
      const a = args[i];
      if (a === undefined) throw rtError('arg-count', `함수 '${fn.name}' 의 ${i + 1}번째 인자가 없습니다.`, line);
      if (pt.k === 'struct') {
        if (a.t !== pt) throw rtError('type', `함수 '${fn.name}' 의 ${i + 1}번째 인자 '${p.name}' 는 ${typeName(pt)} 이어야 하는데 ${typeName(a.t)} 을 전달했습니다.`, line);
        this.copyBytes(addr, a.v, pt.size, p.name);
      } else {
        if (pt.k === 'ptr' && a.t.k === 'ptr' && !ptrCompatible(pt, a.t) && !a.fromCast && (pt.to.k === 'struct' || a.t.to.k === 'struct') && (pt.to.k !== 'void' && a.t.to.k !== 'void'))
          throw rtError('type', `함수 '${fn.name}' 의 ${i + 1}번째 인자 '${p.name}' 는 ${typeName(pt)} 이어야 하는데 ${typeName(a.t)} 을 전달했습니다. 포인터 단계(*)나 타입을 확인하세요.`, line);
        if (pt.k === 'ptr' && a.t.k === 'int' && a.v !== 0 && !a.fromCast)
          throw rtError('type', `함수 '${fn.name}' 의 ${i + 1}번째 인자 '${p.name}' 는 포인터(${typeName(pt)})인데 정수 값 ${a.v} 를 전달했습니다. 키 값과 노드 포인터를 혼동했는지 확인하세요.`, line);
        if (pt.k === 'int' && a.t.k === 'ptr' && !a.fromCast)
          throw rtError('type', `함수 '${fn.name}' 의 ${i + 1}번째 인자 '${p.name}' 는 정수(${typeName(pt)})인데 포인터 값(${typeName(a.t)})을 전달했습니다. 노드 포인터와 키 값을 혼동했는지 확인하세요.`, line);
        const cv = this.convert(a, pt, line, p.name);
        this.store(addr, pt, cv.v, p.name);
      }
      scope.set(p.name, { addr, type: pt });
    }
  }
  finishCall(fn, r, line) {
    const ft = fn.node.type;
    let ret;
    if (r && r.ret) {
      ret = r.ret;
      if (ft.ret.k === 'void') {
        if (ret.t.k !== 'void' && fn.name !== 'main') throw rtError('type', `void 함수 '${fn.name}' 가 값을 반환했습니다 ('return 값;'). 반환형을 바꾸거나 'return;' 으로 고치세요.`, r.line || line);
        return { t: TY.void, v: 0 };
      }
      if (ret.t.k === 'void') throw rtError('type', `함수 '${fn.name}' (반환형 ${typeName(ft.ret)}) 의 return 문에 값이 없습니다.`, r.line || line);
      if (ft.ret.k === 'struct') {
        if (ret.t !== ft.ret) throw rtError('type', `함수 '${fn.name}' 는 ${typeName(ft.ret)} 을 반환해야 하는데 ${typeName(ret.t)} 을 반환했습니다.`, r.line || line);
        // 반환 구조체를 호출자 스택의 임시 공간으로 복사 (피호출자 프레임의 바이트는 아직 남아 있음)
        const tmp = this.allocStack(ft.ret.size, ft.ret.align);
        this.u8.copyWithin(tmp, ret.v, ret.v + ft.ret.size);
        this.shadow.copyWithin(tmp, ret.v, ret.v + ft.ret.size);
        return { t: ft.ret, v: tmp };
      }
      if (ft.ret.k === 'ptr' && ret.t.k === 'int' && ret.v !== 0 && !ret.fromCast) throw rtError('type', `함수 '${fn.name}' 는 포인터(${typeName(ft.ret)})를 반환해야 하는데 정수 ${ret.v} 를 반환했습니다 (예: 노드 대신 키를 반환).`, r.line || line);
      if (ft.ret.k === 'int' && ret.t.k === 'ptr' && !ret.fromCast) throw rtError('type', `함수 '${fn.name}' 는 정수(${typeName(ft.ret)})를 반환해야 하는데 포인터(${typeName(ret.t)})를 반환했습니다 (예: 키 대신 노드를 반환).`, r.line || line);
      if (ft.ret.k === 'ptr' && ret.t.k === 'ptr' && !ptrCompatible(ft.ret, ret.t) && !ret.fromCast && (ft.ret.to.k === 'struct' || ret.t.to.k === 'struct') && ft.ret.to.k !== 'void' && ret.t.to.k !== 'void')
        throw rtError('type', `함수 '${fn.name}' 는 ${typeName(ft.ret)} 을 반환해야 하는데 ${typeName(ret.t)} 을 반환했습니다.`, r.line || line);
      return this.convert(ret, ft.ret, r.line || line);
    }
    ret = { t: ft.ret.k === 'void' ? TY.void : ft.ret, v: 0 };
    if (ft.ret.k !== 'void' && fn.name !== 'main') {
      ret.noReturn = fn.name;
      if (ft.ret.k === 'struct') throw rtError('no-return', `함수 '${fn.name}' (반환형 ${typeName(ft.ret)}) 이 return 문 없이 끝났습니다.`, line);
    }
    return ret;
  }

  /* ---------- 문장 실행 ---------- */
  // 반환: undefined | 'break' | 'continue' | {ret:{t,v}, line}
  // (각 문장 종류를 작은 함수로 나눠 JS 호출 스택 프레임을 작게 유지한다: 깊은 재귀 호출 수용)
  execBlockNoScope(block) {
    const stmts = block.stmts;
    for (let i = 0; i < stmts.length; i++) {
      const r = this.exec(stmts[i]);
      if (r) return r;
    }
    return undefined;
  }
  exec(s) {
    this.line = s.line;
    this.tick();
    switch (s.kind) {
      case 'expr': this.evalR(s.expr); return undefined;
      case 'return': return { ret: s.expr ? this.evalR(s.expr) : { t: TY.void, v: 0 }, line: s.line };
      case 'if': return this.truthy(this.evalR(s.cond)) ? this.exec(s.then) : (s.els ? this.exec(s.els) : undefined);
      case 'block': return this.execBlock(s);
      case 'decl': return this.execDecl(s);
      case 'while': return this.execWhile(s);
      case 'for': return this.execFor(s);
      case 'dowhile': return this.execDoWhile(s);
      case 'switch': return this.execSwitch(s);
      case 'case': case 'default': return this.exec(s.stmt);
      case 'break': return 'break';
      case 'continue': return 'continue';
      case 'empty': return undefined;
    }
    throw rtError('other', `실행할 수 없는 문장입니다: ${s.kind}`, s.line);
  }
  execReturn(s) {
    if (!s.expr) return { ret: { t: TY.void, v: 0 }, line: s.line };
    return { ret: this.evalR(s.expr), line: s.line };
  }
  execIf(s) {
    if (this.truthy(this.evalR(s.cond))) return this.exec(s.then);
    if (s.els) return this.exec(s.els);
    return undefined;
  }
  execDecl(s) {
    const ds = s.decls;
    for (let i = 0; i < ds.length; i++) if (ds[i].kind === 'var') this.declareLocal(ds[i]);
    return undefined;
  }
  execBlock(s) {
    const sp0 = this.sp;
    this.scopes.push(new Map());
    let r;
    try { r = this.execBlockNoScope(s); }
    finally { this.scopes.pop(); this.sp = sp0; }
    return r;
  }
  execWhile(s) {
    for (;;) {
      this.line = s.line; this.tick();
      if (!this.truthy(this.evalR(s.cond))) return undefined;
      const r = this.exec(s.body);
      if (r === 'break') return undefined;
      if (r && r.ret) return r;
    }
  }
  execDoWhile(s) {
    for (;;) {
      const r = this.exec(s.body);
      if (r === 'break') return undefined;
      if (r && r.ret) return r;
      this.line = s.line; this.tick();
      if (!this.truthy(this.evalR(s.cond))) return undefined;
    }
  }
  execFor(s) {
    const sp0 = this.sp;
    this.scopes.push(new Map());
    try {
      if (s.init) this.exec(s.init);
      for (;;) {
        this.line = s.line; this.tick();
        if (s.cond && !this.truthy(this.evalR(s.cond))) return undefined;
        const r = this.exec(s.body);
        if (r === 'break') return undefined;
        if (r && r.ret) return r;
        if (s.step) { this.line = s.line; this.evalR(s.step); }
      }
    } finally { this.scopes.pop(); this.sp = sp0; }
  }
  execSwitch(s) {
    const v = this.evalR(s.expr);
    if (v.t.k !== 'int') throw rtError('type', `switch 의 조건은 정수(문자)여야 합니다 (${typeName(v.t)}).`, s.line);
    const body = s.body;
    const stmts = body.kind === 'block' ? body.stmts : [body];
    let start = -1, def = -1;
    for (let i = 0; i < stmts.length; i++) {
      let st = stmts[i];
      while (st && (st.kind === 'case' || st.kind === 'default')) {
        if (st.kind === 'case' && st.value === v.v && start < 0) start = i;
        if (st.kind === 'default' && def < 0) def = i;
        st = st.stmt;
      }
    }
    if (start < 0) start = def;
    if (start < 0) return undefined;
    const sp0 = this.sp;
    this.scopes.push(new Map());
    try {
      for (let i = start; i < stmts.length; i++) {
        const r = this.exec(stmts[i]);
        if (r === 'break') return undefined;
        if (r === 'continue') return r;
        if (r && r.ret) return r;
      }
    } finally { this.scopes.pop(); this.sp = sp0; }
    return undefined;
  }
}

/* ---------- 타입 보조 ---------- */
function wrapInt(v, t) {
  if (t.size === 4) return t.signed ? (v | 0) : (v >>> 0);
  if (t.size === 1) return t.isBool ? (v ? 1 : 0) : (t.signed ? ((v << 24) >> 24) : (v & 0xff));
  if (t.size === 2) return t.signed ? ((v << 16) >> 16) : (v & 0xffff);
  // 8바이트: 정밀도 한계 내에서 그대로
  return Math.trunc(v);
}
function promote(t) {
  if (t.k === 'int' && t.size < 4) return TY.int;
  if (t.k === 'float' && t.size === 4) return TY.float;
  return t;
}
function arithType(a, b) {
  if (a.k === 'float' || b.k === 'float') {
    if ((a.k === 'float' && a.size === 8) || (b.k === 'float' && b.size === 8)) return TY.double;
    return TY.float;
  }
  a = promote(a); b = promote(b);
  if (a.size === 8 || b.size === 8) return (a.size === 8 && !a.signed) || (b.size === 8 && !b.signed) ? TY.ullong : TY.llong;
  if (!a.signed || !b.signed) return TY.uint;
  return TY.int;
}
function elemSize(pt, line) {
  const to = pt.to;
  if (to.k === 'void') return 1;
  if (to.k === 'fn') throw rtError('type', '함수 포인터에는 산술 연산을 할 수 없습니다.', line);
  if (to.k === 'struct' && !to.complete) throw rtError('type', `${typeName(to)} 이 정의되지 않아 크기를 알 수 없습니다.`, line);
  return to.size;
}
function ptrCompatible(a, b) {
  if (a.to.k === 'void' || b.to.k === 'void') return true;
  return sameType(a.to, b.to);
}
function editDistance(a, b) {
  const m = a.length, n = b.length;
  if (Math.abs(m - n) > 2) return 99;
  const dp = Array.from({ length: m + 1 }, (_, i) => [i].concat(new Array(n).fill(0)));
  for (let j = 0; j <= n; j++) dp[0][j] = j;
  for (let i = 1; i <= m; i++) for (let j = 1; j <= n; j++) dp[i][j] = Math.min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
  return dp[m][n];
}

/* ============================================================
 *  표준 라이브러리
 * ============================================================ */
function installStdlib(rt) {
  const I = TY.int, U = TY.uint, D = TY.double, C = TY.char, V = TY.void;
  const CP = ptrTo(TY.char), VP = ptrTo(TY.void);
  const num = (t, v) => ({ t, v });
  const int = (v) => ({ t: I, v: v | 0 });
  const ptr = (t, v) => ({ t, v: v >>> 0 });
  const def = (name, impl) => rt.registerFn(name, { kind: 'builtin', impl, type: fnType(I, [], true, true) });
  const argN = (args, n, name, line) => { if (args.length < n) throw rtError('arg-count', `${name}() 에 인자가 부족합니다 (${n}개 필요, ${args.length}개 전달).`, line); };
  const asInt = (a, name, i, line) => {
    rt.useCheck(a, line);
    if (a.t.k === 'int') return a.v;
    if (a.t.k === 'float') return Math.trunc(a.v);
    if (a.t.k === 'ptr') throw rtError('type', `${name}() 의 ${i}번째 인자는 정수여야 하는데 포인터(${typeName(a.t)})를 전달했습니다.`, line);
    throw rtError('type', `${name}() 의 ${i}번째 인자는 정수여야 합니다 (${typeName(a.t)}).`, line);
  };
  const asPtr = (a, name, i, line) => {
    rt.useCheck(a, line);
    if (a.t.k === 'ptr') return a.v >>> 0;
    if (a.t.k === 'int' && (a.v === 0 || a.fromCast)) return a.v >>> 0;
    if (a.t.k === 'int') throw rtError('type', `${name}() 의 ${i}번째 인자는 포인터여야 하는데 정수 ${a.v} 를 전달했습니다. (& 를 빠뜨렸거나 변수를 혼동했는지 확인)`, line);
    throw rtError('type', `${name}() 의 ${i}번째 인자는 포인터여야 합니다 (${typeName(a.t)}).`, line);
  };
  const asNum = (a, name, i, line) => {
    rt.useCheck(a, line);
    if (a.t.k === 'int' || a.t.k === 'float') return a.v;
    throw rtError('type', `${name}() 의 ${i}번째 인자는 숫자여야 합니다 (${typeName(a.t)}).`, line);
  };
  const streamIsErr = (a, name, line) => {
    const v = a.t.k === 'ptr' || a.t.k === 'int' ? a.v >>> 0 : -1;
    if (v === FILE_STDERR) return true;
    if (v === FILE_STDOUT) return false;
    if (v === FILE_STDIN) throw rtError('type', `${name}(): stdin 에는 출력할 수 없습니다.`, line);
    throw rtError('type', `${name}(): 첫 번째 인자는 stdout 또는 stderr 이어야 합니다 (파일 입출력은 지원하지 않습니다).`, line);
  };

  /* --- 출력 --- */
  const doPrintf = (fmtAddr, args, ai, name, line) => {
    const fmt = rt.readCString(fmtAddr, `${name} 형식 문자열`);
    const out = [];
    const pushStr = (s) => { for (const b of new TextEncoder().encode(s)) out.push(b); };
    let i = 0;
    while (i < fmt.length) {
      const c = fmt[i];
      if (c !== 37) { out.push(c); i++; continue; }
      i++;
      if (i >= fmt.length) break;
      if (fmt[i] === 37) { out.push(37); i++; continue; }
      let flags = '', width = null, prec = null, len = '';
      while (i < fmt.length && '-+ #0'.includes(String.fromCharCode(fmt[i]))) { flags += String.fromCharCode(fmt[i]); i++; }
      if (fmt[i] === 42) { argN(args, ai + 1, name, line); width = asInt(args[ai++], name, ai, line); i++; if (width < 0) { flags += '-'; width = -width; } }
      else { let w = ''; while (i < fmt.length && fmt[i] >= 48 && fmt[i] <= 57) { w += String.fromCharCode(fmt[i]); i++; } if (w) width = parseInt(w, 10); }
      if (fmt[i] === 46) {
        i++;
        if (fmt[i] === 42) { argN(args, ai + 1, name, line); prec = asInt(args[ai++], name, ai, line); i++; if (prec < 0) prec = null; }
        else { let p = ''; while (i < fmt.length && fmt[i] >= 48 && fmt[i] <= 57) { p += String.fromCharCode(fmt[i]); i++; } prec = p ? parseInt(p, 10) : 0; }
      }
      while (i < fmt.length && 'hlLqjzt'.includes(String.fromCharCode(fmt[i]))) { len += String.fromCharCode(fmt[i]); i++; }
      if (i >= fmt.length) throw rtError('type', `${name}(): 형식 문자열이 '%' 뒤에서 끝났습니다.`, line);
      const conv = String.fromCharCode(fmt[i]); i++;
      let s;
      const pad = (str, isNum) => {
        if (width != null && str.length < width) {
          if (flags.includes('-')) str = str + ' '.repeat(width - str.length);
          else if (flags.includes('0') && isNum && prec == null) {
            const sign = (str[0] === '-' || str[0] === '+' || str[0] === ' ') ? str[0] : '';
            const body = sign ? str.slice(1) : str;
            str = sign + '0'.repeat(width - str.length) + body;
          } else str = ' '.repeat(width - str.length) + str;
        }
        return str;
      };
      switch (conv) {
        case 'd': case 'i': case 'u': case 'x': case 'X': case 'o': case 'c': case 'p': case 'f': case 'F': case 'e': case 'E': case 'g': case 'G': case 's': case 'a':
          if (ai >= args.length) throw rtError('arg-count', `${name}(): 형식 문자열의 '%${conv}' 에 대응하는 인자가 없습니다. 형식 지정자 개수와 인자 개수를 확인하세요.`, line);
      }
      switch (conv) {
        case 'd': case 'i': {
          const a = args[ai++];
          rt.useCheck(a, line);
          if (a.t.k === 'ptr') throw rtError('type', `${name}(): '%${conv}' 에 포인터(${typeName(a.t)})를 전달했습니다. 노드가 아니라 노드의 키(->key)를 출력해야 하는지 확인하세요.`, line);
          if (a.t.k === 'struct') throw rtError('type', `${name}(): '%${conv}' 에 구조체를 전달했습니다. 구조체의 멤버를 출력하세요.`, line);
          let v = a.t.k === 'float' ? Math.trunc(a.v) : a.v;
          if (len === 'll' || len === 'q' || len === 'j') v = Math.trunc(v); else if (len === 'h') v = (v << 16) >> 16; else if (len === 'hh') v = (v << 24) >> 24; else v = v | 0;
          s = String(Math.abs(v));
          if (prec != null) s = s.padStart(prec, '0');
          if (prec === 0 && v === 0) s = '';
          if (v < 0) s = '-' + s; else if (flags.includes('+')) s = '+' + s; else if (flags.includes(' ')) s = ' ' + s;
          s = pad(s, true); break;
        }
        case 'u': case 'x': case 'X': case 'o': {
          const a = args[ai++];
          if (a.t.k === 'struct') throw rtError('type', `${name}(): '%${conv}' 에 구조체를 전달했습니다.`, line);
          let v = a.t.k === 'float' ? Math.trunc(a.v) : a.v;
          if (len === 'll' || len === 'q' || len === 'j') { if (v < 0) v = Number(BigInt.asUintN(64, BigInt(Math.trunc(v)))); } else v = v >>> 0;
          if (len === 'h') v = v & 0xffff; if (len === 'hh') v = v & 0xff;
          s = v.toString(conv === 'u' ? 10 : conv === 'o' ? 8 : 16);
          if (conv === 'X') s = s.toUpperCase();
          if (prec != null) s = s.padStart(prec, '0');
          if (flags.includes('#') && v !== 0) s = (conv === 'o' ? '0' : conv === 'x' ? '0x' : conv === 'X' ? '0X' : '') + s;
          s = pad(s, true); break;
        }
        case 'c': {
          const a = args[ai++];
          if (a.t.k === 'ptr') throw rtError('type', `${name}(): '%c' 에 포인터(문자열?)를 전달했습니다. 문자열은 '%s' 를 사용하세요.`, line);
          const v = asInt(a, name, ai, line) & 0xff;
          s = pad(String.fromCharCode(v), false);
          if (width == null) { out.push(v); s = null; }
          break;
        }
        case 's': {
          const a = args[ai++];
          if (a.t.k === 'int' && !a.fromCast) throw rtError('type', `${name}(): '%s' 에 정수 ${a.v} 를 전달했습니다. 문자열(char*)이 필요합니다. 정수를 출력하려면 '%d' 를 사용하세요.`, line);
          if (a.t.k === 'struct') throw rtError('type', `${name}(): '%s' 에 구조체를 전달했습니다.`, line);
          const addr = asPtr(a, name, ai, line);
          if (addr === 0) { s = '(null)'; } else {
            let bytes = rt.readCString(addr, `${name} '%s' 인자`);
            if (prec != null) bytes = bytes.slice(0, prec);
            const str = new TextDecoder().decode(new Uint8Array(bytes));
            if (width != null && str.length < width) {
              const padLen = width - str.length;
              const padBytes = new Array(padLen).fill(32);
              if (flags.includes('-')) { for (const b of bytes) out.push(b); for (const b of padBytes) out.push(b); }
              else { for (const b of padBytes) out.push(b); for (const b of bytes) out.push(b); }
            } else for (const b of bytes) out.push(b);
            s = null;
          }
          if (s === '(null)') s = pad(s, false);
          break;
        }
        case 'f': case 'F': case 'e': case 'E': case 'g': case 'G': case 'a': {
          const a = args[ai++];
          if (a.t.k === 'ptr') throw rtError('type', `${name}(): '%${conv}' 에 포인터를 전달했습니다.`, line);
          if (a.t.k === 'struct') throw rtError('type', `${name}(): '%${conv}' 에 구조체를 전달했습니다.`, line);
          if (a.t.k === 'int' && !a.fromCast) throw rtError('type', `${name}(): '%${conv}' 에 정수(${typeName(a.t)})를 전달했습니다. 정수는 '%d' 로 출력해야 합니다.`, line);
          const v = a.v;
          const p = prec == null ? 6 : prec;
          if (!isFinite(v)) s = isNaN(v) ? 'nan' : (v < 0 ? '-inf' : 'inf');
          else if (conv === 'f' || conv === 'F') s = v.toFixed(Math.min(p, 100));
          else if (conv === 'e' || conv === 'E') { s = v.toExponential(Math.min(p, 100)); s = s.replace(/e([+-])(\d)$/, 'e$10$2'); if (conv === 'E') s = s.toUpperCase(); }
          else {
            const P = p === 0 ? 1 : p;
            if (v === 0) s = '0';
            else {
              const exp = Math.floor(Math.log10(Math.abs(v)));
              if (exp < -4 || exp >= P) { s = v.toExponential(P - 1); if (!flags.includes('#')) s = s.replace(/\.?0+e/, 'e'); s = s.replace(/e([+-])(\d)$/, 'e$10$2'); }
              else { s = v.toFixed(Math.max(0, P - 1 - exp)); if (!flags.includes('#') && s.includes('.')) s = s.replace(/\.?0+$/, ''); }
            }
            if (conv === 'G') s = s.toUpperCase();
          }
          if (v >= 0 || (v === 0 && !Object.is(v, -0))) { if (flags.includes('+')) s = '+' + s; else if (flags.includes(' ')) s = ' ' + s; }
          s = pad(s, true); break;
        }
        case 'p': { const a = args[ai++]; s = pad('0x' + (a.v >>> 0).toString(16).padStart(8, '0'), false); break; }
        case 'n': ai++; s = ''; break;
        default: throw rtError('type', `${name}(): 알 수 없는 형식 지정자 '%${conv}' 입니다.`, line);
      }
      if (s != null) pushStr(s);
    }
    if (ai < args.length) {
      // 초과 인자는 C 에서도 허용되지만, 형식 지정자 누락 가능성을 알려주기 위해 경고를 남긴다
      rt.warn = rt.warn || [];
      rt.warn.push(`${line}번째 줄 ${name}(): 형식 문자열보다 인자가 ${args.length - ai}개 많습니다.`);
    }
    return out;
  };

  def('printf', (args, e) => { argN(args, 1, 'printf', e.line); const out = doPrintf(asPtr(args[0], 'printf', 1, e.line), args, 1, 'printf', e.line); rt.writeOut(out, false); return int(out.length); });
  def('fprintf', (args, e) => { argN(args, 2, 'fprintf', e.line); const isErr = streamIsErr(args[0], 'fprintf', e.line); const out = doPrintf(asPtr(args[1], 'fprintf', 2, e.line), args, 2, 'fprintf', e.line); rt.writeOut(out, isErr); return int(out.length); });
  def('sprintf', (args, e) => { argN(args, 2, 'sprintf', e.line); const out = doPrintf(asPtr(args[1], 'sprintf', 2, e.line), args, 2, 'sprintf', e.line); rt.writeCString(asPtr(args[0], 'sprintf', 1, e.line), out, 'sprintf 대상 버퍼'); return int(out.length); });
  def('snprintf', (args, e) => { argN(args, 3, 'snprintf', e.line); const n = asInt(args[1], 'snprintf', 2, e.line); const out = doPrintf(asPtr(args[2], 'snprintf', 3, e.line), args, 3, 'snprintf', e.line); if (n > 0) rt.writeCString(asPtr(args[0], 'snprintf', 1, e.line), out.slice(0, n - 1), 'snprintf 대상 버퍼'); return int(out.length); });
  def('puts', (args, e) => { argN(args, 1, 'puts', e.line); const a = args[0]; if (a.t.k === 'int' && !a.fromCast) throw rtError('type', `puts() 에는 문자열(char*)을 전달해야 합니다. 정수를 출력하려면 printf("%d") 를 사용하세요.`, e.line); const addr = asPtr(a, 'puts', 1, e.line); if (addr === 0) throw rtError('null-deref', 'puts(NULL) 을 호출했습니다.', e.line); const bytes = rt.readCString(addr, 'puts 인자'); bytes.push(10); rt.writeOut(bytes, false); return int(bytes.length); });
  def('fputs', (args, e) => { argN(args, 2, 'fputs', e.line); const isErr = streamIsErr(args[1], 'fputs', e.line); const bytes = rt.readCString(asPtr(args[0], 'fputs', 1, e.line), 'fputs 인자'); rt.writeOut(bytes, isErr); return int(bytes.length); });
  const putcharImpl = (args, e) => { argN(args, 1, 'putchar', e.line); const a = args[0]; if (a.t.k === 'ptr') throw rtError('type', `putchar() 에 포인터(문자열?)를 전달했습니다. 문자 하나(int/char)가 필요합니다.`, e.line); const v = asInt(a, 'putchar', 1, e.line) & 0xff; rt.writeOut([v], false); return int(v); };
  def('putchar', putcharImpl);
  def('_putch', putcharImpl);
  def('putch', putcharImpl);
  def('fputc', (args, e) => { argN(args, 2, 'fputc', e.line); const isErr = streamIsErr(args[1], 'fputc', e.line); const v = asInt(args[0], 'fputc', 1, e.line) & 0xff; rt.writeOut([v], isErr); return int(v); });
  def('putc', (args, e) => { argN(args, 2, 'putc', e.line); const isErr = streamIsErr(args[1], 'putc', e.line); const v = asInt(args[0], 'putc', 1, e.line) & 0xff; rt.writeOut([v], isErr); return int(v); });
  def('fflush', () => int(0));
  def('setvbuf', () => int(0));
  def('setbuf', () => num(V, 0));
  def('perror', (args, e) => { if (args.length) { const b = rt.readCString(asPtr(args[0], 'perror', 1, e.line), 'perror'); rt.writeOut(b.concat([58, 32]), true); } rt.writeStr('error\n', true); return num(V, 0); });

  /* --- 입력 --- */
  const isWs = (b) => b === 32 || b === 9 || b === 10 || b === 13 || b === 11 || b === 12;
  const makeSource = (addr, name, line) => {
    if (addr == null) return { isStdin: true, peek: () => rt.inPeek(), next: () => rt.inNext() };
    let pos = addr;
    return {
      peek: () => { rt.checkAccess(pos, 1, false, name); const b = rt.u8[pos]; return b === 0 ? -1 : b; },
      next: () => { rt.checkAccess(pos, 1, false, name); const b = rt.u8[pos]; if (b === 0) return -1; pos++; return b; },
    };
  };
  const doScanf = (src, fmtAddr, args, ai, name, line, secure) => {
    const fmt = rt.readCString(fmtAddr, `${name} 형식 문자열`);
    let assigned = 0, consumedAny = false;
    let i = 0;
    const skipWs = () => { while (src.peek() >= 0 && isWs(src.peek())) { src.next(); } };
    const eofRet = () => { if (src.isStdin) rt.eofReads++; return assigned === 0 ? -1 : assigned; };
    while (i < fmt.length) {
      const c = fmt[i];
      if (isWs(c)) { skipWs(); i++; continue; }
      if (c !== 37) {
        const b = src.peek();
        if (b < 0) { if (src.isStdin) rt.eofReads++; return assigned === 0 && !consumedAny ? -1 : assigned; }
        if (b !== c) return assigned;
        src.next(); consumedAny = true; i++; continue;
      }
      i++;
      if (fmt[i] === 37) { skipWs(); if (src.peek() !== 37) return assigned; src.next(); i++; continue; }
      let suppress = false, width = null, len = '';
      if (fmt[i] === 42) { suppress = true; i++; }
      let w = ''; while (i < fmt.length && fmt[i] >= 48 && fmt[i] <= 57) { w += String.fromCharCode(fmt[i]); i++; }
      if (w) width = parseInt(w, 10);
      while (i < fmt.length && 'hlLqjzt'.includes(String.fromCharCode(fmt[i]))) { len += String.fromCharCode(fmt[i]); i++; }
      if (i >= fmt.length) throw rtError('type', `${name}(): 형식 문자열이 '%' 뒤에서 끝났습니다.`, line);
      const conv = String.fromCharCode(fmt[i]); i++;
      let scanset = null;
      if (conv === '[') {
        let neg = false; const set = new Set();
        if (fmt[i] === 94) { neg = true; i++; }
        if (fmt[i] === 93) { set.add(93); i++; }
        while (i < fmt.length && fmt[i] !== 93) {
          if (fmt[i + 1] === 45 && fmt[i + 2] != null && fmt[i + 2] !== 93) { for (let k = fmt[i]; k <= fmt[i + 2]; k++) set.add(k); i += 3; }
          else { set.add(fmt[i]); i++; }
        }
        i++;
        scanset = { neg, set };
      }
      let target = null;
      if (!suppress && conv !== 'n') {
        if (ai >= args.length) throw rtError('arg-count', `${name}(): 형식 문자열의 '%${conv}' 에 대응하는 인자가 없습니다. 입력받을 변수의 주소(&변수)를 전달했는지 확인하세요.`, line);
        const a = args[ai++];
        if (a.t.k === 'int' && !a.fromCast) throw rtError('type', `${name}(): '%${conv}' 에 변수의 주소가 아닌 정수 값 ${a.v} 을 전달했습니다. 변수 앞에 & 를 붙여야 합니다 (예: scanf("%d", &data)).`, line);
        if (a.t.k === 'struct') throw rtError('type', `${name}(): '%${conv}' 에 구조체를 전달했습니다. 멤버의 주소(&s.key)를 전달하세요.`, line);
        target = asPtr(a, name, ai, line);
        if (target === 0) throw rtError('null-deref', `${name}(): NULL 주소에 입력을 저장하려 했습니다.`, line);
        if (secure && (conv === 'c' || conv === 's' || conv === '[') && ai < args.length && args[ai].t.k === 'int') ai++; // scanf_s 의 버퍼 크기 인자
      }
      const storeInt = (v, unsigned) => {
        if (suppress) return;
        let t;
        if (len === 'hh') t = unsigned ? TY.uchar : TY.char; else if (len === 'h') t = unsigned ? TY.ushort : TY.short; else if (len === 'll' || len === 'q' || len === 'j') t = unsigned ? TY.ullong : TY.llong; else t = unsigned ? TY.uint : TY.int;
        rt.store(target, t, wrapInt(v, t), `${name} 대상 변수`);
      };
      switch (conv) {
        case 'd': case 'i': case 'u': case 'x': case 'X': case 'o': {
          skipWs();
          if (src.peek() < 0) return eofRet();
          let s = '', n = 0;
          const maxW = width == null ? Infinity : width;
          if ((src.peek() === 45 || src.peek() === 43) && n < maxW) { s += String.fromCharCode(src.next()); n++; }
          let base = conv === 'x' || conv === 'X' ? 16 : conv === 'o' ? 8 : 10;
          if (conv === 'i' && src.peek() === 48) { s += '0'; src.next(); n++; if ((src.peek() === 120 || src.peek() === 88) && n < maxW) { src.next(); n++; base = 16; s = s.slice(0, -1); } else base = 8; }
          if (base === 16 && src.peek() === 48) { /* 0x 접두 허용 */ }
          const isD = (b) => base === 10 ? (b >= 48 && b <= 57) : base === 8 ? (b >= 48 && b <= 55) : ((b >= 48 && b <= 57) || (b >= 97 && b <= 102) || (b >= 65 && b <= 70));
          let digits = '';
          while (src.peek() >= 0 && isD(src.peek()) && n < maxW) { digits += String.fromCharCode(src.next()); n++; }
          if (digits === '' && !(conv === 'i' && s.endsWith('0'))) return assigned;
          if (digits === '') digits = '0';
          const v = parseInt(digits, base) * (s.startsWith('-') ? -1 : 1);
          storeInt(v, conv === 'u' || conv === 'x' || conv === 'X' || conv === 'o');
          if (!suppress) assigned++;
          consumedAny = true;
          break;
        }
        case 'f': case 'e': case 'g': case 'E': case 'G': case 'a': case 'F': {
          skipWs();
          if (src.peek() < 0) return eofRet();
          let s = '', n = 0;
          const maxW = width == null ? Infinity : width;
          const ok = (b) => (b >= 48 && b <= 57) || b === 46 || b === 101 || b === 69 || b === 43 || b === 45;
          while (src.peek() >= 0 && ok(src.peek()) && n < maxW) {
            const b = src.peek();
            if ((b === 43 || b === 45) && n > 0 && !(s.endsWith('e') || s.endsWith('E'))) break;
            s += String.fromCharCode(src.next()); n++;
          }
          const v = parseFloat(s);
          if (isNaN(v)) return assigned;
          if (!suppress) { rt.store(target, len === 'l' || len === 'L' ? TY.double : TY.float, v, `${name} 대상 변수`); assigned++; }
          consumedAny = true;
          break;
        }
        case 'c': {
          const n = width == null ? 1 : width;
          if (src.peek() < 0) return eofRet();
          for (let k = 0; k < n; k++) {
            const b = src.next();
            if (b < 0) break;
            if (!suppress) rt.store(target + k, TY.char, (b << 24) >> 24, `${name} 대상 변수`);
          }
          if (!suppress) assigned++;
          consumedAny = true;
          break;
        }
        case 's': {
          skipWs();
          if (src.peek() < 0) return eofRet();
          const bytes = [];
          const maxW = width == null ? Infinity : width;
          while (src.peek() >= 0 && !isWs(src.peek()) && bytes.length < maxW) bytes.push(src.next());
          if (!suppress) { rt.writeCString(target, bytes, `${name} '%s' 대상 버퍼`); assigned++; }
          consumedAny = true;
          break;
        }
        case '[': {
          if (src.peek() < 0) return eofRet();
          const bytes = [];
          const maxW = width == null ? Infinity : width;
          const inSet = (b) => scanset.set.has(b) !== scanset.neg;
          while (src.peek() >= 0 && inSet(src.peek()) && bytes.length < maxW) bytes.push(src.next());
          if (bytes.length === 0) return assigned;
          if (!suppress) { rt.writeCString(target, bytes, `${name} '%[]' 대상 버퍼`); assigned++; }
          consumedAny = true;
          break;
        }
        case 'n': break;
        default: throw rtError('type', `${name}(): 알 수 없는 형식 지정자 '%${conv}' 입니다.`, line);
      }
    }
    return assigned;
  };
  def('scanf', (args, e) => { argN(args, 1, 'scanf', e.line); return int(doScanf(makeSource(null), asPtr(args[0], 'scanf', 1, e.line), args, 1, 'scanf', e.line)); });
  def('scanf_s', (args, e) => { argN(args, 1, 'scanf_s', e.line); return int(doScanf(makeSource(null), asPtr(args[0], 'scanf_s', 1, e.line), args, 1, 'scanf_s', e.line, true)); });
  def('sscanf_s', (args, e) => { argN(args, 2, 'sscanf_s', e.line); return int(doScanf(makeSource(asPtr(args[0], 'sscanf_s', 1, e.line), 'sscanf_s 입력 문자열', e.line), asPtr(args[1], 'sscanf_s', 2, e.line), args, 2, 'sscanf_s', e.line, true)); });
  def('fscanf', (args, e) => { argN(args, 2, 'fscanf', e.line); if ((args[0].v >>> 0) !== FILE_STDIN) throw rtError('type', 'fscanf(): stdin 만 지원합니다 (파일 입출력은 지원하지 않습니다).', e.line); return int(doScanf(makeSource(null), asPtr(args[1], 'fscanf', 2, e.line), args, 2, 'fscanf', e.line)); });
  def('sscanf', (args, e) => { argN(args, 2, 'sscanf', e.line); return int(doScanf(makeSource(asPtr(args[0], 'sscanf', 1, e.line), 'sscanf 입력 문자열', e.line), asPtr(args[1], 'sscanf', 2, e.line), args, 2, 'sscanf', e.line)); });
  const getcharImpl = () => int(rt.inNext());
  def('getchar', getcharImpl);
  def('getch', getcharImpl); def('_getch', getcharImpl); def('getche', getcharImpl); def('_getche', getcharImpl);
  def('getc', (args, e) => { argN(args, 1, 'getc', e.line); return int(rt.inNext()); });
  def('fgetc', (args, e) => { argN(args, 1, 'fgetc', e.line); return int(rt.inNext()); });
  def('ungetc', (args, e) => { argN(args, 2, 'ungetc', e.line); if (rt.inPos > 0) rt.inPos--; return int(asInt(args[0], 'ungetc', 1, e.line)); });
  def('feof', (args, e) => int(rt.inPeek() < 0 ? 1 : 0));
  def('rewind', () => num(V, 0));
  def('gets', (args, e) => { argN(args, 1, 'gets', e.line); const buf = asPtr(args[0], 'gets', 1, e.line); if (rt.inPeek() < 0) return ptr(CP, 0); const bytes = []; for (;;) { const b = rt.inNext(); if (b < 0 || b === 10) break; if (b !== 13) bytes.push(b); } rt.writeCString(buf, bytes, 'gets 버퍼'); return ptr(CP, buf); });
  def('gets_s', (args, e) => { argN(args, 2, 'gets_s', e.line); const buf = asPtr(args[0], 'gets_s', 1, e.line); const n = asInt(args[1], 'gets_s', 2, e.line); if (rt.inPeek() < 0) return ptr(CP, 0); const bytes = []; for (;;) { const b = rt.inNext(); if (b < 0 || b === 10) break; if (b !== 13 && bytes.length < n - 1) bytes.push(b); } rt.writeCString(buf, bytes, 'gets_s 버퍼'); return ptr(CP, buf); });
  def('fgets', (args, e) => { argN(args, 3, 'fgets', e.line); const buf = asPtr(args[0], 'fgets', 1, e.line); const n = asInt(args[1], 'fgets', 2, e.line); if (rt.inPeek() < 0 || n <= 0) return ptr(CP, 0); const bytes = []; while (bytes.length < n - 1) { const b = rt.inNext(); if (b < 0) break; bytes.push(b); if (b === 10) break; } rt.writeCString(buf, bytes, 'fgets 버퍼'); return ptr(CP, buf); });

  /* --- 메모리 --- */
  def('malloc', (args, e) => { argN(args, 1, 'malloc', e.line); const a = args[0]; if (a.t.k === 'ptr') throw rtError('type', `malloc() 의 인자는 바이트 수(정수)여야 하는데 포인터를 전달했습니다. sizeof(node) 처럼 크기를 전달하세요.`, e.line); const n = asInt(a, 'malloc', 1, e.line); if (n < 0 || n > HEAP_END - HEAP_BASE) throw rtError('out-of-memory', `malloc(${n}): 할당 크기가 잘못되었습니다.`, e.line); if (n === 0) rt.warn = (rt.warn || []).concat([`${e.line}번째 줄: malloc(0) 을 호출했습니다.`]); return ptr(VP, rt.heapAlloc(n)); });
  def('calloc', (args, e) => { argN(args, 2, 'calloc', e.line); const n = asInt(args[0], 'calloc', 1, e.line) * asInt(args[1], 'calloc', 2, e.line); if (n < 0 || n > HEAP_END - HEAP_BASE) throw rtError('out-of-memory', `calloc: 할당 크기가 잘못되었습니다.`, e.line); const a = rt.heapAlloc(n); rt.zeroInit(a, n); return ptr(VP, a); });
  def('realloc', (args, e) => { argN(args, 2, 'realloc', e.line); const p = asPtr(args[0], 'realloc', 1, e.line); const n = asInt(args[1], 'realloc', 2, e.line); const a = rt.heapAlloc(n); if (p !== 0) { const idx = rt.findBlock(p); if (idx < 0 || rt.hStart[idx] !== p) throw rtError('bad-free', 'realloc(): malloc 으로 받은 주소가 아닙니다.', e.line); if (!rt.hLive[idx]) throw rtError('use-after-free', 'realloc(): 이미 해제된 메모리입니다.', e.line); const sz = Math.min(rt.hSize[idx], n); rt.u8.copyWithin(a, p, p + sz); rt.shadow.copyWithin(a, p, p + sz); rt.hLive[idx] = false; } return ptr(VP, a); });
  def('free', (args, e) => { argN(args, 1, 'free', e.line); const a = args[0]; if (a.t.k === 'int' && a.v !== 0 && !a.fromCast) throw rtError('bad-free', `free() 에 포인터가 아닌 정수 값 ${a.v} 을 전달했습니다.`, e.line); if (a.t.k === 'struct') throw rtError('bad-free', `free() 에 구조체 값을 전달했습니다. 구조체 포인터를 전달해야 합니다.`, e.line); rt.heapFree(asPtr(a, 'free', 1, e.line)); return num(V, 0); });
  def('memset', (args, e) => { argN(args, 3, 'memset', e.line); const p = asPtr(args[0], 'memset', 1, e.line), v = asInt(args[1], 'memset', 2, e.line) & 0xff, n = asInt(args[2], 'memset', 3, e.line); if (n > 0) { rt.checkAccess(p, n, true, 'memset'); rt.u8.fill(v, p, p + n); rt.shadow.fill(1, p, p + n); } return ptr(VP, p); });
  def('memcpy', (args, e) => { argN(args, 3, 'memcpy', e.line); const d = asPtr(args[0], 'memcpy', 1, e.line), s = asPtr(args[1], 'memcpy', 2, e.line), n = asInt(args[2], 'memcpy', 3, e.line); if (n > 0) rt.copyBytes(d, s, n, 'memcpy'); return ptr(VP, d); });
  def('memmove', (args, e) => { argN(args, 3, 'memmove', e.line); const d = asPtr(args[0], 'memmove', 1, e.line), s = asPtr(args[1], 'memmove', 2, e.line), n = asInt(args[2], 'memmove', 3, e.line); if (n > 0) rt.copyBytes(d, s, n, 'memmove'); return ptr(VP, d); });
  def('memcmp', (args, e) => { argN(args, 3, 'memcmp', e.line); const a = asPtr(args[0], 'memcmp', 1, e.line), b = asPtr(args[1], 'memcmp', 2, e.line), n = asInt(args[2], 'memcmp', 3, e.line); for (let k = 0; k < n; k++) { rt.checkAccess(a + k, 1, false, 'memcmp'); rt.checkAccess(b + k, 1, false, 'memcmp'); const d = rt.u8[a + k] - rt.u8[b + k]; if (d) return int(d); } return int(0); });

  /* --- 문자열 --- */
  const cstr = (a, name, i, line) => { const p = asPtr(a, name, i, line); if (p === 0) throw rtError('null-deref', `${name}() 에 NULL 포인터를 전달했습니다.`, line); return rt.readCString(p, `${name} ${i}번째 인자`); };
  def('strlen', (args, e) => { argN(args, 1, 'strlen', e.line); return num(U, cstr(args[0], 'strlen', 1, e.line).length); });
  def('strcpy', (args, e) => { argN(args, 2, 'strcpy', e.line); const d = asPtr(args[0], 'strcpy', 1, e.line); rt.writeCString(d, cstr(args[1], 'strcpy', 2, e.line), 'strcpy 대상'); return ptr(CP, d); });
  def('strcpy_s', (args, e) => { argN(args, 3, 'strcpy_s', e.line); const d = asPtr(args[0], 'strcpy_s', 1, e.line); const n = asInt(args[1], 'strcpy_s', 2, e.line); const s = cstr(args[2], 'strcpy_s', 3, e.line); if (s.length >= n) throw rtError('heap-oob', 'strcpy_s(): 대상 버퍼가 작습니다.', e.line); rt.writeCString(d, s, 'strcpy_s 대상'); return int(0); });
  def('strncpy', (args, e) => { argN(args, 3, 'strncpy', e.line); const d = asPtr(args[0], 'strncpy', 1, e.line); const s = cstr(args[1], 'strncpy', 2, e.line); const n = asInt(args[2], 'strncpy', 3, e.line); rt.checkAccess(d, n, true, 'strncpy'); for (let k = 0; k < n; k++) { rt.u8[d + k] = k < s.length ? s[k] : 0; rt.shadow[d + k] = 1; } return ptr(CP, d); });
  def('strcat', (args, e) => { argN(args, 2, 'strcat', e.line); const d = asPtr(args[0], 'strcat', 1, e.line); const cur = cstr(args[0], 'strcat', 1, e.line); const s = cstr(args[1], 'strcat', 2, e.line); rt.writeCString(d, cur.concat(s), 'strcat 대상'); return ptr(CP, d); });
  def('strcat_s', (args, e) => { argN(args, 3, 'strcat_s', e.line); const d = asPtr(args[0], 'strcat_s', 1, e.line); const cur = cstr(args[0], 'strcat_s', 1, e.line); const s = cstr(args[2], 'strcat_s', 3, e.line); rt.writeCString(d, cur.concat(s), 'strcat_s 대상'); return int(0); });
  def('strncat', (args, e) => { argN(args, 3, 'strncat', e.line); const d = asPtr(args[0], 'strncat', 1, e.line); const cur = cstr(args[0], 'strncat', 1, e.line); const s = cstr(args[1], 'strncat', 2, e.line).slice(0, asInt(args[2], 'strncat', 3, e.line)); rt.writeCString(d, cur.concat(s), 'strncat 대상'); return ptr(CP, d); });
  const cmpBytes = (a, b, n) => { const m = Math.min(a.length, b.length, n); for (let k = 0; k < m; k++) if (a[k] !== b[k]) return a[k] < b[k] ? -1 : 1; if (n <= m) return 0; return a.length === b.length ? 0 : (a.length < b.length ? -1 : 1); };
  def('strcmp', (args, e) => { argN(args, 2, 'strcmp', e.line); return int(cmpBytes(cstr(args[0], 'strcmp', 1, e.line), cstr(args[1], 'strcmp', 2, e.line), Infinity)); });
  def('strncmp', (args, e) => { argN(args, 3, 'strncmp', e.line); return int(cmpBytes(cstr(args[0], 'strncmp', 1, e.line), cstr(args[1], 'strncmp', 2, e.line), asInt(args[2], 'strncmp', 3, e.line))); });
  def('stricmp', (args, e) => { argN(args, 2, 'stricmp', e.line); const lo = (b) => b.map(x => (x >= 65 && x <= 90) ? x + 32 : x); return int(cmpBytes(lo(cstr(args[0], 'stricmp', 1, e.line)), lo(cstr(args[1], 'stricmp', 2, e.line)), Infinity)); });
  def('_stricmp', (args, e) => rt.funcs.get('stricmp').impl(args, e));
  def('strchr', (args, e) => { argN(args, 2, 'strchr', e.line); const p = asPtr(args[0], 'strchr', 1, e.line); const s = cstr(args[0], 'strchr', 1, e.line); const c = asInt(args[1], 'strchr', 2, e.line) & 0xff; if (c === 0) return ptr(CP, p + s.length); const k = s.indexOf(c); return ptr(CP, k < 0 ? 0 : p + k); });
  def('strrchr', (args, e) => { argN(args, 2, 'strrchr', e.line); const p = asPtr(args[0], 'strrchr', 1, e.line); const s = cstr(args[0], 'strrchr', 1, e.line); const c = asInt(args[1], 'strrchr', 2, e.line) & 0xff; if (c === 0) return ptr(CP, p + s.length); const k = s.lastIndexOf(c); return ptr(CP, k < 0 ? 0 : p + k); });
  def('strstr', (args, e) => { argN(args, 2, 'strstr', e.line); const p = asPtr(args[0], 'strstr', 1, e.line); const s = String.fromCharCode(...cstr(args[0], 'strstr', 1, e.line)); const t = String.fromCharCode(...cstr(args[1], 'strstr', 2, e.line)); const k = s.indexOf(t); return ptr(CP, k < 0 ? 0 : p + k); });
  def('strdup', (args, e) => { argN(args, 1, 'strdup', e.line); const s = cstr(args[0], 'strdup', 1, e.line); const a = rt.heapAlloc(s.length + 1); rt.writeCString(a, s, 'strdup'); return ptr(CP, a); });
  def('_strdup', (args, e) => rt.funcs.get('strdup').impl(args, e));
  def('strtok', (args, e) => {
    argN(args, 2, 'strtok', e.line);
    let p = asPtr(args[0], 'strtok', 1, e.line);
    const delims = new Set(cstr(args[1], 'strtok', 2, e.line));
    if (p === 0) { p = rt.strtokPos || 0; if (p === 0) return ptr(CP, 0); }
    while (rt.u8[p] !== 0 && delims.has(rt.u8[p])) { rt.checkAccess(p, 1, false, 'strtok'); p++; }
    if (rt.u8[p] === 0) { rt.strtokPos = 0; return ptr(CP, 0); }
    const start = p;
    while (rt.u8[p] !== 0 && !delims.has(rt.u8[p])) { rt.checkAccess(p, 1, false, 'strtok'); p++; }
    if (rt.u8[p] !== 0) { rt.u8[p] = 0; rt.shadow[p] = 1; p++; }
    rt.strtokPos = p;
    return ptr(CP, start);
  });

  /* --- ctype --- */
  const ct = (name, f) => def(name, (args, e) => { argN(args, 1, name, e.line); const c = asInt(args[0], name, 1, e.line); return int(f(c) ? 1 : 0); });
  ct('isdigit', c => c >= 48 && c <= 57);
  ct('isalpha', c => (c >= 65 && c <= 90) || (c >= 97 && c <= 122));
  ct('isalnum', c => (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122));
  ct('isspace', c => c === 32 || (c >= 9 && c <= 13));
  ct('isupper', c => c >= 65 && c <= 90);
  ct('islower', c => c >= 97 && c <= 122);
  ct('ispunct', c => (c >= 33 && c <= 47) || (c >= 58 && c <= 64) || (c >= 91 && c <= 96) || (c >= 123 && c <= 126));
  ct('isxdigit', c => (c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102));
  ct('isprint', c => c >= 32 && c <= 126);
  ct('iscntrl', c => c < 32 || c === 127);
  def('toupper', (args, e) => { argN(args, 1, 'toupper', e.line); const c = asInt(args[0], 'toupper', 1, e.line); return int(c >= 97 && c <= 122 ? c - 32 : c); });
  def('tolower', (args, e) => { argN(args, 1, 'tolower', e.line); const c = asInt(args[0], 'tolower', 1, e.line); return int(c >= 65 && c <= 90 ? c + 32 : c); });

  /* --- stdlib --- */
  def('exit', (args, e) => { throw new ExitSignal(args.length ? (asInt(args[0], 'exit', 1, e.line) | 0) : 0); });
  def('_exit', (args, e) => { throw new ExitSignal(args.length ? (asInt(args[0], '_exit', 1, e.line) | 0) : 0); });
  def('abort', () => { throw rtError('abort', 'abort() 가 호출되었습니다.', rt.line); });
  def('abs', (args, e) => { argN(args, 1, 'abs', e.line); const a = args[0]; if (a.t.k === 'ptr') throw rtError('type', 'abs() 에 포인터를 전달했습니다.', e.line); return int(Math.abs(asNum(a, 'abs', 1, e.line)) | 0); });
  def('labs', (args, e) => { argN(args, 1, 'labs', e.line); return int(Math.abs(asInt(args[0], 'labs', 1, e.line)) | 0); });
  def('llabs', (args, e) => { argN(args, 1, 'llabs', e.line); return num(TY.llong, Math.abs(asInt(args[0], 'llabs', 1, e.line))); });
  def('atoi', (args, e) => { argN(args, 1, 'atoi', e.line); const s = String.fromCharCode(...cstr(args[0], 'atoi', 1, e.line)); const m = /^\s*[+-]?\d+/.exec(s); return int(m ? parseInt(m[0], 10) : 0); });
  def('atol', (args, e) => rt.funcs.get('atoi').impl(args, e));
  def('atoll', (args, e) => { argN(args, 1, 'atoll', e.line); const s = String.fromCharCode(...cstr(args[0], 'atoll', 1, e.line)); const m = /^\s*[+-]?\d+/.exec(s); return num(TY.llong, m ? parseInt(m[0], 10) : 0); });
  def('atof', (args, e) => { argN(args, 1, 'atof', e.line); const s = String.fromCharCode(...cstr(args[0], 'atof', 1, e.line)); const v = parseFloat(s); return num(D, isNaN(v) ? 0 : v); });
  def('strtol', (args, e) => { argN(args, 3, 'strtol', e.line); const p = asPtr(args[0], 'strtol', 1, e.line); const s = String.fromCharCode(...cstr(args[0], 'strtol', 1, e.line)); const base = asInt(args[2], 'strtol', 3, e.line) || 10; const m = base === 16 ? /^\s*[+-]?(0x)?[0-9a-fA-F]+/.exec(s) : /^\s*[+-]?[0-9]+/.exec(s); const endp = asPtr(args[1], 'strtol', 2, e.line); if (endp) rt.store(endp, CP, p + (m ? m[0].length : 0)); return int(m ? parseInt(m[0], base) : 0); });
  def('strtod', (args, e) => { argN(args, 2, 'strtod', e.line); const p = asPtr(args[0], 'strtod', 1, e.line); const s = String.fromCharCode(...cstr(args[0], 'strtod', 1, e.line)); const m = /^\s*[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?/.exec(s); const endp = asPtr(args[1], 'strtod', 2, e.line); if (endp) rt.store(endp, CP, p + (m ? m[0].length : 0)); return num(D, m ? parseFloat(m[0]) : 0); });
  def('rand', () => { rt.randState = (Math.imul(rt.randState, 1103515245) + 12345) >>> 0; return int((rt.randState >>> 16) & 0x7fff); });
  def('srand', (args, e) => { argN(args, 1, 'srand', e.line); rt.randState = asInt(args[0], 'srand', 1, e.line) >>> 0; return num(V, 0); });
  def('time', () => num(TY.llong, 1700000000));
  def('clock', () => int(Math.floor(rt.steps / 1000)));
  def('system', () => int(0));
  def('Sleep', () => num(V, 0));
  def('sleep', () => int(0));
  def('usleep', () => int(0));
  def('getenv', () => ptr(CP, 0));
  def('qsort', (args, e) => {
    argN(args, 4, 'qsort', e.line);
    const base = asPtr(args[0], 'qsort', 1, e.line), n = asInt(args[1], 'qsort', 2, e.line), sz = asInt(args[2], 'qsort', 3, e.line);
    const cmp = rt.fnByAddr(asPtr(args[3], 'qsort', 4, e.line));
    if (!cmp) throw rtError('type', 'qsort(): 비교 함수가 유효하지 않습니다.', e.line);
    rt.checkAccess(base, n * sz, true, 'qsort');
    const items = [];
    for (let k = 0; k < n; k++) items.push({ bytes: rt.u8.slice(base + k * sz, base + (k + 1) * sz), sh: rt.shadow.slice(base + k * sz, base + (k + 1) * sz) });
    const tmp1 = rt.heapAlloc(sz), tmp2 = rt.heapAlloc(sz);
    items.sort((x, y) => { rt.u8.set(x.bytes, tmp1); rt.shadow.set(x.sh, tmp1); rt.u8.set(y.bytes, tmp2); rt.shadow.set(y.sh, tmp2); const r = cmp.kind === 'user' ? rt.callUser(cmp, [ptr(VP, tmp1), ptr(VP, tmp2)], e.line) : cmp.impl([ptr(VP, tmp1), ptr(VP, tmp2)], e, cmp); return r.v; });
    items.forEach((it, k) => { rt.u8.set(it.bytes, base + k * sz); rt.shadow.set(it.sh, base + k * sz); });
    return num(V, 0);
  });

  /* --- math --- */
  const m1 = (name, f) => def(name, (args, e) => { argN(args, 1, name, e.line); return num(D, f(asNum(args[0], name, 1, e.line))); });
  m1('sqrt', Math.sqrt); m1('fabs', Math.abs); m1('floor', Math.floor); m1('ceil', Math.ceil); m1('round', (x) => Math.sign(x) * Math.round(Math.abs(x))); m1('trunc', Math.trunc);
  m1('log', Math.log); m1('log10', Math.log10); m1('log2', Math.log2); m1('exp', Math.exp); m1('sin', Math.sin); m1('cos', Math.cos); m1('tan', Math.tan); m1('asin', Math.asin); m1('acos', Math.acos); m1('atan', Math.atan); m1('sinh', Math.sinh); m1('cosh', Math.cosh); m1('tanh', Math.tanh);
  def('pow', (args, e) => { argN(args, 2, 'pow', e.line); return num(D, Math.pow(asNum(args[0], 'pow', 1, e.line), asNum(args[1], 'pow', 2, e.line))); });
  def('fmod', (args, e) => { argN(args, 2, 'fmod', e.line); return num(D, asNum(args[0], 'fmod', 1, e.line) % asNum(args[1], 'fmod', 2, e.line)); });
  def('atan2', (args, e) => { argN(args, 2, 'atan2', e.line); return num(D, Math.atan2(asNum(args[0], 'atan2', 1, e.line), asNum(args[1], 'atan2', 2, e.line))); });
  def('fmax', (args, e) => { argN(args, 2, 'fmax', e.line); return num(D, Math.max(asNum(args[0], 'fmax', 1, e.line), asNum(args[1], 'fmax', 2, e.line))); });
  def('fmin', (args, e) => { argN(args, 2, 'fmin', e.line); return num(D, Math.min(asNum(args[0], 'fmin', 1, e.line), asNum(args[1], 'fmin', 2, e.line))); });

  def('max', (args, e) => { argN(args, 2, 'max', e.line); const a = asNum(args[0], 'max', 1, e.line), b = asNum(args[1], 'max', 2, e.line); const t = (args[0].t.k === 'float' || args[1].t.k === 'float') ? D : I; return num(t, Math.max(a, b)); });
  def('min', (args, e) => { argN(args, 2, 'min', e.line); const a = asNum(args[0], 'min', 1, e.line), b = asNum(args[1], 'min', 2, e.line); const t = (args[0].t.k === 'float' || args[1].t.k === 'float') ? D : I; return num(t, Math.min(a, b)); });
  def('__max', (args, e) => rt.funcs.get('max').impl(args, e));
  def('__min', (args, e) => rt.funcs.get('min').impl(args, e));

  /* FILE 포인터 전역 */
  const fileT = ptrTo(TY.void);
  for (const [name, val] of [['stdin', FILE_STDIN], ['stdout', FILE_STDOUT], ['stderr', FILE_STDERR]]) {
    const addr = rt.allocStatic(4, 4);
    rt.store(addr, fileT, val);
    rt.globals.set(name, { addr, type: fileT });
  }
}

/* ============================================================
 *  진입점
 * ============================================================ */
function compileAndRun(source, input, opts) {
  opts = opts || {};
  const result = { status: 'ok', exitCode: 0, stdout: '', stderr: '', error: null, warnings: [], steps: 0, functions: [], includes: [] };
  let rt = null;
  try {
    const pp = preprocess(source);
    result.includes = pp.includes;
    result.warnings.push(...pp.warnings);
    const env = { typedefs: new Map(), structs: new Map(), enums: new Map() };
    // 기본 typedef
    env.typedefs.set('size_t', TY.uint);
    env.typedefs.set('FILE', { k: 'struct', tag: 'FILE', fields: [], size: 4, align: 4, complete: true });
    env.typedefs.set('bool', TY.bool);
    env.typedefs.set('ptrdiff_t', TY.int);
    env.typedefs.set('int8_t', TY.schar); env.typedefs.set('uint8_t', TY.uchar); env.typedefs.set('int16_t', TY.short); env.typedefs.set('uint16_t', TY.ushort);
    env.typedefs.set('int32_t', TY.int); env.typedefs.set('uint32_t', TY.uint); env.typedefs.set('int64_t', TY.llong); env.typedefs.set('uint64_t', TY.ullong);
    env.typedefs.set('time_t', TY.llong); env.typedefs.set('clock_t', TY.int);
    const parser = new Parser(pp.tokens, env, false);
    // 사용자 정의 bool 과 충돌 방지: 사용자가 typedef 하면 덮어씀
    const unit = parser.parseTranslationUnit();
    result.functions = unit.decls.filter(d => d.kind === 'func').map(d => d.name);
    rt = new Runtime(unit, env, opts);
    result.exitCode = rt.run(input);
  } catch (e) {
    if (e instanceof CError) {
      result.status = e.kind === 'compile' ? 'compile_error' : 'runtime_error';
      result.error = { kind: e.kind, ekind: e.ekind || null, message: e.message, line: e.cline || (rt ? rt.line : 0) };
    } else if (e instanceof RangeError && /call stack/i.test(String(e.message))) {
      result.status = 'runtime_error';
      result.error = { kind: 'runtime', ekind: 'stack-overflow', message: '재귀 호출이 너무 깊어 스택이 넘쳤습니다 (스택 오버플로). 재귀 함수의 종료 조건을 확인하세요.', line: rt ? rt.line : 0 };
    } else {
      result.status = 'internal_error';
      result.error = { kind: 'internal', message: String(e && e.stack || e), line: rt ? rt.line : 0 };
    }
  }
  if (rt) {
    result.stdout = new TextDecoder().decode(new Uint8Array(rt.out));
    result.stderr = new TextDecoder().decode(new Uint8Array(rt.err));
    result.steps = rt.steps;
    result.eofReads = rt.eofReads;
    if (rt.warn) result.warnings.push(...rt.warn.slice(0, 5));
  }
  return result;
}

if (typeof module !== 'undefined') module.exports = { compileAndRun, Runtime, ExitSignal };
