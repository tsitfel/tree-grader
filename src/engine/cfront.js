/* ============================================================
 *  cfront.js — C 소스 전처리기 · 어휘분석기 · 구문분석기
 *  (교육용 C 인터프리터 프런트엔드, 외부 의존성 없음)
 * ============================================================ */
'use strict';

class CError extends Error {
  constructor(kind, message, line, col) {
    super(message);
    this.kind = kind;        // 'compile' | 'runtime'
    this.cline = line || 0;
    this.ccol = col || 0;
  }
}

/* ---------------- 타입 시스템 ---------------- */
const TY = (() => {
  const mk = (o) => Object.freeze(o);
  const t = {
    void:   mk({ k: 'void', size: 1, align: 1, name: 'void' }),
    bool:   mk({ k: 'int', size: 1, align: 1, signed: false, isBool: true, name: '_Bool' }),
    char:   mk({ k: 'int', size: 1, align: 1, signed: true, name: 'char' }),
    schar:  mk({ k: 'int', size: 1, align: 1, signed: true, name: 'signed char' }),
    uchar:  mk({ k: 'int', size: 1, align: 1, signed: false, name: 'unsigned char' }),
    short:  mk({ k: 'int', size: 2, align: 2, signed: true, name: 'short' }),
    ushort: mk({ k: 'int', size: 2, align: 2, signed: false, name: 'unsigned short' }),
    int:    mk({ k: 'int', size: 4, align: 4, signed: true, name: 'int' }),
    uint:   mk({ k: 'int', size: 4, align: 4, signed: false, name: 'unsigned int' }),
    long:   mk({ k: 'int', size: 4, align: 4, signed: true, name: 'long' }),
    ulong:  mk({ k: 'int', size: 4, align: 4, signed: false, name: 'unsigned long' }),
    llong:  mk({ k: 'int', size: 8, align: 8, signed: true, name: 'long long' }),
    ullong: mk({ k: 'int', size: 8, align: 8, signed: false, name: 'unsigned long long' }),
    float:  mk({ k: 'float', size: 4, align: 4, name: 'float' }),
    double: mk({ k: 'float', size: 8, align: 8, name: 'double' }),
  };
  return t;
})();

function ptrTo(to) { return { k: 'ptr', to, size: 4, align: 4 }; }
function arrOf(of, n) { return { k: 'arr', of, n, size: (n == null ? 0 : n * of.size), align: of.align, incomplete: n == null }; }
function fnType(ret, params, variadic, oldStyle) { return { k: 'fn', ret, params, variadic: !!variadic, oldStyle: !!oldStyle, size: 1, align: 1 }; }
function isInt(t) { return t.k === 'int'; }
function isFloat(t) { return t.k === 'float'; }
function isArith(t) { return t.k === 'int' || t.k === 'float'; }
function isPtr(t) { return t.k === 'ptr'; }
function isScalar(t) { return t.k === 'int' || t.k === 'float' || t.k === 'ptr'; }
function typeName(t) {
  if (!t) return '?';
  switch (t.k) {
    case 'void': case 'int': case 'float': return t.name;
    case 'ptr': return t.to.k === 'fn' ? typeName(t.to.ret) + ' (*)(...)' : typeName(t.to) + '*';
    case 'arr': return typeName(t.of) + '[' + (t.n == null ? '' : t.n) + ']';
    case 'struct': return (t.union ? 'union ' : 'struct ') + (t.tag || '(anonymous)');
    case 'fn': return typeName(t.ret) + ' (' + t.params.map(p => typeName(p.type)).join(', ') + (t.variadic ? ', ...' : '') + ')';
  }
  return '?';
}
function sameType(a, b) {
  if (a === b) return true;
  if (a.k !== b.k) return false;
  switch (a.k) {
    case 'int': return a.size === b.size && a.signed === b.signed;
    case 'float': return a.size === b.size;
    case 'ptr': return sameType(a.to, b.to);
    case 'arr': return a.n === b.n && sameType(a.of, b.of);
    case 'struct': return a === b;
    case 'fn': return sameType(a.ret, b.ret) && a.params.length === b.params.length && a.params.every((p, i) => sameType(p.type, b.params[i].type));
    case 'void': return true;
  }
  return false;
}

/* ---------------- 어휘분석기 ---------------- */
const KEYWORDS = new Set(['auto', 'break', 'case', 'char', 'const', 'continue', 'default', 'do', 'double', 'else', 'enum', 'extern', 'float', 'for', 'goto', 'if', 'inline', 'int', 'long', 'register', 'restrict', 'return', 'short', 'signed', 'sizeof', 'static', 'struct', 'switch', 'typedef', 'union', 'unsigned', 'void', 'volatile', 'while', '_Bool', '__inline', '__forceinline']);
const PUNCT = ['...', '<<=', '>>=', '->', '++', '--', '<<', '>>', '<=', '>=', '==', '!=', '&&', '||', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '##', '#', '(', ')', '[', ']', '{', '}', '.', ',', ';', ':', '?', '~', '!', '+', '-', '*', '/', '%', '<', '>', '=', '&', '|', '^'];

function isIdStart(c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c === '_' || c === '$' || c > '\x7f'; }
function isIdChar(c) { return isIdStart(c) || (c >= '0' && c <= '9'); }
function isDigit(c) { return c >= '0' && c <= '9'; }

function readEscape(s, i, line) {
  // s[i] is the char after the backslash; returns [code, nextIndex]
  const c = s[i];
  const simple = { n: 10, t: 9, r: 13, a: 7, b: 8, f: 12, v: 11, '0': 0, '\\': 92, '\'': 39, '"': 34, '?': 63, e: 27 };
  if (c === 'x') {
    let j = i + 1, v = 0, any = false;
    while (j < s.length && /[0-9a-fA-F]/.test(s[j])) { v = v * 16 + parseInt(s[j], 16); j++; any = true; }
    if (!any) throw new CError('compile', '잘못된 16진수 이스케이프(\\x)입니다.', line);
    return [v & 0xff, j];
  }
  if (c >= '0' && c <= '7') {
    let j = i, v = 0, n = 0;
    while (j < s.length && n < 3 && s[j] >= '0' && s[j] <= '7') { v = v * 8 + (s.charCodeAt(j) - 48); j++; n++; }
    return [v & 0xff, j];
  }
  if (c in simple) return [simple[c], i + 1];
  return [c.charCodeAt(0), i + 1];
}

function lexLine(s, line, out) {
  let i = 0;
  const n = s.length;
  while (i < n) {
    const c = s[i];
    if (c === ' ' || c === '\t' || c === '\r' || c === '\f' || c === '\v' || c === '\n') { i++; continue; }
    const col = i + 1;
    if (isIdStart(c)) {
      let j = i + 1;
      while (j < n && isIdChar(s[j])) j++;
      const w = s.slice(i, j);
      out.push({ t: KEYWORDS.has(w) ? 'kw' : 'id', v: w, line, col });
      i = j; continue;
    }
    if (isDigit(c) || (c === '.' && i + 1 < n && isDigit(s[i + 1]))) {
      let j = i, isF = false;
      if (c === '0' && (s[i + 1] === 'x' || s[i + 1] === 'X')) {
        j = i + 2;
        while (j < n && /[0-9a-fA-F]/.test(s[j])) j++;
        const text = s.slice(i, j);
        let suf = '';
        while (j < n && /[uUlL]/.test(s[j])) { suf += s[j]; j++; }
        out.push({ t: 'num', v: parseInt(text, 16), isFloat: false, suffix: suf.toLowerCase(), text, line, col });
        i = j; continue;
      }
      while (j < n && isDigit(s[j])) j++;
      if (j < n && s[j] === '.') { isF = true; j++; while (j < n && isDigit(s[j])) j++; }
      if (j < n && (s[j] === 'e' || s[j] === 'E')) {
        let k = j + 1;
        if (k < n && (s[k] === '+' || s[k] === '-')) k++;
        if (k < n && isDigit(s[k])) { isF = true; j = k; while (j < n && isDigit(s[j])) j++; }
      }
      const text = s.slice(i, j);
      let suf = '';
      while (j < n && /[uUlLfF]/.test(s[j])) { suf += s[j]; j++; }
      let v;
      if (isF) v = parseFloat(text);
      else if (text.length > 1 && text[0] === '0' && /^[0-7]+$/.test(text)) v = parseInt(text, 8);
      else v = parseInt(text, 10);
      if (!isF && /f/i.test(suf)) isF = true;
      out.push({ t: 'num', v, isFloat: isF, suffix: suf.toLowerCase(), text, line, col });
      i = j; continue;
    }
    if (c === '\'') {
      let j = i + 1;
      const codes = [];
      while (j < n && s[j] !== '\'') {
        if (s[j] === '\\') { const [v, nj] = readEscape(s, j + 1, line); codes.push(v); j = nj; }
        else { codes.push(s.charCodeAt(j)); j++; }
      }
      if (j >= n) throw new CError('compile', "문자 상수가 닫히지 않았습니다 (')가 없습니다).", line, col);
      if (codes.length === 0) throw new CError('compile', '빈 문자 상수입니다.', line, col);
      let v = 0;
      for (const cc of codes) v = (v << 8) | (cc & 0xff);
      if (codes.length === 1) v = (codes[0] << 24) >> 24; // char는 부호 있는 1바이트
      out.push({ t: 'chr', v, line, col });
      i = j + 1; continue;
    }
    if (c === '"') {
      let j = i + 1;
      const bytes = [];
      while (j < n && s[j] !== '"') {
        if (s[j] === '\\') { const [v, nj] = readEscape(s, j + 1, line); bytes.push(v); j = nj; }
        else {
          const code = s.codePointAt(j);
          if (code < 0x80) { bytes.push(code); j++; }
          else { // UTF-8 인코딩
            const str = String.fromCodePoint(code);
            for (const b of new TextEncoder().encode(str)) bytes.push(b);
            j += str.length;
          }
        }
      }
      if (j >= n) throw new CError('compile', '문자열 상수가 닫히지 않았습니다 (")가 없습니다).', line, col);
      out.push({ t: 'str', v: bytes, line, col });
      i = j + 1; continue;
    }
    let matched = null;
    for (const p of PUNCT) { if (s.startsWith(p, i)) { matched = p; break; } }
    if (matched) { out.push({ t: 'op', v: matched, line, col }); i += matched.length; continue; }
    if (c === '@' || c === '`') throw new CError('compile', `사용할 수 없는 문자 '${c}' 입니다.`, line, col);
    throw new CError('compile', `알 수 없는 문자 '${c}' 입니다.`, line, col);
  }
}

/* ---------------- 전처리기 ---------------- */
function stripComments(src) {
  let out = '';
  let i = 0; const n = src.length;
  while (i < n) {
    const c = src[i];
    if (c === '/' && src[i + 1] === '/') {
      while (i < n && src[i] !== '\n') i++;
      continue;
    }
    if (c === '/' && src[i + 1] === '*') {
      i += 2;
      out += ' ';
      while (i < n && !(src[i] === '*' && src[i + 1] === '/')) { if (src[i] === '\n') out += '\n'; i++; }
      i += 2; continue;
    }
    if (c === '"' || c === '\'') {
      const q = c; out += c; i++;
      while (i < n && src[i] !== q && src[i] !== '\n') {
        if (src[i] === '\\' && i + 1 < n) { out += src[i] + src[i + 1]; i += 2; continue; }
        out += src[i]; i++;
      }
      if (i < n && src[i] === q) { out += q; i++; }
      continue;
    }
    out += c; i++;
  }
  return out;
}

const STD_HEADERS = new Set(['stdio.h', 'stdlib.h', 'string.h', 'math.h', 'ctype.h', 'stdbool.h', 'limits.h', 'time.h', 'assert.h', 'stdint.h', 'stddef.h', 'float.h', 'errno.h', 'malloc.h', 'memory.h', 'conio.h', 'windows.h', 'unistd.h', 'stdarg.h', 'locale.h', 'signal.h', 'setjmp.h', 'wchar.h', 'tchar.h', 'process.h', 'io.h', 'direct.h', 'crtdbg.h', 'inttypes.h', 'iso646.h']);

function preprocess(src) {
  src = src.replace(/\r\n?/g, '\n').replace(/^﻿/, '');
  src = stripComments(src);
  const rawLines = src.split('\n');
  // 줄 이어쓰기(\) 처리: 이어진 줄 수만큼 빈 줄을 뒤에 넣어 줄 번호를 유지한다.
  const lines = [];
  for (let i = 0; i < rawLines.length; i++) {
    let s = rawLines[i], joined = 0;
    while (/\\\s*$/.test(s) && i + 1 < rawLines.length) { s = s.replace(/\\\s*$/, '') + rawLines[i + 1]; i++; joined++; }
    lines.push(s);
    for (let k = 0; k < joined; k++) lines.push('');
  }

  const macros = new Map();
  const defineMacro = (name, params, bodyText, line) => {
    const body = [];
    lexLine(bodyText, line, body);
    macros.set(name, { params, body, line });
  };
  // 기본 매크로
  defineMacro('NULL', null, '0', 0);
  defineMacro('EOF', null, '(-1)', 0);
  defineMacro('INT_MAX', null, '2147483647', 0);
  defineMacro('INT_MIN', null, '(-2147483647-1)', 0);
  defineMacro('UINT_MAX', null, '4294967295u', 0);
  defineMacro('LONG_MAX', null, '2147483647', 0);
  defineMacro('LONG_MIN', null, '(-2147483647-1)', 0);
  defineMacro('LLONG_MAX', null, '9223372036854775807', 0);
  defineMacro('CHAR_MAX', null, '127', 0);
  defineMacro('CHAR_MIN', null, '(-128)', 0);
  defineMacro('SHRT_MAX', null, '32767', 0);
  defineMacro('RAND_MAX', null, '32767', 0);
  defineMacro('BUFSIZ', null, '512', 0);
  defineMacro('_CRT_SECURE_NO_WARNINGS', null, '', 0);
  defineMacro('assert', ['x'], '((void)0)', 0);
  defineMacro('__FILE__', null, '"main.c"', 0);
  defineMacro('__func__', null, '"?"', 0);
  defineMacro('__cplusplus_dummy__', null, '', 0);

  const includes = [];
  const warnings = [];
  const toks = [];
  const cond = []; // {active, anyTaken, parentActive}
  const isActive = () => cond.every(c => c.active);

  const evalIfExpr = (text, line) => {
    const lt = [];
    try { lexLine(text, line, lt); } catch (e) { return 0; }
    // defined X / defined(X)
    const t2 = [];
    for (let i = 0; i < lt.length; i++) {
      if (lt[i].t === 'id' && lt[i].v === 'defined') {
        let name = null;
        if (lt[i + 1] && lt[i + 1].t === 'op' && lt[i + 1].v === '(') { name = lt[i + 2] && lt[i + 2].v; i += 3; }
        else { name = lt[i + 1] && lt[i + 1].v; i += 1; }
        t2.push({ t: 'num', v: macros.has(name) ? 1 : 0, isFloat: false, suffix: '', line });
      } else t2.push(lt[i]);
    }
    const expanded = expandTokens(t2, macros, line).map(t => (t.t === 'id') ? { t: 'num', v: 0, isFloat: false, suffix: '', line } : t);
    try {
      const p = new Parser(expanded.concat([{ t: 'eof', line }]), { typedefs: new Map(), structs: new Map(), enums: new Map() }, true);
      const e = p.parseExpr();
      return constEval(e, p) ? 1 : 0;
    } catch (e) { return 0; }
  };

  for (let ln = 0; ln < lines.length; ln++) {
    const lineNo = ln + 1;
    const s = lines[ln];
    const m = /^\s*#\s*([A-Za-z_]*)\s*(.*)$/.exec(s);
    if (m) {
      const dir = m[1], rest = m[2];
      switch (dir) {
        case 'ifdef': { const a = isActive(); const nm = rest.trim().split(/\s+/)[0]; const take = macros.has(nm); cond.push({ active: a && take, anyTaken: take, parentActive: a }); break; }
        case 'ifndef': { const a = isActive(); const nm = rest.trim().split(/\s+/)[0]; const take = !macros.has(nm); cond.push({ active: a && take, anyTaken: take, parentActive: a }); break; }
        case 'if': { const a = isActive(); const take = a ? !!evalIfExpr(rest, lineNo) : false; cond.push({ active: a && take, anyTaken: take, parentActive: a }); break; }
        case 'elif': {
          if (!cond.length) throw new CError('compile', '#if 없이 #elif 가 나왔습니다.', lineNo);
          const c = cond[cond.length - 1];
          if (c.anyTaken || !c.parentActive) c.active = false;
          else { const take = !!evalIfExpr(rest, lineNo); c.active = take; c.anyTaken = take; }
          break;
        }
        case 'else': {
          if (!cond.length) throw new CError('compile', '#if 없이 #else 가 나왔습니다.', lineNo);
          const c = cond[cond.length - 1];
          c.active = c.parentActive && !c.anyTaken; c.anyTaken = true; break;
        }
        case 'endif': if (!cond.length) throw new CError('compile', '#if 없이 #endif 가 나왔습니다.', lineNo); cond.pop(); break;
        default:
          if (!isActive()) break;
          if (dir === 'include') {
            const im = /^[<"]([^>"]*)[>"]/.exec(rest);
            const name = im ? im[1] : rest;
            includes.push(name);
            const low = name.toLowerCase().replace(/^.*\//, '');
            if (!STD_HEADERS.has(low)) warnings.push(`${lineNo}번째 줄: 헤더 <${name}> 는 이 채점 환경에서 제공되지 않아 무시했습니다.`);
            if (low === 'stdbool.h') { defineMacro('true', null, '1', 0); defineMacro('false', null, '0', 0); defineMacro('bool', null, '_Bool', 0); }
            if (low === 'stdint.h' || low === 'inttypes.h') {
              for (const [a, b] of [['int8_t', 'signed char'], ['uint8_t', 'unsigned char'], ['int16_t', 'short'], ['uint16_t', 'unsigned short'], ['int32_t', 'int'], ['uint32_t', 'unsigned int'], ['int64_t', 'long long'], ['uint64_t', 'unsigned long long']]) defineMacro(a, null, b, 0);
            }
          } else if (dir === 'define') {
            const dm = /^([A-Za-z_][A-Za-z0-9_]*)(\(([^)]*)\))?\s*(.*)$/.exec(rest);
            if (!dm) throw new CError('compile', '#define 형식이 잘못되었습니다.', lineNo);
            const name = dm[1];
            const params = dm[2] != null ? (dm[3].trim() === '' ? [] : dm[3].split(',').map(x => x.trim())) : null;
            defineMacro(name, params, dm[4], lineNo);
          } else if (dir === 'undef') {
            macros.delete(rest.trim().split(/\s+/)[0]);
          } else if (dir === 'pragma' || dir === 'line' || dir === 'warning' || dir === '') {
            /* 무시 */
          } else if (dir === 'error') {
            throw new CError('compile', '#error: ' + rest, lineNo);
          } else {
            warnings.push(`${lineNo}번째 줄: 알 수 없는 전처리 지시문 #${dir} 를 무시했습니다.`);
          }
      }
      continue;
    }
    if (!isActive()) continue;
    if (/^\s*$/.test(s)) continue;
    const lt = [];
    lexLine(s, lineNo, lt);
    for (const t of lt) toks.push(t);
  }
  if (cond.length) throw new CError('compile', '#if/#ifdef 에 대응하는 #endif 가 없습니다.', lines.length);
  const expanded = expandTokens(toks, macros, null);
  expanded.push({ t: 'eof', line: lines.length + 1, col: 1 });
  return { tokens: expanded, includes, warnings, macros };
}

function expandTokens(tokens, macros, forceLine) {
  const out = [];
  const work = tokens.slice().reverse(); // 스택처럼 사용 (pop = 다음 토큰)
  const guard = 0;
  let expansions = 0;
  while (work.length) {
    const t = work.pop();
    if (t.t === 'id' && macros.has(t.v) && !(t.noexp && t.noexp.has(t.v))) {
      const m = macros.get(t.v);
      if (++expansions > 200000) throw new CError('compile', '매크로 확장이 너무 많습니다 (재귀적 #define?).', t.line);
      const useLine = forceLine != null ? forceLine : t.line;
      const noexp = new Set(t.noexp || []); noexp.add(t.v);
      if (m.params === null) {
        const body = m.body.map(b => Object.assign({}, b, { line: useLine, col: t.col, noexp }));
        for (let i = body.length - 1; i >= 0; i--) work.push(body[i]);
        continue;
      }
      // 함수형 매크로: 다음 토큰이 '(' 이어야 확장
      const nt = work[work.length - 1];
      if (!nt || nt.t !== 'op' || nt.v !== '(') { out.push(Object.assign({}, t, { t: 'id' })); continue; }
      work.pop();
      const args = [];
      let cur = [], depth = 0, closed = false;
      while (work.length) {
        const a = work.pop();
        if (a.t === 'op' && a.v === '(') { depth++; cur.push(a); }
        else if (a.t === 'op' && a.v === ')') { if (depth === 0) { closed = true; break; } depth--; cur.push(a); }
        else if (a.t === 'op' && a.v === ',' && depth === 0) { args.push(cur); cur = []; }
        else cur.push(a);
      }
      if (!closed) throw new CError('compile', `매크로 ${t.v}(...) 의 괄호가 닫히지 않았습니다.`, t.line);
      if (cur.length || args.length || m.params.length) args.push(cur);
      if (m.params.length === 0 && args.length === 1 && args[0].length === 0) args.length = 0;
      if (args.length !== m.params.length) throw new CError('compile', `매크로 ${t.v} 는 인자 ${m.params.length}개가 필요하지만 ${args.length}개가 주어졌습니다.`, t.line);
      const expArgs = args.map(a => expandTokens(a, macros, useLine));
      const body = [];
      for (let i = 0; i < m.body.length; i++) {
        const b = m.body[i];
        const pi = (b.t === 'id') ? m.params.indexOf(b.v) : -1;
        if (pi >= 0) { for (const x of expArgs[pi]) body.push(Object.assign({}, x, { line: useLine, noexp })); }
        else body.push(Object.assign({}, b, { line: useLine, col: t.col, noexp }));
      }
      for (let i = body.length - 1; i >= 0; i--) work.push(body[i]);
      continue;
    }
    out.push(t);
  }
  return out;
}

/* ---------------- 구문분석기 ---------------- */
const TYPE_KW = new Set(['void', 'char', 'short', 'int', 'long', 'float', 'double', 'signed', 'unsigned', '_Bool', 'struct', 'union', 'enum', 'const', 'volatile', 'static', 'extern', 'typedef', 'register', 'auto', 'inline', '__inline', '__forceinline', 'restrict']);

class Parser {
  constructor(tokens, env, constOnly) {
    this.toks = tokens;
    this.i = 0;
    this.typedefs = env.typedefs;   // Map name -> type (전역 범위 + 블록 범위 스택으로 관리)
    this.structs = env.structs;     // Map tag -> struct type
    this.enums = env.enums;         // Map name -> int value (열거 상수)
    this.scopeStack = [];           // 블록 범위에서 typedef / 변수 가림 처리용: Set of names declared as variables
    this.constOnly = !!constOnly;
    this.stringLits = [];
    this.anonCount = 0;
    this.funcNames = new Set();
    this.varNamesGlobal = new Set();
  }
  peek(o = 0) { return this.toks[Math.min(this.i + o, this.toks.length - 1)]; }
  next() { const t = this.toks[this.i]; if (this.i < this.toks.length - 1) this.i++; return t; }
  isOp(v, o = 0) { const t = this.peek(o); return t.t === 'op' && t.v === v; }
  isKw(v, o = 0) { const t = this.peek(o); return t.t === 'kw' && t.v === v; }
  accept(v) { if (this.isOp(v) || this.isKw(v)) { return this.next(); } return null; }
  expect(v, what) {
    if (this.isOp(v) || this.isKw(v)) return this.next();
    const t = this.peek();
    const near = (t.t === 'eof') ? '파일 끝' : `'${this.tokText(t)}'`;
    throw new CError('compile', `'${v}' 가 필요합니다${what ? ' (' + what + ')' : ''}. (${near} 근처)`, t.line, t.col);
  }
  tokText(t) {
    if (t.t === 'str') return '"' + String.fromCharCode(...t.v.slice(0, 20)) + '"';
    if (t.t === 'chr') return "'" + String.fromCharCode(t.v & 0xff) + "'";
    if (t.t === 'num') return t.text || String(t.v);
    if (t.t === 'eof') return '<EOF>';
    return String(t.v);
  }
  err(msg, t) { t = t || this.peek(); throw new CError('compile', msg, t.line, t.col); }

  isTypedefName(name) {
    // 블록 범위에서 같은 이름의 변수가 선언되었으면 typedef 이름이 아님
    for (let i = this.scopeStack.length - 1; i >= 0; i--) {
      const sc = this.scopeStack[i];
      if (sc.vars.has(name)) return false;
      if (sc.typedefs.has(name)) return true;
    }
    if (this.varNamesGlobal.has(name) || this.funcNames.has(name)) return false;
    return this.typedefs.has(name);
  }
  lookupTypedef(name) {
    for (let i = this.scopeStack.length - 1; i >= 0; i--) {
      const sc = this.scopeStack[i];
      if (sc.vars.has(name)) return null;
      if (sc.typedefs.has(name)) return sc.typedefs.get(name);
    }
    return this.typedefs.get(name) || null;
  }
  declareVarName(name) {
    if (this.scopeStack.length) this.scopeStack[this.scopeStack.length - 1].vars.add(name);
    else this.varNamesGlobal.add(name);
  }
  declareTypedef(name, type) {
    if (this.scopeStack.length) this.scopeStack[this.scopeStack.length - 1].typedefs.set(name, type);
    else this.typedefs.set(name, type);
  }
  pushScope() { this.scopeStack.push({ vars: new Set(), typedefs: new Map() }); }
  popScope() { this.scopeStack.pop(); }

  startsDecl() {
    const t = this.peek();
    if (t.t === 'kw') return TYPE_KW.has(t.v);
    if (t.t === 'id') {
      if (!this.isTypedefName(t.v)) return false;
      // typedef 이름 뒤에 식별자/별표/괄호가 오면 선언으로 간주
      const n = this.peek(1);
      if (n.t === 'id') return true;
      if (n.t === 'op' && (n.v === '*' || n.v === '(' )) return true;
      if (n.t === 'kw' && (n.v === 'const' || n.v === 'volatile')) return true;
      return false;
    }
    return false;
  }
  startsTypeName() {
    const t = this.peek();
    if (t.t === 'kw') return TYPE_KW.has(t.v) && !['static', 'extern', 'typedef', 'register', 'auto', 'inline', '__inline', '__forceinline'].includes(t.v);
    if (t.t === 'id') return this.isTypedefName(t.v);
    return false;
  }

  /* ---- 번역 단위 ---- */
  parseTranslationUnit() {
    const decls = [];
    while (this.peek().t !== 'eof') {
      if (this.accept(';')) continue;
      const d = this.parseExternalDecl();
      if (d) decls.push(...(Array.isArray(d) ? d : [d]));
    }
    return { kind: 'unit', decls, stringLits: this.stringLits };
  }

  parseDeclSpecs() {
    const t0 = this.peek();
    let storage = null, isTypedef = false, isConst = false;
    let base = null, sign = null, longs = 0, short = false, seenInt = false;
    let struct = null, typedefName = null;
    let any = false;
    for (;;) {
      const t = this.peek();
      if (t.t === 'kw') {
        if (t.v === 'typedef') { isTypedef = true; this.next(); any = true; continue; }
        if (t.v === 'static' || t.v === 'extern' || t.v === 'register' || t.v === 'auto') { storage = t.v; this.next(); any = true; continue; }
        if (t.v === 'const' || t.v === 'volatile' || t.v === 'inline' || t.v === '__inline' || t.v === '__forceinline' || t.v === 'restrict') { if (t.v === 'const') isConst = true; this.next(); any = true; continue; }
        if (t.v === 'void' || t.v === 'char' || t.v === 'float' || t.v === 'double' || t.v === '_Bool') { if (base) this.err(`타입 지정이 중복되었습니다 ('${t.v}').`); base = t.v; this.next(); any = true; continue; }
        if (t.v === 'int') { seenInt = true; this.next(); any = true; continue; }
        if (t.v === 'short') { short = true; this.next(); any = true; continue; }
        if (t.v === 'long') { longs++; this.next(); any = true; continue; }
        if (t.v === 'signed' || t.v === 'unsigned') { sign = t.v; this.next(); any = true; continue; }
        if (t.v === 'struct' || t.v === 'union') { if (base || struct) this.err('타입 지정이 중복되었습니다.'); struct = this.parseStructSpec(); any = true; continue; }
        if (t.v === 'enum') { if (base || struct) this.err('타입 지정이 중복되었습니다.'); this.parseEnumSpec(); seenInt = true; any = true; continue; }
        break;
      }
      if (t.t === 'id' && !base && !struct && !typedefName && !seenInt && !short && !longs && !sign && this.isTypedefName(t.v)) {
        // typedef 이름 — 단, 뒤에 선언자가 없는 경우(예: 변수 이름으로 쓰인 경우)는 제외
        typedefName = this.lookupTypedef(t.v); this.next(); any = true; continue;
      }
      break;
    }
    if (!any) return null;
    let type;
    if (struct) type = struct;
    else if (typedefName) type = typedefName;
    else if (base === 'void') type = TY.void;
    else if (base === 'char') type = sign === 'unsigned' ? TY.uchar : (sign === 'signed' ? TY.schar : TY.char);
    else if (base === '_Bool') type = TY.bool;
    else if (base === 'float') type = TY.float;
    else if (base === 'double') type = TY.double;
    else if (short) type = sign === 'unsigned' ? TY.ushort : TY.short;
    else if (longs >= 2) type = sign === 'unsigned' ? TY.ullong : TY.llong;
    else if (longs === 1) type = sign === 'unsigned' ? TY.ulong : TY.long;
    else if (seenInt || sign) type = sign === 'unsigned' ? TY.uint : TY.int;
    else {
      // 저장 클래스만 있고 타입이 없으면 int (암묵적)
      type = TY.int;
      if (!storage && !isTypedef && !isConst) return null;
    }
    return { type, storage, isTypedef, isConst, line: t0.line };
  }

  parseStructSpec() {
    const kw = this.next(); // struct | union
    const isUnion = kw.v === 'union';
    let tag = null;
    if (this.peek().t === 'id') tag = this.next().v;
    let st = null;
    if (tag) {
      st = this.structs.get((isUnion ? 'u:' : 's:') + tag);
      if (!st) { st = { k: 'struct', tag, union: isUnion, fields: [], size: 0, align: 1, complete: false }; this.structs.set((isUnion ? 'u:' : 's:') + tag, st); }
    } else {
      st = { k: 'struct', tag: null, union: isUnion, fields: [], size: 0, align: 1, complete: false, anonId: ++this.anonCount };
    }
    if (this.accept('{')) {
      if (st.complete) this.err(`${isUnion ? 'union' : 'struct'} ${tag} 가 두 번 정의되었습니다.`, kw);
      const fields = [];
      let offset = 0, align = 1;
      while (!this.isOp('}')) {
        if (this.peek().t === 'eof') this.err('구조체 정의가 닫히지 않았습니다 (} 가 없습니다).', kw);
        const specs = this.parseDeclSpecs();
        if (!specs) this.err(`구조체 멤버의 타입을 알 수 없습니다: '${this.tokText(this.peek())}'`);
        if (this.isOp(';')) { this.next(); continue; } // 익명 구조체 등
        for (;;) {
          const d = this.parseDeclarator(specs.type, false);
          if (this.accept(':')) { this.parseCondExpr(); } // 비트필드 폭은 무시
          if (!d.name) this.err('구조체 멤버 이름이 필요합니다.');
          if (d.type.k === 'void') this.err(`구조체 멤버 '${d.name}' 의 타입이 void 입니다.`);
          if (d.type.k === 'struct' && !d.type.complete) this.err(`구조체 멤버 '${d.name}' 의 타입(${typeName(d.type)})이 아직 정의되지 않았습니다. 자기 자신을 가리키려면 포인터(*)로 선언해야 합니다.`);
          if (d.type.k === 'arr' && d.type.incomplete) this.err(`구조체 멤버 배열 '${d.name}' 의 크기가 필요합니다.`);
          const fa = d.type.align || 1;
          if (!isUnion) offset = Math.ceil(offset / fa) * fa;
          fields.push({ name: d.name, type: d.type, offset: isUnion ? 0 : offset });
          if (isUnion) offset = Math.max(offset, d.type.size); else offset += d.type.size;
          align = Math.max(align, fa);
          if (!this.accept(',')) break;
        }
        this.expect(';', '구조체 멤버 선언 끝');
      }
      this.expect('}');
      st.fields = fields; st.align = align; st.size = Math.max(1, Math.ceil(offset / align) * align); st.complete = true;
    } else if (!tag) this.err('struct/union 다음에 이름이나 { 가 필요합니다.', kw);
    return st;
  }

  parseEnumSpec() {
    this.next(); // enum
    if (this.peek().t === 'id') this.next();
    if (this.accept('{')) {
      let val = 0;
      while (!this.isOp('}')) {
        const nt = this.next();
        if (nt.t !== 'id') this.err('열거 상수 이름이 필요합니다.', nt);
        if (this.accept('=')) val = constEval(this.parseCondExpr(), this);
        this.enums.set(nt.v, val);
        val++;
        if (!this.accept(',')) break;
      }
      this.expect('}');
    }
    return TY.int;
  }

  // 선언자 파싱: 반환 {name, type}
  parseDeclarator(base, abstractOk) {
    const parts = this.parseDeclaratorParts(abstractOk);
    return { name: parts.name, type: parts.apply(base), nameTok: parts.nameTok };
  }
  parseDeclaratorParts(abstractOk) {
    let ptrs = 0;
    while (this.isOp('*')) { this.next(); ptrs++; while (this.isKw('const') || this.isKw('volatile') || this.isKw('restrict')) this.next(); }
    let inner = null, name = null, nameTok = null;
    const t = this.peek();
    if (t.t === 'op' && t.v === '(') {
      const n1 = this.peek(1);
      const nested = (n1.t === 'op' && (n1.v === '*' || n1.v === '(' || n1.v === '[')) || (n1.t === 'id' && !this.isTypedefName(n1.v));
      if (nested) { this.next(); inner = this.parseDeclaratorParts(abstractOk); this.expect(')'); }
    } else if (t.t === 'id') {
      name = t.v; nameTok = t; this.next();
    } else if (!abstractOk) {
      if (t.t === 'kw') this.err(`'${t.v}' 는 예약어이므로 이름으로 쓸 수 없습니다.`, t);
      this.err(`선언에서 이름이 필요합니다. ('${this.tokText(t)}' 근처)`, t);
    }
    const suffixes = [];
    for (;;) {
      if (this.isOp('[')) {
        this.next();
        let n = null;
        if (!this.isOp(']')) { const e = this.parseAssignExpr(); n = constEval(e, this); if (!(n >= 0)) this.err('배열 크기는 0 이상의 상수여야 합니다.'); }
        this.expect(']');
        suffixes.push({ arr: n });
      } else if (this.isOp('(')) {
        this.next();
        const params = [];
        let variadic = false, oldStyle = false;
        if (this.isOp(')')) { oldStyle = true; }
        else if (this.isKw('void') && this.isOp(')', 1)) { this.next(); }
        else {
          for (;;) {
            if (this.accept('...')) { variadic = true; break; }
            const specs = this.parseDeclSpecs();
            if (!specs) {
              const pt = this.peek();
              if (pt.t === 'id') this.err(`매개변수 '${pt.v}' 의 타입이 없습니다. (알 수 없는 타입 이름이면 typedef 선언을 확인하세요)`, pt);
              this.err(`매개변수 선언이 잘못되었습니다. ('${this.tokText(pt)}' 근처)`, pt);
            }
            const d = this.parseDeclarator(specs.type, true);
            let pty = d.type;
            if (pty.k === 'arr') pty = ptrTo(pty.of);
            if (pty.k === 'fn') pty = ptrTo(pty);
            params.push({ name: d.name, type: pty, line: specs.line });
            if (!this.accept(',')) break;
          }
        }
        this.expect(')', '매개변수 목록 끝');
        suffixes.push({ fn: params, variadic, oldStyle });
      } else break;
    }
    const apply = (base) => {
      let ty = base;
      for (let i = 0; i < ptrs; i++) ty = ptrTo(ty);
      for (let i = suffixes.length - 1; i >= 0; i--) {
        const s = suffixes[i];
        if ('arr' in s) {
          if (ty.k === 'void') this.err('void 형 배열은 만들 수 없습니다.', t);
          if (ty.k === 'fn') this.err('함수의 배열은 만들 수 없습니다.', t);
          ty = arrOf(ty, s.arr);
        } else {
          if (ty.k === 'arr') this.err('함수는 배열을 반환할 수 없습니다.', t);
          if (ty.k === 'fn') this.err('함수는 함수를 반환할 수 없습니다.', t);
          ty = fnType(ty, s.fn, s.variadic, s.oldStyle);
        }
      }
      if (inner) ty = inner.apply(ty);
      return ty;
    };
    if (inner) { name = inner.name; nameTok = inner.nameTok; }
    return { name, nameTok, apply };
  }

  parseExternalDecl() {
    const specs = this.parseDeclSpecs();
    if (!specs) {
      const t = this.peek();
      if (t.t === 'id') {
        if (this.isOp('(', 1)) this.err(`'${t.v}' 의 반환 타입이 없습니다. 함수 정의는 'int ${t.v}(...)' 처럼 타입으로 시작해야 합니다.`, t);
        this.err(`알 수 없는 타입 이름 '${t.v}' 입니다. 오타이거나 typedef/struct 선언이 빠졌는지 확인하세요.`, t);
      }
      if (t.t === 'op' && t.v === '}') this.err("짝이 맞지 않는 '}' 입니다. 중괄호 개수를 확인하세요.", t);
      this.err(`전역 범위에 올 수 없는 토큰 '${this.tokText(t)}' 입니다. (함수 밖에는 선언만 올 수 있습니다)`, t);
    }
    if (this.accept(';')) return null; // struct 정의 등
    const out = [];
    for (;;) {
      const d = this.parseDeclarator(specs.type, false);
      if (specs.isTypedef) {
        this.declareTypedef(d.name, d.type);
        if (!this.accept(',')) { this.expect(';', 'typedef 선언 끝'); break; }
        continue;
      }
      if (d.type.k === 'fn') {
        this.funcNames.add(d.name);
        if (this.isOp('{')) {
          if (out.length) this.err('함수 정의는 다른 선언과 함께 쓸 수 없습니다.');
          const body = this.parseFunctionBody(d);
          return { kind: 'func', name: d.name, type: d.type, body, line: d.nameTok.line, storage: specs.storage };
        }
        out.push({ kind: 'funcdecl', name: d.name, type: d.type, line: d.nameTok.line });
      } else {
        if (d.type.k === 'void') this.err(`변수 '${d.name}' 를 void 형으로 선언할 수 없습니다.`, d.nameTok);
        this.declareVarName(d.name);
        let init = null;
        if (this.accept('=')) init = this.parseInitializer();
        if (d.type.k === 'arr' && d.type.incomplete) {
          if (!init) this.err(`배열 '${d.name}' 의 크기를 알 수 없습니다.`, d.nameTok);
          d.type = completeArrayFromInit(d.type, init);
        }
        if (d.type.k === 'struct' && !d.type.complete) this.err(`'${d.name}' 의 타입 ${typeName(d.type)} 이 정의되지 않았습니다.`, d.nameTok);
        out.push({ kind: 'var', name: d.name, type: d.type, init, line: d.nameTok.line, storage: specs.storage, global: true });
      }
      if (!this.accept(',')) { this.expect(';', '선언 끝'); break; }
    }
    return out;
  }

  parseFunctionBody(d) {
    this.pushScope();
    for (const p of d.type.params) { if (p.name) this.declareVarName(p.name); else this.err(`함수 '${d.name}' 의 매개변수에 이름이 없습니다.`, d.nameTok); }
    const body = this.parseCompound(false);
    this.popScope();
    return body;
  }

  parseInitializer() {
    if (this.isOp('{')) {
      const t = this.next();
      const items = [];
      while (!this.isOp('}')) {
        if (this.isOp('.') || this.isOp('[')) this.err('지정 초기화자(designated initializer)는 지원하지 않습니다.');
        items.push(this.parseInitializer());
        if (!this.accept(',')) break;
      }
      this.expect('}', '초기화 목록 끝');
      return { kind: 'initlist', items, line: t.line };
    }
    return this.parseAssignExpr();
  }

  /* ---- 문장 ---- */
  parseCompound(newScope = true) {
    const t = this.expect('{');
    if (newScope) this.pushScope();
    const stmts = [];
    while (!this.isOp('}')) {
      if (this.peek().t === 'eof') this.err("'{' 에 대응하는 '}' 가 없습니다. 중괄호 개수를 확인하세요.", t);
      stmts.push(this.parseStmt());
    }
    this.expect('}');
    if (newScope) this.popScope();
    return { kind: 'block', stmts, line: t.line };
  }

  parseDeclStmt() {
    const specs = this.parseDeclSpecs();
    const decls = [];
    if (this.accept(';')) return { kind: 'decl', decls, line: specs.line };
    for (;;) {
      const d = this.parseDeclarator(specs.type, false);
      if (specs.isTypedef) { this.declareTypedef(d.name, d.type); }
      else if (d.type.k === 'fn') {
        if (this.isOp('{')) this.err(`함수 '${d.name}' 를 다른 함수 안에서 정의하려 했습니다. 바로 앞 함수의 닫는 중괄호 '}' 가 빠졌는지 확인하세요.`, d.nameTok);
        this.funcNames.add(d.name); decls.push({ kind: 'funcdecl', name: d.name, type: d.type, line: d.nameTok.line });
      }
      else {
        if (d.type.k === 'void') this.err(`변수 '${d.name}' 를 void 형으로 선언할 수 없습니다.`, d.nameTok);
        let init = null;
        if (this.accept('=')) init = this.parseInitializer();
        this.declareVarName(d.name);
        if (d.type.k === 'arr' && d.type.incomplete) {
          if (!init) this.err(`배열 '${d.name}' 의 크기를 알 수 없습니다.`, d.nameTok);
          d.type = completeArrayFromInit(d.type, init);
        }
        if (d.type.k === 'struct' && !d.type.complete) this.err(`'${d.name}' 의 타입 ${typeName(d.type)} 이 정의되지 않았습니다.`, d.nameTok);
        decls.push({ kind: 'var', name: d.name, type: d.type, init, line: d.nameTok.line, storage: specs.storage, isStatic: specs.storage === 'static' });
      }
      if (!this.accept(',')) break;
    }
    this.expect(';', '선언 끝');
    return { kind: 'decl', decls, line: specs.line };
  }

  parseStmt() {
    const t = this.peek();
    if (t.t === 'op') {
      if (t.v === '{') return this.parseCompound();
      if (t.v === ';') { this.next(); return { kind: 'empty', line: t.line }; }
    }
    if (t.t === 'kw') {
      switch (t.v) {
        case 'if': {
          this.next(); this.expect('(', 'if 조건');
          const cond = this.parseExpr(); this.expect(')', 'if 조건 끝');
          const then = this.parseStmt();
          let els = null;
          if (this.accept('else')) els = this.parseStmt();
          return { kind: 'if', cond, then, els, line: t.line };
        }
        case 'while': {
          this.next(); this.expect('(', 'while 조건');
          const cond = this.parseExpr(); this.expect(')', 'while 조건 끝');
          const body = this.parseStmt();
          return { kind: 'while', cond, body, line: t.line };
        }
        case 'do': {
          this.next();
          const body = this.parseStmt();
          this.expect('while', 'do-while');
          this.expect('('); const cond = this.parseExpr(); this.expect(')'); this.expect(';', 'do-while 끝');
          return { kind: 'dowhile', cond, body, line: t.line };
        }
        case 'for': {
          this.next(); this.expect('(', 'for');
          this.pushScope();
          let init = null, cond = null, step = null;
          if (!this.isOp(';')) {
            if (this.startsDecl()) init = this.parseDeclStmt();
            else { init = { kind: 'expr', expr: this.parseExpr(), line: t.line }; this.expect(';', 'for 초기식 끝'); }
          } else this.next();
          if (!this.isOp(';')) cond = this.parseExpr();
          this.expect(';', 'for 조건식 끝');
          if (!this.isOp(')')) step = this.parseExpr();
          this.expect(')', 'for 끝');
          const body = this.parseStmt();
          this.popScope();
          return { kind: 'for', init, cond, step, body, line: t.line };
        }
        case 'switch': {
          this.next(); this.expect('(');
          const expr = this.parseExpr(); this.expect(')');
          const body = this.parseStmt();
          return { kind: 'switch', expr, body, line: t.line };
        }
        case 'case': {
          this.next();
          const e = this.parseCondExpr();
          const v = constEval(e, this);
          this.expect(':', 'case 레이블');
          const stmt = this.isOp('}') ? { kind: 'empty', line: t.line } : this.parseStmt();
          return { kind: 'case', value: v, stmt, line: t.line };
        }
        case 'default': {
          this.next(); this.expect(':', 'default 레이블');
          const stmt = this.isOp('}') ? { kind: 'empty', line: t.line } : this.parseStmt();
          return { kind: 'default', stmt, line: t.line };
        }
        case 'break': this.next(); this.expect(';', 'break'); return { kind: 'break', line: t.line };
        case 'continue': this.next(); this.expect(';', 'continue'); return { kind: 'continue', line: t.line };
        case 'return': {
          this.next();
          let e = null;
          if (!this.isOp(';')) e = this.parseExpr();
          this.expect(';', 'return 문 끝');
          return { kind: 'return', expr: e, line: t.line };
        }
        case 'goto': this.err('goto 문은 이 채점 환경에서 지원하지 않습니다.', t);
        case 'else': this.err("짝이 맞지 않는 'else' 입니다. 앞의 if 문 중괄호나 세미콜론을 확인하세요.", t);
        case 'sizeof': break;
        default:
          if (TYPE_KW.has(t.v)) return this.parseDeclStmt();
      }
    }
    if (t.t === 'id' && this.isOp(':', 1)) {
      // 레이블 (goto 미지원이므로 레이블은 무시)
      this.next(); this.next();
      return this.parseStmt();
    }
    if (this.startsDecl()) return this.parseDeclStmt();
    const e = this.parseExpr();
    if (!this.isOp(';')) {
      const nt = this.peek();
      if (nt.t === 'id' && e.kind === 'ident' && this.isTypedefName(e.name) === false)
        this.err(`알 수 없는 타입 이름 '${e.name}' 입니다. 오타이거나 typedef 선언이 빠졌는지 확인하세요.`, t);
      if (nt.t === 'eof' || (nt.t === 'op' && nt.v === '}') || nt.line > t.line) {
        const lt = this.toks[this.i - 1];
        this.err(`문장 끝에 ';' 가 없습니다. (${lt.line}번째 줄 '${this.tokText(lt)}' 뒤)`, lt);
      }
      this.err(`예상치 못한 토큰 '${this.tokText(nt)}' 입니다. 연산자나 ';' 가 빠졌는지 확인하세요.`, nt);
    }
    this.next();
    return { kind: 'expr', expr: e, line: t.line };
  }

  /* ---- 수식 ---- */
  parseExpr() {
    let e = this.parseAssignExpr();
    while (this.isOp(',')) { const t = this.next(); const r = this.parseAssignExpr(); e = { kind: 'comma', l: e, r, line: t.line }; }
    return e;
  }
  parseAssignExpr() {
    const l = this.parseCondExpr();
    const t = this.peek();
    if (t.t === 'op' && ['=', '+=', '-=', '*=', '/=', '%=', '<<=', '>>=', '&=', '|=', '^='].includes(t.v)) {
      this.next();
      const r = this.parseAssignExpr();
      return { kind: 'assign', op: t.v, l, r, line: t.line };
    }
    return l;
  }
  parseCondExpr() {
    const c = this.parseBinary(0);
    if (this.isOp('?')) {
      const t = this.next();
      const a = this.parseExpr();
      this.expect(':', '조건 연산자 ?:');
      const b = this.parseCondExpr();
      return { kind: 'cond', c, a, b, line: t.line };
    }
    return c;
  }
  parseBinary(minPrec) {
    const PREC = { '||': 1, '&&': 2, '|': 3, '^': 4, '&': 5, '==': 6, '!=': 6, '<': 7, '>': 7, '<=': 7, '>=': 7, '<<': 8, '>>': 8, '+': 9, '-': 9, '*': 10, '/': 10, '%': 10 };
    let l = this.parseCast();
    for (;;) {
      const t = this.peek();
      if (t.t !== 'op' || !(t.v in PREC) || PREC[t.v] <= minPrec) break;
      this.next();
      const r = this.parseBinary(PREC[t.v]);
      l = { kind: 'binary', op: t.v, l, r, line: t.line };
    }
    return l;
  }
  parseCast() {
    if (this.isOp('(') && this.startsTypeNameAt(1)) {
      const t = this.next();
      const ty = this.parseTypeName();
      this.expect(')', '형변환');
      if (this.isOp('{')) this.err('복합 리터럴(compound literal)은 지원하지 않습니다.', t);
      const e = this.parseCast();
      return { kind: 'cast', type: ty, e, line: t.line };
    }
    return this.parseUnary();
  }
  startsTypeNameAt(o) {
    const t = this.peek(o);
    if (t.t === 'kw') return TYPE_KW.has(t.v) && !['static', 'extern', 'typedef', 'register', 'auto'].includes(t.v);
    if (t.t === 'id') {
      if (!this.isTypedefName(t.v)) return false;
      const n = this.peek(o + 1);
      return (n.t === 'op' && (n.v === ')' || n.v === '*' || n.v === '[' || n.v === '('));
    }
    return false;
  }
  parseTypeName() {
    const specs = this.parseDeclSpecs();
    if (!specs) this.err('타입 이름이 필요합니다.');
    const d = this.parseDeclarator(specs.type, true);
    if (d.name) this.err('형변환/sizeof 의 타입 이름에는 변수 이름이 올 수 없습니다.');
    return d.type;
  }
  parseUnary() {
    const t = this.peek();
    if (t.t === 'op') {
      if (t.v === '++' || t.v === '--') { this.next(); const e = this.parseUnary(); return { kind: 'preinc', op: t.v, e, line: t.line }; }
      if (t.v === '&' || t.v === '*' || t.v === '+' || t.v === '-' || t.v === '!' || t.v === '~') {
        this.next(); const e = this.parseCast();
        return { kind: 'unary', op: t.v, e, line: t.line };
      }
    }
    if (t.t === 'kw' && t.v === 'sizeof') {
      this.next();
      if (this.isOp('(') && this.startsTypeNameAt(1)) {
        this.next(); const ty = this.parseTypeName(); this.expect(')');
        return { kind: 'sizeof', type: ty, line: t.line };
      }
      const e = this.parseUnary();
      return { kind: 'sizeof', e, line: t.line };
    }
    return this.parsePostfix();
  }
  parsePostfix() {
    let e = this.parsePrimary();
    for (;;) {
      const t = this.peek();
      if (t.t !== 'op') break;
      if (t.v === '[') { this.next(); const idx = this.parseExpr(); this.expect(']', '배열 인덱스'); e = { kind: 'index', a: e, i: idx, line: t.line }; }
      else if (t.v === '(') {
        this.next();
        const args = [];
        if (!this.isOp(')')) { for (;;) { args.push(this.parseAssignExpr()); if (!this.accept(',')) break; } }
        this.expect(')', '함수 호출 인자 끝');
        e = { kind: 'call', f: e, args, line: t.line };
      }
      else if (t.v === '.' || t.v === '->') {
        this.next();
        const n = this.next();
        if (n.t !== 'id') this.err(`'${t.v}' 다음에는 멤버 이름이 와야 합니다.`, n);
        e = { kind: 'member', e, name: n.v, arrow: t.v === '->', line: t.line };
      }
      else if (t.v === '++' || t.v === '--') { this.next(); e = { kind: 'postinc', op: t.v, e, line: t.line }; }
      else break;
    }
    return e;
  }
  parsePrimary() {
    const t = this.next();
    switch (t.t) {
      case 'num': {
        let type;
        if (t.isFloat) type = /f/.test(t.suffix) ? TY.float : TY.double;
        else if (/ll/.test(t.suffix)) type = /u/.test(t.suffix) ? TY.ullong : TY.llong;
        else if (/u/.test(t.suffix)) type = TY.uint;
        else if (t.v > 2147483647) type = t.v > 4294967295 ? TY.llong : TY.uint;
        else type = TY.int;
        return { kind: 'num', v: t.v, type, line: t.line };
      }
      case 'chr': return { kind: 'num', v: t.v, type: TY.int, line: t.line };
      case 'str': {
        let bytes = t.v.slice();
        while (this.peek().t === 'str') bytes = bytes.concat(this.next().v); // 인접 문자열 결합
        const node = { kind: 'str', bytes, line: t.line, id: this.stringLits.length };
        this.stringLits.push(node);
        return node;
      }
      case 'id':
        if (this.enums.has(t.v)) return { kind: 'num', v: this.enums.get(t.v), type: TY.int, line: t.line };
        return { kind: 'ident', name: t.v, line: t.line, col: t.col };
      case 'op':
        if (t.v === '(') { const e = this.parseExpr(); this.expect(')', '괄호 수식'); return e; }
        if (t.v === ')') this.err("짝이 맞지 않는 ')' 입니다.", t);
        if (t.v === ';') this.err("수식이 필요한 자리에 ';' 가 왔습니다.", t);
        this.err(`수식이 필요한 자리에 '${t.v}' 가 왔습니다.`, t);
        break;
      case 'kw':
        if (TYPE_KW.has(t.v)) this.err(`수식이 필요한 자리에 타입 이름 '${t.v}' 가 왔습니다. 선언은 문장 처음에 와야 합니다.`, t);
        this.err(`수식이 필요한 자리에 예약어 '${t.v}' 가 왔습니다.`, t);
        break;
      case 'eof': this.err('파일이 예상보다 일찍 끝났습니다. 닫는 괄호나 중괄호가 빠졌는지 확인하세요.', t);
    }
    this.err('수식을 해석할 수 없습니다.', t);
  }
}

function completeArrayFromInit(type, init) {
  if (init.kind === 'initlist') return arrOf(type.of, init.items.length);
  if (init.kind === 'str' && type.of.k === 'int' && type.of.size === 1) return arrOf(type.of, init.bytes.length + 1);
  throw new CError('compile', '배열 초기화 형식이 잘못되었습니다.', init.line);
}

/* 상수식 평가 (배열 크기, case 레이블, enum 값) */
function constEval(e, parser) {
  const ev = (n) => {
    switch (n.kind) {
      case 'num': return n.v;
      case 'unary': {
        const v = ev(n.e);
        switch (n.op) { case '-': return -v; case '+': return v; case '!': return v ? 0 : 1; case '~': return ~v; }
        break;
      }
      case 'binary': {
        const a = ev(n.l), b = ev(n.r);
        switch (n.op) {
          case '+': return a + b; case '-': return a - b; case '*': return a * b;
          case '/': if (b === 0) throw new CError('compile', '상수식에서 0으로 나눴습니다.', n.line); return Math.trunc(a / b);
          case '%': if (b === 0) throw new CError('compile', '상수식에서 0으로 나눴습니다.', n.line); return a % b;
          case '<<': return a << b; case '>>': return a >> b; case '&': return a & b; case '|': return a | b; case '^': return a ^ b;
          case '==': return a === b ? 1 : 0; case '!=': return a !== b ? 1 : 0; case '<': return a < b ? 1 : 0; case '>': return a > b ? 1 : 0; case '<=': return a <= b ? 1 : 0; case '>=': return a >= b ? 1 : 0;
          case '&&': return (a && b) ? 1 : 0; case '||': return (a || b) ? 1 : 0;
        }
        break;
      }
      case 'cond': return ev(n.c) ? ev(n.a) : ev(n.b);
      case 'cast': return ev(n.e);
      case 'sizeof': return n.type ? n.type.size : sizeofExprStatic(n.e, parser);
      case 'ident': throw new CError('compile', `상수식에 변수 '${n.name}' 를 쓸 수 없습니다. (배열 크기·case 레이블은 상수여야 합니다)`, n.line);
    }
    throw new CError('compile', '상수식이 필요합니다.', n.line);
  };
  return ev(e);
}
function sizeofExprStatic(e, parser) {
  if (e.kind === 'num') return e.type.size;
  if (e.kind === 'str') return e.bytes.length + 1;
  throw new CError('compile', 'sizeof 의 피연산자를 상수식으로 계산할 수 없습니다. sizeof(타입) 형태를 사용하세요.', e.line);
}

if (typeof module !== 'undefined') module.exports = { CError, TY, ptrTo, arrOf, fnType, isInt, isFloat, isArith, isPtr, isScalar, typeName, sameType, preprocess, Parser, constEval };
