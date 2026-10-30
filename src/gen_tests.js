// 테스트케이스 생성기: 정답 코드(gcc)로 기대 출력을 만들고, 추적 바이너리로 유형을 분류한다.
// 출력: tests.json  { p1:[...], p2:[...], p3:[...] }
const fs = require('fs');
const { execFileSync } = require('child_process');

const REF = { p1: './ref7_1', p2: './ref7_2', p3: './ref7_3' };
const TRACE = { p1: './tests/ref7_1_trace', p2: './tests/ref7_2_trace', p3: './tests/ref7_3_trace' };

function run(bin, input) { return execFileSync(bin, { input, timeout: 5000 }).toString(); }
function trace(bin, input) {
  const r = require('child_process').spawnSync(bin, { input, timeout: 5000 });
  return r.stderr.toString().split('\n').filter(Boolean);
}
let seed = 20261030;
function rnd() { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 4294967296; }
function ri(n) { return Math.floor(rnd() * n); }
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = ri(i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; }
function pick(a) { return a[ri(a.length)]; }
function cmds(list) { return list.join('\n') + '\n'; }

// 삭제 추적 파싱: "D30:ROOT C2 R1n TIE R2r" -> {key, root, case2, rots:[{cs,root}], tie}
function parseDel(line) {
  const m = /^D(\d+):(.*)$/.exec(line); if (!m) return null;
  const toks = m[2].trim().split(/\s+/).filter(Boolean);
  const d = { key: +m[1], root: toks.includes('ROOT'), case2: toks.includes('C2'), case1: toks.includes('C1'), tie: toks.includes('TIE'), rots: [] };
  for (const t of toks) { const r = /^R([1-4])([rn])$/.exec(t); if (r) d.rots.push({ cs: +r[1], atRoot: r[2] === 'r', single: r[1] === '1' || r[1] === '2' }); }
  return d;
}
function parseIns(line) {
  const m = /^I(\d+):(.*)$/.exec(line); if (!m) return null;
  const toks = m[2].trim().split(/\s+/).filter(Boolean);
  const d = { key: +m[1], rots: [] };
  for (const t of toks) { const r = /^R([1-4])([rn])$/.exec(t); if (r) d.rots.push({ cs: +r[1], atRoot: r[2] === 'r', single: r[1] === '1' || r[1] === '2' }); }
  return d;
}

const out = { p1: [], p2: [], p3: [] };
function add(p, t) {
  t.input = cmds(t.cmds); delete t.cmds;
  t.expected = run(REF[p], t.input);
  t.id = p + '-' + (out[p].length + 1);
  out[p].push(t);
}

// 임의 키 집합
function keys(n, maxKey) { const s = new Set(); while (s.size < n) s.add(1 + ri(maxKey)); return shuffle([...s]); }

/* ================= 문제 1: 이진탐색트리 ================= */
const H1 = {
  insert: 'insertItem: treeSearch(root, k)로 키가 들어갈 외부노드 w를 찾아 w에 키를 저장하고 expandExternal(w)로 w의 두 자식(외부노드)을 만들어야 합니다. 비교 방향은 k < key(v) → 왼쪽, k > key(v) → 오른쪽입니다. 전위순회(p)는 루트 → 왼쪽 부트리 → 오른쪽 부트리 순서로 각 키 앞에 공백 하나를 붙여 한 줄에 출력하고 줄바꿈합니다.',
  search: 'findElement/treeSearch: 탐색이 외부노드에 도달하면 키가 없는 것이므로 X를 출력합니다. 외부노드 판별(isExternal: left와 right가 모두 NULL)과 비교 방향(k < key → 왼쪽)을 확인하세요. 탐색은 트리를 바꾸지 않아야 합니다.',
  del1: 'removeElement (case 1): 삭제할 노드 w의 자식 z 중 하나라도 외부노드이면 reduceExternal(z)로 w와 z를 함께 제거하고, z의 형제(w의 다른 자식)가 w 자리를 계승합니다. 이때 w의 부모 g의 left/right 중 w가 있던 쪽을 형제로 바꾸고, 형제의 parent도 g로 갱신해야 합니다. 삭제된 키를 출력합니다.',
  del2: 'removeElement (case 2): w의 두 자식이 모두 내부노드이면 중위순회 후계자 y = inOrderSucc(w)(오른쪽 자식에서 왼쪽 자식만 끝까지 따라간 내부노드)의 키를 w에 복사하고, y의 왼쪽 외부노드 z에 대해 reduceExternal(z)를 수행합니다. 후계자 대신 선행자(왼쪽 부트리의 최댓값)를 쓰면 트리 모양이 달라져 전위순회 결과가 틀립니다.',
  delroot: '루트 삭제: 삭제되는 노드가 루트이면(부모 g가 NULL) 전역 root 포인터를 계승 노드로 바꾸고 그 노드의 parent를 NULL로 만들어야 합니다. 모든 노드가 삭제되면 외부노드 하나만 남은 빈 트리가 되어 p는 빈 줄을 출력하고, 이후 삽입이 다시 정상 동작해야 합니다.',
  delmiss: '없는 키 삭제: treeSearch 결과가 외부노드이면 트리를 바꾸지 않고 X를 출력해야 합니다. 삭제 후에는 그 키의 탐색(s)이 X가 되어야 하며 다른 키는 그대로 찾아져야 합니다.',
  mixed: '여러 명령이 섞인 긴 입력입니다. 앞의 유형별 테스트가 모두 통과했다면, 많은 노드가 있을 때 포인터(parent/left/right) 갱신이 빠진 경우나 free 한 노드를 다시 사용하는 경우를 의심해 보세요.',
};
add('p1', { cat: '예시', title: '문제지 입출력 예시 1', weight: 6, hint: H1.insert + ' ' + H1.search,
  cmds: ['i 3', 'i 2', 'i 7', 's 4', 'i 6', 'p', 'i 5', 's 6', 'q'] });
add('p1', { cat: '예시', title: '문제지 입출력 예시 2', weight: 6, hint: H1.del1 + ' ' + H1.del2,
  cmds: ['i 9', 'i 2', 'i 15', 'i 1', 'i 7', 'i 11', 'i 5', 'i 8', 'i 3', 'i 4', 'p', 'd 2', 'd 13', 'p', 'q'] });
add('p1', { cat: '삽입·전위순회', title: '삽입 7개 후 전위순회', weight: 6, hint: H1.insert,
  cmds: ['i 50', 'i 30', 'i 70', 'i 20', 'i 40', 'i 60', 'i 80', 'p', 'q'] });
add('p1', { cat: '삽입·전위순회', title: '오름차순 삽입(한쪽으로 치우친 트리)', weight: 5, hint: H1.insert,
  cmds: ['i 1', 'i 2', 'i 3', 'i 4', 'i 5', 'i 6', 'p', 'i 0', 'p', 'q'] });
{ const k = keys(25, 500); add('p1', { cat: '삽입·전위순회', title: '임의 순서 25개 삽입', weight: 5, hint: H1.insert, cmds: [...k.map(x => 'i ' + x), 'p', 'q'] }); }
add('p1', { cat: '탐색', title: '있는 키·없는 키 탐색', weight: 6, hint: H1.search,
  cmds: ['i 40', 'i 20', 'i 60', 'i 10', 'i 30', 'i 50', 'i 70', 's 40', 's 10', 's 70', 's 35', 's 5', 's 100', 's 30', 'p', 'q'] });
add('p1', { cat: '탐색', title: '빈 트리와 노드 1개 트리에서 탐색', weight: 4, hint: H1.search + ' 빈 트리(외부노드 1개)에서도 탐색은 X를 출력하고 오류 없이 동작해야 합니다.',
  cmds: ['s 5', 'i 5', 's 5', 's 4', 's 6', 'p', 'q'] });
add('p1', { cat: '삭제(case 1)', title: '잎 노드 삭제', weight: 6, hint: H1.del1,
  cmds: ['i 50', 'i 30', 'i 70', 'i 20', 'i 40', 'i 60', 'i 80', 'd 20', 'p', 'd 80', 'p', 'd 40', 'd 60', 'p', 'q'] });
add('p1', { cat: '삭제(case 1)', title: '자식이 하나뿐인 노드 삭제', weight: 6, hint: H1.del1,
  cmds: ['i 50', 'i 30', 'i 70', 'i 20', 'i 60', 'i 10', 'i 65', 'd 30', 'p', 'd 70', 'p', 'd 20', 'p', 'q'] });
add('p1', { cat: '삭제(case 2)', title: '두 자식이 모두 내부노드인 노드 삭제(후계자가 오른쪽 자식)', weight: 7, hint: H1.del2,
  cmds: ['i 50', 'i 30', 'i 70', 'i 20', 'i 40', 'i 60', 'i 80', 'd 30', 'p', 'd 70', 'p', 'q'] });
add('p1', { cat: '삭제(case 2)', title: '후계자가 깊은 곳에 있고 오른쪽 자식을 가진 경우', weight: 7, hint: H1.del2,
  cmds: ['i 50', 'i 20', 'i 80', 'i 10', 'i 30', 'i 60', 'i 90', 'i 55', 'i 70', 'i 57', 'd 50', 'p', 'd 20', 'p', 'd 80', 'p', 'q'] });
add('p1', { cat: '루트 삭제', title: '루트 삭제(두 자식) 후 삽입·탐색', weight: 6, hint: H1.delroot,
  cmds: ['i 10', 'i 5', 'i 15', 'i 12', 'd 10', 'p', 's 12', 'i 10', 'p', 'q'] });
add('p1', { cat: '루트 삭제', title: '모두 삭제해 빈 트리로 만든 뒤 다시 삽입', weight: 6, hint: H1.delroot,
  cmds: ['i 7', 'd 7', 'p', 'i 3', 'i 9', 'd 3', 'd 9', 'p', 's 3', 'i 5', 'i 4', 'i 6', 'p', 'd 5', 'p', 'q'] });
add('p1', { cat: '없는 키 삭제·삭제 후 탐색', title: '없는 키 삭제와 삭제 후 탐색', weight: 6, hint: H1.delmiss,
  cmds: ['i 10', 'i 5', 'i 15', 'd 7', 'd 20', 'p', 'd 5', 's 5', 's 10', 's 15', 'd 5', 'p', 'q'] });
for (let t = 0; t < 3; t++) {
  const maxKey = [100, 1000, 50][t];
  const n = [60, 90, 120][t];
  const cur = new Set(); const list = [];
  for (let i = 0; i < n; i++) {
    const r = rnd();
    if (r < 0.45 || cur.size < 3) { let k = 1 + ri(maxKey); if (cur.has(k)) continue; cur.add(k); list.push('i ' + k); }
    else if (r < 0.6) list.push('s ' + (1 + ri(maxKey)));
    else if (r < 0.85) { const arr = [...cur]; const k = rnd() < 0.75 ? arr[ri(arr.length)] : 1 + ri(maxKey); cur.delete(k); list.push('d ' + k); }
    else list.push('p');
  }
  list.push('p', 'q');
  add('p1', { cat: '종합', title: `삽입·탐색·삭제 혼합 ${n}개 명령 (${t + 1})`, weight: 6, hint: H1.mixed, cmds: list });
}

/* ================= 문제 2: AVL 삽입 ================= */
const H2 = {
  norot: '회전이 필요 없는 삽입입니다. 문제 1의 삽입·탐색·전위순회가 그대로 동작해야 합니다. 노드 구조체에 height를 추가했다면 expandExternal에서 외부노드 높이 0, 새 내부노드 높이 1로 초기화하세요.',
  single: '단일회전(LL/RR): 삽입 후 조상을 따라 올라가며 처음 불균형이 된 노드 z, z의 더 높은 자식 y, y의 더 높은 자식 x가 한 방향으로 늘어선 경우입니다. restructure에서 (a,b,c)는 x,y,z를 키 순서로 정렬한 것이고 b가 부트리의 새 루트가 됩니다. z가 루트이면 root를 b로 바꾸고 b->parent = NULL로 설정해야 합니다.',
  double: '이중회전(LR/RL): x가 y의 자식 중 y와 반대 방향에 있는 경우(예: z의 왼콼 자식 y, y의 오른쪽 자식 x)입니다. 이때 b = x가 부트리의 루트가 되고 a, c는 x의 자식이 됩니다. T0~T3(네 부트리)를 올바른 위치에 다시 연결하고 각 부트리의 parent도 갱신하세요.',
  nonroot: '루트가 아닌 위치의 회전: z의 부모 p가 있을 때, p->left 또는 p->right 중 z가 있던 쪽을 b로 바꾸고 b->parent = p로 설정해야 합니다. 이 연결을 빠뜨리면 회전한 부트리가 트리에서 떨어져 전위순회에서 사라집니다.',
  height: '높이 갱신: 회전 후 a와 c의 높이를 먼저 갱신(max(자식 높이)+1)하고 그 다음 b의 높이를 갱신해야 합니다. 또 삽입 위치에서 루트까지 올라가며 모든 조상의 높이를 갱신(updateHeight)해야 다음 삽입 때 불균형 판단이 정확합니다. 높이가 틀리면 나중의 회전이 잘못 일어나거나 빠집니다.',
  search: 'AVL 트리에서의 탐색은 이진탐색트리와 같습니다. 회전 후에도 키의 순서(중위순회 순서)가 유지되어야 하므로, 탐색이 틀렸다면 회전에서 부트리 연결이 잘못된 것일 수 있습니다.',
  mixed: '많은 삽입이 섞인 긴 입력입니다. 단일·이중회전, 루트/비루트 위치의 회전, 높이 갱신 중 어느 하나라도 틀리면 결과가 달라집니다. 유형별 테스트 결과를 먼저 확인하세요.',
};
add('p2', { cat: '예시', title: '문제지 입출력 예시', weight: 8, hint: H2.norot + ' ' + H2.search,
  cmds: ['i 44', 'i 17', 'i 78', 'i 32', 'i 50', 'i 88', 'i 48', 'i 62', 's 88', 'p', 'q'] });
add('p2', { cat: '회전 없는 삽입', title: '균형이 유지되는 삽입', weight: 8, hint: H2.norot,
  cmds: ['i 40', 'i 20', 'i 60', 'i 10', 'i 30', 'i 50', 'i 70', 'p', 's 30', 's 35', 'q'] });
add('p2', { cat: '단일회전', title: '오른쪽으로 치우친 삽입(RR) → 단일회전', weight: 8, hint: H2.single,
  cmds: ['i 10', 'i 20', 'i 30', 'p', 'q'] });
add('p2', { cat: '단일회전', title: '왼쪽으로 치우친 삽입(LL) → 단일회전', weight: 8, hint: H2.single,
  cmds: ['i 30', 'i 20', 'i 10', 'p', 's 20', 'q'] });
add('p2', { cat: '이중회전', title: 'RL 형태 → 이중회전', weight: 8, hint: H2.double,
  cmds: ['i 10', 'i 30', 'i 20', 'p', 'q'] });
add('p2', { cat: '이중회전', title: 'LR 형태 → 이중회전', weight: 8, hint: H2.double,
  cmds: ['i 30', 'i 10', 'i 20', 'p', 's 10', 'q'] });
// 비루트 회전: 추적으로 확인하며 선택
function findInsertSeq(pred, n, maxKey, tries = 5000) {
  for (let t = 0; t < tries; t++) {
    const k = keys(n, maxKey);
    const input = cmds([...k.map(x => 'i ' + x), 'p', 'q']);
    const tr = trace(TRACE.p2, input).map(parseIns).filter(Boolean);
    if (pred(tr)) return k;
  }
  throw new Error('no sequence found');
}
{
  const k = findInsertSeq(tr => { const rots = tr.flatMap(x => x.rots); return rots.length >= 2 && rots.some(r => !r.atRoot && r.single) && rots.every(r => r.single); }, 9, 99);
  add('p2', { cat: '비루트 위치 회전', title: '루트 아래에서의 단일회전(부모 연결 갱신)', weight: 8, hint: H2.nonroot + ' ' + H2.single, cmds: [...k.map(x => 'i ' + x), 'p', 'q'] });
}
{
  const k = findInsertSeq(tr => { const rots = tr.flatMap(x => x.rots); return rots.length >= 2 && rots.some(r => !r.atRoot && !r.single); }, 9, 99);
  add('p2', { cat: '비루트 위치 회전', title: '루트 아래에서의 이중회전(부모 연결 갱신)', weight: 8, hint: H2.nonroot + ' ' + H2.double, cmds: [...k.map(x => 'i ' + x), 'p', 's ' + k[3], 'q'] });
}
add('p2', { cat: '높이 갱신', title: '오름차순 1~20 삽입(연속 회전)', weight: 7, hint: H2.height,
  cmds: [...Array.from({ length: 20 }, (_, i) => 'i ' + (i + 1)), 'p', 'q'] });
add('p2', { cat: '높이 갱신', title: '내림차순 31~1 삽입(연속 회전)', weight: 7, hint: H2.height,
  cmds: [...Array.from({ length: 31 }, (_, i) => 'i ' + (31 - i)), 'p', 's 16', 's 32', 'q'] });
{ const k = keys(40, 999); add('p2', { cat: '높이 갱신', title: '임의 순서 40개 삽입', weight: 7, hint: H2.height + ' ' + H2.mixed, cmds: [...k.map(x => 'i ' + x), 'p', 's ' + k[7], 's ' + (1000), 'q'] }); }
for (let t = 0; t < 2; t++) {
  const n = [60, 100][t]; const maxKey = [200, 5000][t];
  const cur = new Set(); const list = [];
  for (let i = 0; i < n; i++) {
    const r = rnd();
    if (r < 0.65) { const k = 1 + ri(maxKey); if (cur.has(k)) continue; cur.add(k); list.push('i ' + k); }
    else if (r < 0.9) list.push('s ' + (rnd() < 0.5 && cur.size ? pick([...cur]) : 1 + ri(maxKey)));
    else list.push('p');
  }
  list.push('p', 'q');
  add('p2', { cat: '종합', title: `삽입·탐색 혼합 ${n}개 명령 (${t + 1})`, weight: 7.5, hint: H2.mixed, cmds: list });
}

/* ================= 문제 3: AVL 삭제 ================= */
const H3 = {
  ins: '삭제를 구현하기 전에 문제 2의 AVL 삽입이 정확해야 합니다. 삽입 관련 유형(단일·이중회전, 높이 갱신)을 먼저 확인하세요.',
  norot: '회전이 필요 없는 삭제입니다. 이진탐색트리의 삭제(reduceExternal, 중위 후계자)가 그대로 동작해야 하며, 삭제 후 reduceExternal로 사라진 노드의 부모(zs->parent)에서 시작해 루트까지 높이를 갱신해야 합니다.',
  single: '삭제 후 단일회전: 삭제로 한쪽 부트리가 낮아져 조상 z가 불균형이 되면, y = z의 더 높은 자식, x = y의 더 높은 자식으로 restructure(x)를 수행합니다. 삽입과 달리 삭제에서는 불균형 노드 z가 삭제 위치의 반대쪽에서 생기므로 y, x를 높이로 골라야 합니다.',
  tie: '동점(tie) 처리: y의 두 자식 높이가 같으면 x는 y와 같은 방향의 자식(z->left == y 이면 y->left, 아니면 y->right)으로 골라 단일회전을 해야 합니다. 이 규칙을 반대로 하면 이중회전이 되어 트리 모양이 달라집니다. (삭제에서만 생기는 경우입니다)',
  double: '삭제 후 이중회전: y의 두 자식 중 y와 반대 방향의 자식이 더 높으면 이중회전입니다. restructure 자체는 삽입 때와 같은 함수를 그대로 쓸 수 있습니다.',
  cascade: '연쇄 회전: 삭제에서는 한 번 회전한 뒤에도 그 위의 조상이 불균형일 수 있습니다. restructure가 돌려준 부트리 루트 b에서 다시 위로 올라가며(searchAndFixAfterRemoval(b) 재호출 또는 반복) 루트까지 높이 갱신과 균형 검사를 계속해야 합니다. 삽입처럼 한 번만 회전하고 멈추면 틀립니다.',
  case2: '두 자식이 모두 내부노드인 노드의 삭제: 중위 후계자 y의 키를 w에 복사하고 y의 왼쪽 외부노드 z에 reduceExternal(z) 한 뒤, 균형 수리는 (w가 아니라) 실제로 노드가 사라진 위치인 zs->parent에서 시작해야 합니다.',
  root: '루트 삭제: 루트가 삭제될 때 root 포인터 갱신과, 삭제 후 새 루트에서의 균형 수리를 확인하세요. 또 회전으로 루트가 바뀌는 경우(z == root) root = b, b->parent = NULL 처리를 확인하세요.',
  mixed: '삽입·삭제·탐색이 섞인 긴 입력입니다. 유형별 테스트(단일/이중/동점/연쇄 회전, case 2, 루트 삭제) 결과를 먼저 확인하고, 포인터 갱신 누락이나 free 한 노드 재사용을 의심해 보세요.',
};
add('p3', { cat: '예시', title: '문제지 입출력 예시', weight: 6, hint: H3.ins + ' ' + H3.norot,
  cmds: ['i 9', 'i 31', 'i 66', 'i 30', 'i 1', 's 30', 'i 24', 'p', 's 47', 'i 61', 'd 30', 'i 13', 'q'] });
add('p3', { cat: '삽입(문제 2)', title: 'AVL 삽입: 단일·이중회전', weight: 6, hint: H3.ins,
  cmds: ['i 10', 'i 20', 'i 30', 'p', 'i 25', 'i 28', 'p', 'i 5', 'i 3', 'p', 'q'] });
add('p3', { cat: '삭제(회전 없음)', title: '회전이 필요 없는 삭제', weight: 6, hint: H3.norot,
  cmds: ['i 40', 'i 20', 'i 60', 'i 10', 'i 30', 'i 50', 'i 70', 'd 10', 'p', 'd 70', 'p', 'd 20', 'p', 's 30', 's 20', 'q'] });

// 삭제 유형 탐색
function findDelSeq(pred, n, maxKey, nDel, tries = 20000) {
  for (let t = 0; t < tries; t++) {
    const k = keys(n, maxKey);
    const dels = shuffle(k.slice()).slice(0, nDel);
    const list = [...k.map(x => 'i ' + x)];
    for (const d of dels) list.push('d ' + d, 'p');
    list.push('q');
    const input = cmds(list);
    const tr = trace(TRACE.p3, input);
    const ins = tr.map(parseIns).filter(Boolean), del = tr.map(parseDel).filter(Boolean);
    if (pred(ins, del)) return { k, dels, list };
  }
  throw new Error('no sequence found for ' + pred.toString().slice(0, 80));
}
{ // 단일회전 (동점 아님), 1회
  const s = findDelSeq((ins, del) => del.length === 1 && del[0].rots.length === 1 && del[0].rots[0].single && !del[0].tie && del[0].case1, 8, 99, 1);
  add('p3', { cat: '삭제 후 단일회전', title: '잎 삭제 후 단일회전', weight: 7, hint: H3.single, cmds: s.list });
}
{ // 단일회전, 루트가 아닌 위치
  const s = findDelSeq((ins, del) => del.length === 2 && del.every(d => d.rots.length <= 1 && !d.tie) && del.some(d => d.rots.length === 1 && d.rots[0].single && !d.rots[0].atRoot), 12, 99, 2);
  add('p3', { cat: '삭제 후 단일회전', title: '루트 아래에서의 단일회전(두 번 삭제)', weight: 6, hint: H3.single, cmds: s.list });
}
{ // 동점(tie): 직접 구성 (z=50, y=30, y의 두 자식 20·40 높이 같음, 70 삭제)
  const list = ['i 50', 'i 30', 'i 70', 'i 20', 'i 40', 'd 70', 'p', 'q'];
  const tr = trace(TRACE.p3, cmds(list)).map(parseDel).filter(Boolean);
  if (!(tr.length === 1 && tr[0].tie)) throw new Error('tie case check failed');
  add('p3', { cat: '동점 처리(단일회전)', title: 'y의 두 자식 높이가 같은 경우 → 같은 방향 자식 선택', weight: 8, hint: H3.tie, cmds: list });
}
{
  const list = ['i 50', 'i 30', 'i 70', 'i 20', 'i 40', 'i 60', 'i 80', 'i 10', 'i 25', 'i 35', 'i 45', 'i 55', 'd 80', 'p', 'd 60', 'p', 'd 55', 'p', 's 45', 's 80', 'q'];
  const tr = trace(TRACE.p3, cmds(list)).map(parseDel).filter(Boolean);
  if (!(tr.filter(d => d.tie).length >= 1 && tr.some(d => d.rots.length === 1 && !d.rots[0].atRoot))) throw new Error('tie case 2 check failed: ' + JSON.stringify(tr));
  add('p3', { cat: '동점 처리(단일회전)', title: '비루트 단일회전과 루트 동점 처리를 포함한 세 번의 삭제', weight: 7, hint: H3.tie, cmds: list });
}
{ // 이중회전
  const s = findDelSeq((ins, del) => del.length === 1 && del[0].rots.length === 1 && !del[0].rots[0].single, 8, 99, 1);
  add('p3', { cat: '삭제 후 이중회전', title: '삭제 후 이중회전', weight: 7, hint: H3.double, cmds: s.list });
}
{
  const s = findDelSeq((ins, del) => del.length === 2 && del.some(d => d.rots.length === 1 && !d.rots[0].single && !d.rots[0].atRoot) && del.every(d => d.rots.length <= 1), 13, 999, 2);
  add('p3', { cat: '삭제 후 이중회전', title: '루트 아래에서의 이중회전(두 번 삭제)', weight: 6, hint: H3.double, cmds: s.list });
}
{ // 연쇄 회전 (한 삭제에 2회 이상)
  const s = findDelSeq((ins, del) => del.length === 1 && del[0].rots.length >= 2, 13, 99, 1, 60000);
  add('p3', { cat: '연쇄 회전', title: '한 번의 삭제로 두 번 이상 회전', weight: 8, hint: H3.cascade, cmds: s.list });
}
{ // case 2 + 회전
  const s = findDelSeq((ins, del) => del.length === 1 && del[0].case2 && del[0].rots.length >= 1, 9, 99, 1);
  add('p3', { cat: '두 자식 내부노드 삭제', title: '두 자식이 내부노드인 노드 삭제 후 회전', weight: 7, hint: H3.case2, cmds: s.list });
}
{
  const s = findDelSeq((ins, del) => del.length === 2 && del.every(d => d.case2), 12, 99, 2);
  add('p3', { cat: '두 자식 내부노드 삭제', title: '두 자식이 내부노드인 노드 두 번 삭제', weight: 6, hint: H3.case2, cmds: [...s.list.slice(0, -1), 's ' + s.dels[0], 's ' + s.k[0], 'q'] });
}
{ // 루트 삭제
  const s = findDelSeq((ins, del) => del.length === 1 && del[0].root, 7, 99, 1);
  add('p3', { cat: '루트 삭제', title: '루트 삭제', weight: 6, hint: H3.root, cmds: [...s.list.slice(0, -1), 'i ' + s.dels[0], 'p', 'q'] });
}
add('p3', { cat: '루트 삭제', title: '모두 삭제 후 재삽입', weight: 6, hint: H3.root,
  cmds: ['i 5', 'i 3', 'i 8', 'd 5', 'p', 'd 3', 'd 8', 'p', 's 3', 'i 1', 'i 2', 'i 3', 'p', 'd 2', 'p', 'q'] });
for (let t = 0; t < 2; t++) {
  const n = [80, 130][t]; const maxKey = [120, 3000][t];
  const cur = new Set(); const list = [];
  for (let i = 0; i < n; i++) {
    const r = rnd();
    if (r < 0.45 || cur.size < 3) { const k = 1 + ri(maxKey); if (cur.has(k)) continue; cur.add(k); list.push('i ' + k); }
    else if (r < 0.58) list.push('s ' + (rnd() < 0.5 && cur.size ? pick([...cur]) : 1 + ri(maxKey)));
    else if (r < 0.88) { const arr = [...cur]; const k = rnd() < 0.8 ? arr[ri(arr.length)] : 1 + ri(maxKey); cur.delete(k); list.push('d ' + k); }
    else list.push('p');
  }
  list.push('p', 'q');
  add('p3', { cat: '종합', title: `삽입·탐색·삭제 혼합 ${n}개 명령 (${t + 1})`, weight: 4, hint: H3.mixed, cmds: list });
}

// 가중치 합 확인
for (const p of ['p1', 'p2', 'p3']) {
  const w = out[p].reduce((s, t) => s + t.weight, 0);
  console.log(p, out[p].length, 'tests, weight sum =', w);
  for (const t of out[p]) console.log('  ', t.id, t.cat, '|', t.title, '| lines:', t.expected.split('\n').length - 1);
}
fs.writeFileSync('tests.json', JSON.stringify(out, null, 1));
