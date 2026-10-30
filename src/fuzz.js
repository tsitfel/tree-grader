// 차분 테스트: gcc 실행 결과 vs 인터프리터 결과
// 사용법: node fuzz.js <prog.c> <gcc-binary> <mode:bst|avl|avlins> <iterations> [seed]
const fs = require('fs');
const { execFileSync } = require('child_process');
const { compileAndRun } = require('./engine/cruntime.js');

const [,, cfile, bin, mode, itersS, seedS] = process.argv;
const src = fs.readFileSync(cfile, 'utf8');
let seed = parseInt(seedS || '12345', 10);
function rnd() { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 4294967296; }
function ri(n) { return Math.floor(rnd() * n); }

function genInput() {
  const n = 1 + ri(60);
  const maxKey = [20, 50, 100, 1000][ri(4)];
  const keys = new Set();
  const lines = [];
  for (let i = 0; i < n; i++) {
    const r = rnd();
    if (r < 0.45) { let k; do { k = 1 + ri(maxKey); } while (keys.has(k) && keys.size < maxKey); if (keys.has(k)) continue; keys.add(k); lines.push(`i ${k}`); }
    else if (r < 0.6) { const k = 1 + ri(maxKey); lines.push(`s ${k}`); }
    else if (r < 0.8 && mode !== 'avlins') { const arr = [...keys]; const k = (arr.length && rnd() < 0.7) ? arr[ri(arr.length)] : 1 + ri(maxKey); if (keys.has(k)) keys.delete(k); lines.push(`d ${k}`); }
    else lines.push('p');
  }
  lines.push('q');
  return lines.join('\n') + '\n';
}

let fails = 0, total = 0, maxSteps = 0, maxMs = 0;
const iters = parseInt(itersS || '100', 10);
for (let it = 0; it < iters; it++) {
  const input = genInput();
  let expected;
  try { expected = execFileSync(bin, { input, timeout: 5000 }).toString(); } catch (e) { expected = '<<gcc error: ' + (e.stdout || '').toString() + '>>'; }
  const t0 = Date.now();
  const r = compileAndRun(src, input, {});
  const dt = Date.now() - t0;
  maxSteps = Math.max(maxSteps, r.steps); maxMs = Math.max(maxMs, dt);
  total++;
  if (r.status !== 'ok' || r.stdout !== expected) {
    fails++;
    if (fails <= 3) {
      console.log('--- MISMATCH #' + fails);
      console.log('input:\n' + input);
      console.log('expected:\n' + expected);
      console.log('got (' + r.status + '):\n' + r.stdout);
      if (r.error) console.log('error:', r.error);
    }
  }
}
console.log(`${cfile}: ${total - fails}/${total} match, maxSteps=${maxSteps}, maxTime=${maxMs}ms`);
process.exit(fails ? 1 : 0);
