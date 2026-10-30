// 사용법: node run.js prog.c [input.txt]
const fs = require('fs');
const { compileAndRun } = require('./cruntime.js');
const src = fs.readFileSync(process.argv[2], 'utf8');
const input = process.argv[3] ? fs.readFileSync(process.argv[3], 'utf8') : '';
const t0 = Date.now();
const r = compileAndRun(src, input, {});
const dt = Date.now() - t0;
process.stdout.write(r.stdout);
if (r.status !== 'ok') console.error('[' + r.status + '] line ' + (r.error && r.error.line) + ': ' + (r.error && r.error.message));
if (r.stderr) console.error('[stderr] ' + r.stderr);
if (r.warnings.length) console.error('[warn] ' + r.warnings.join(' | '));
console.error(`[steps=${r.steps} time=${dt}ms exit=${r.exitCode}]`);
