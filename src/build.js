// 단일 HTML 빌드: 템플릿 + 엔진 소스 + 테스트 데이터 → ../index.html (GitHub Pages 용 완성 문서)
//                                                → tree-grader.html (Claude 아티팩트 용 본문만)
const fs = require('fs');
const path = require('path');
const here = __dirname;
const engine = [fs.readFileSync(path.join(here, 'engine/cfront.js'), 'utf8'), fs.readFileSync(path.join(here, 'engine/cruntime.js'), 'utf8')]
  .map(s => s.replace(/^'use strict';\s*$/m, '').replace(/if \(typeof module !== 'undefined'\) module\.exports = \{[^}]*\};\s*/g, ''))
  .join('\n');
if (engine.includes('</script')) throw new Error('engine source contains </script');
const tests = fs.readFileSync(path.join(here, 'tests.json'), 'utf8');
let body = fs.readFileSync(path.join(here, 'template.html'), 'utf8');
body = body.replace('/*__ENGINE__*/', () => engine).replace('/*__TESTS__*/', () => tests);
fs.writeFileSync(path.join(here, 'tree-grader.html'), body);
const full = `<!doctype html>\n<html lang="ko">\n<head>\n<meta charset="utf-8">\n<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n<style>:root{color-scheme:light}body{margin:0}[hidden]{display:none!important}</style>\n</head>\n<body>\n${body}\n</body>\n</html>\n`;
fs.writeFileSync(path.join(here, '..', 'index.html'), full);
console.log('built index.html', (full.length / 1024).toFixed(0) + 'KB');
