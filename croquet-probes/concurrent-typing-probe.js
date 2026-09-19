/* Two clients type into ONE editor at the same time. The design
   (CROQUET_EDITOR_DIFF_SYNC_DESIGN_2026-09-18.md) promises CONVERGENCE, not
   intention preservation: every client's shadow takes every edit event in session
   order, and a client whose visible editor was ahead when a foreign event came in
   is brought back to the shadow once its own edits are all in.

     croquet-probes/run.sh concurrent-typing-probe.js [js]

   N (30 characters each)  CADENCE_MS (60)  NS_PAGE (croquetpsoup-test.html)

   A starts at the end of the first line and types 'a's, B at the end of the last
   line and types 'b's, with real key events, interleaved. Asserted: both visible
   editors end equal; every shadow is equal on both clients; the visible editor
   equals its shadow; no character is lost; no divergence is reported. Reported,
   not asserted: where the characters ended up (the sender's selection rides its
   edit events and is applied by a client that is not itself ahead, so one
   client's characters may land on the other's line). */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'concur' + Math.floor(Date.now() / 1000);
const JS = process.argv[2] === 'js';
const PAGE = JS ? 'CroquetJSIDE-TEST.html?sessionId='
                : (process.env.NS_PAGE || 'croquetpsoup-test.html') + '?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const N = Number(process.env.N || 30), CADENCE = Number(process.env.CADENCE_MS || 60);
const sleep = ms => new Promise(r => setTimeout(r, ms));
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
const live = [];
function bail(why) {
  console.log('BAIL: ' + why);
  for (const b of live) { console.log('  ' + b.tag + ' console tail: ' + b.log.slice(-6).join(' || ')); try { b.proc.kill(); } catch (e) {} }
  process.exit(1);
}
setTimeout(() => bail('overall deadline passed'), Number(process.env.DEADLINE_MS || 400000)).unref();
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-con-'+tag+'-'+SESSION,'--no-first-run','--window-size=1400,1000','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<300;i++){ try { const t=await getJson(port,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await sleep(300); }
  if (!page) { try { proc.kill(); } catch (e) {} bail('no page target on port ' + port); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'&&(m.params.type==='error'||m.params.type==='warning'))log.push('['+m.params.type+'] '+m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ').slice(0,200));
    if(m.method==='Runtime.exceptionThrown')log.push('[THROWN] '+((m.params.exceptionDetails.exception||{}).description||'').slice(0,300));}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); if (r&&r.exceptionDetails) return 'EVAL-THREW: '+((r.exceptionDetails.exception||{}).description||r.exceptionDetails.text); return r&&r.result&&r.result.value; };
  const b = { proc, ev, send, log, tag };
  live.push(b);
  return b;
}
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)===true) return true; await sleep(500); } return false; }
async function boot(b) {
  await b.send('Page.navigate',{url:URL});
  if (!await waitFor(b, "!!(document.body && document.body.innerText.includes('Workspaces'))", 150000)) bail(b.tag + ' never showed the home page');
  console.log(b.tag + ' booted'); await sleep(4000);
}
async function typeChars(b, ch, n) {
  for (let i = 0; i < n; i++) {
    const t0 = Date.now();
    await b.send('Input.dispatchKeyEvent', { type: 'keyDown', text: ch, unmodifiedText: ch, key: ch });
    await b.send('Input.dispatchKeyEvent', { type: 'keyUp', key: ch });
    const rest = CADENCE - (Date.now() - t0); if (rest > 0) await sleep(rest);
  }
}
const SHADOWS = "(typeof nsShadows==='undefined')?'n/a':JSON.stringify(Array.from(nsShadows.entries()).map(function(e){return [e[0],e[1].getValue()]}))";
let fails = 0;
const ok = (name, pass, detail) => { if (!pass) fails++; console.log((pass ? '  PASS  ' : '  FAIL  ') + name + (detail ? '   ' + detail : '')); };
async function main() {
  console.log('N=' + N + ' CADENCE_MS=' + CADENCE + '  ' + PAGE);
  const A = await browser(9493, 'A'); await boot(A);
  await A.ev(click('Workspaces'));
  if (!await waitFor(A, "document.body.innerText.includes('Evaluate')", 40000)) bail('A never reached the workspace');
  const B = await browser(9494, 'B'); await boot(B);
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000)) bail('B never followed A to the workspace');
  await sleep(3000);
  const START = 'first line:\\nmiddle line\\nlast line:';
  await A.ev(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');cm.replaceSelection("${START}",null,'+input');return 1})()`);
  if (!await waitFor(B, `${CM}.getValue()==="${START}"`, 30000)) bail('B never received the starting text');
  await sleep(1500);
  console.log('A cursor: ' + await A.ev(`(function(){var cm=${CM};cm.focus();cm.setCursor(0,11);return JSON.stringify(cm.getCursor())})()`));
  console.log('B cursor: ' + await B.ev(`(function(){var cm=${CM};cm.focus();cm.setCursor(2,10);return JSON.stringify(cm.getCursor())})()`));
  await sleep(500);
  await Promise.all([typeChars(A, 'a', N), typeChars(B, 'b', N)]);
  console.log('typed; settling...');
  let va, vb, stable = 0, t0 = Date.now();
  while (Date.now() - t0 < 90000 && stable < 6) {
    await sleep(1000);
    const na = await A.ev(`${CM}.getValue()`), nb = await B.ev(`${CM}.getValue()`);
    stable = (na === va && nb === vb && na === nb) ? stable + 1 : 0; va = na; vb = nb;
  }
  console.log('A: ' + JSON.stringify(va)); console.log('B: ' + JSON.stringify(vb));
  const count = (s, c) => (String(s).match(new RegExp(c, 'g')) || []).length - (START.match(new RegExp(c, 'g')) || []).length;
  ok('VISIBLE EDITORS CONVERGE', va === vb);
  ok('NO CHARACTER LOST', count(va, 'a') === N && count(va, 'b') === N, "a's=" + count(va, 'a') + " b's=" + count(va, 'b') + ' of ' + N + ' each');
  const sa = await A.ev(SHADOWS), sb = await B.ev(SHADOWS);
  if (sa === 'n/a') console.log('  (shadows are not reachable from the page on this platform)');
  else {
    ok('SHADOWS IDENTICAL ON BOTH CLIENTS', sa === sb, JSON.parse(sa).length + ' shadow(s)');
    ok('VISIBLE EDITOR == ITS SHADOW (A)', JSON.parse(sa).some(e => e[1] === va));
    ok('VISIBLE EDITOR == ITS SHADOW (B)', JSON.parse(sb).some(e => e[1] === vb));
  }
  const lines = String(va).split('\n');
  console.log('  placement (info): line 1 ' + JSON.stringify(lines[0]) + '  last line ' + JSON.stringify(lines[lines.length - 1]));
  const divs = [await A.ev('String(nsDivergences.length)'), await B.ev('String(nsDivergences.length)')];
  ok('NO DIVERGENCE REPORTED', divs[0] === '0' && divs[1] === '0', 'A=' + divs[0] + ' B=' + divs[1]);
  console.log('errors/warnings A/B: ' + A.log.length + ' / ' + B.log.length + (A.log.length + B.log.length ? '\n  ' + A.log.concat(B.log).slice(-6).join('\n  ') : ''));
  console.log('==== ' + (fails ? fails + ' FAILED' : 'all passed') + ' ====');
  for (const b of live) { try { b.proc.kill(); } catch (e) {} }
  process.exit(fails ? 1 : 0);
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
