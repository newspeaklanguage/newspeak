/* Does "Evaluate Selection" run on EVERY client?
 *
 *   croquet-probes/run.sh evaluate-selection-probe.js
 *
 * It is a synchronized action: the click is published, and every client runs
 * evaluateResponse, which reads a selection and evaluates it. Until multiple
 * cursors (2026-09-21) every client happened to hold the same selection,
 * because a remote selection was applied as its own. Removing that -- which is
 * what multiple cursors IS -- broke this, and nothing in the probe suite
 * noticed except one assertion buried at the end of typing-test.
 *
 * The fix under test is the SELECTION OF RECORD: the range is published where a
 * command might be about to read it, stored by every client beside the shadow,
 * and read through selectedTextBeingAccepted. The open question this probe
 * exists to answer is WHEN it is published -- blur is the moment a real button
 * click passes through, but a synthetic click may not blur at all.
 *
 * So the probe runs the same evaluation twice:
 *
 *   phase 1  NO blur before the click  -- what typing-test does
 *   phase 2  an explicit blur first    -- what a real mouse click does
 *
 * Neither is the "expected" case on its own. Together they say whether the
 * mechanism works and whether blur is a sufficient trigger, which is exactly
 * the thing to know before deciding how often the selection must be published.
 */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'evsel' + Math.floor(Date.now() / 1000);
const PAGE = (process.env.NS_PAGE || 'croquetpsoup-test.html') + '?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
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
setTimeout(() => bail('overall deadline passed'), Number(process.env.DEADLINE_MS || 280000)).unref();
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-evs-'+tag+'-'+SESSION,'--no-first-run','--window-size=1400,1000','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
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
  // Without it a headless page has no focus and the blur in phase 2 fires nothing (see harness.js).
  await send('Emulation.setFocusEmulationEnabled', { enabled: true });
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
let fails = 0;
const ok = (name, pass, detail) => { if (!pass) fails++; console.log((pass ? '  PASS  ' : '  FAIL  ') + name + (detail ? '   ' + detail : '')); };

// The selection of record, as each client holds it.
const SEL = "(typeof nsShadowSels==='undefined')?'n/a':JSON.stringify(Array.from(nsShadowSels.entries()))";

async function evaluatePhase(A, B, slot, withBlur) {
  await A.ev(`window.${slot}=undefined`); await B.ev(`window.${slot}=undefined`);
  // A literal, not syncRandom: phase 1 may run on A alone, which advances A's
  // random sequence past B's, and phase 2 would then fail on the numbers even
  // though both clients evaluated.
  const expr = `platform js global at: '${slot}' put: 'ran-${slot}'`;
  await A.ev(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');cm.replaceSelection(${JSON.stringify(expr)}, null, '+input');return 'SET'})()`);
  await sleep(2500);
  await A.ev(`(function(){var cm=${CM};cm.execCommand('selectAll');return 'SEL'})()`);
  await sleep(800);
  if (withBlur) {
    // What a real mouse-down on a button does before the click lands. Counted,
    // because "the selection of record is empty" has two causes -- the publish
    // hook never ran, or it ran and the event did not come back -- and only a
    // counter on the hook itself tells them apart.
    console.log('    A cm.state.focused before blur: ' + await A.ev(`String(${CM}.state.focused)`));
    console.log('    A blur handlers registered: ' + await A.ev(`String((${CM}._handlers&&${CM}._handlers.blur||[]).length)`));
    const evBefore = await A.ev('String(theModel.newspeakEvents.length)');
    await A.ev(`(function(){window.__sel=0;var f=nsCurrentSelection;nsCurrentSelection=function(a,b){window.__sel++;return f(a,b)};return 1})()`);
    await A.ev(`(function(){var cm=${CM};cm.getInputField().blur();return 'BLUR'})()`);
    await sleep(1200);
    console.log('    A nsCurrentSelection calls after blur: ' + await A.ev('String(window.__sel)'));
    console.log('    A events ' + evBefore + ' -> ' + await A.ev('String(theModel.newspeakEvents.length)'));
  }
  console.log('    A selection of record: ' + await A.ev(SEL));
  console.log('    B selection of record: ' + await B.ev(SEL));
  await A.ev(click('Evaluate Selection'));
  await waitFor(A, `typeof window.${slot} === 'string'`, 20000);
  await waitFor(B, `typeof window.${slot} === 'string'`, 20000);
  return [await A.ev(`window.${slot}`), await B.ev(`window.${slot}`)];
}

async function main() {
  console.log(PAGE);
  const A = await browser(9497, 'A'); await boot(A);
  await A.ev(click('Workspaces'));
  if (!await waitFor(A, "document.body.innerText.includes('Evaluate')", 40000)) bail('A never reached the workspace');
  const B = await browser(9498, 'B'); await boot(B);
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000)) bail('B never followed A to the workspace');
  await sleep(3000);

  console.log('\n-- phase 1: click with NO preceding blur (what typing-test does) --');
  const [a1, b1] = await evaluatePhase(A, B, 'rnd1', false);
  console.log('    A=' + a1 + '  B=' + b1);
  const p1 = !!a1 && a1 === b1;
  console.log('    ' + (p1 ? 'both clients evaluated' : 'only the clicking client evaluated'));

  console.log('\n-- phase 2: an explicit blur first (what a real mouse click does) --');
  const [a2, b2] = await evaluatePhase(A, B, 'rnd2', true);
  console.log('    A=' + a2 + '  B=' + b2);
  ok('EVALUATE SELECTION RUNS ON BOTH CLIENTS (after blur)', !!a2 && a2 === b2, 'A=' + a2 + ' B=' + b2);

  // Phase 1 is reported, not asserted: it says whether blur is REQUIRED, which
  // is the design question, not whether the feature works.
  console.log('\n  => blur is ' + (p1 ? 'NOT required' : 'REQUIRED') + ' for the selection of record to be in place.');
  if (!p1) console.log('     A command that reaches an editor without a preceding blur would still read a stale selection.');

  const divs = [await A.ev('String(nsDivergences.length)'), await B.ev('String(nsDivergences.length)')];
  ok('NO DIVERGENCE REPORTED', divs[0] === '0' && divs[1] === '0', 'A=' + divs[0] + ' B=' + divs[1]);
  console.log('errors/warnings A/B: ' + A.log.length + ' / ' + B.log.length);
  console.log('==== ' + (fails ? fails + ' FAILED' : 'all passed') + ' ====');
  for (const b of live) { try { b.proc.kill(); } catch (e) {} }
  process.exit(fails ? 1 : 0);
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
