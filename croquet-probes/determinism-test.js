/* Determinism suite - reconstruction of the reboot-lost
   croquet-{random,transclusion,timer}-test.js trio in one probe, per
   CROQUET_DETERMINISM_DESIGN_2026-08-23.md.

   Phases (A and B live; C late-joins BEFORE the timer phase so no orphan
   tick events sit in its replay path):
   1. RANDOM   - one synced eval draws syncRandom three times; the streams
                 must agree across A, B, and later across C's replay.
   2. COORDFETCH - one synced eval calls coordinatedFetch: with a fetcher
                 producing known bytes under key 'probe:cf1'. Election: the
                 fetcher runs on EXACTLY ONE of A/B; both receive the bytes.
   3. LATE JOIN - C replays: same random triple, bytes delivered from the
                 recorded loaded event, its own fetcher NOT run, zero
                 'no subscriber' skips.
   4. TIMER    - model-driven countdown: start {interval 400, count 3} =>
                 exactly ticks [2,1,0] recorded, identically on A and B;
                 a repeat start of the completed timer answers ONE recorded
                 0-tick and does not restart the countdown.
   Run: node determinism-test.js [js] */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'determ' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const RANDOM_DOIT = "[:g | g at: 'r1' put: platform hopscotch syncRandom printString. g at: 'r2' put: platform hopscotch syncRandom printString. g at: 'r3' put: platform hopscotch syncRandom printString. 'DREW'] value: platform js global";
/* The byte plumbing goes through pre-installed JS helpers (see browser())
   rather than TextEncoder/`at: #buffer` from Newspeak: on NS2JS, `at:` sent
   to a TypedArray dispatches to the NATIVE ES2022 `.at(index)` method - which
   coerces #buffer to NaN and answers undefined - instead of psoup's
   property-access semantics. A real platform-parity divergence, found by this
   suite 2026-09-03; it bites any alien with a native `at` (TypedArrays,
   Arrays, strings). */
const CF_DOIT = "[:g | platform hopscotch coordinatedFetch: 'probe:cf1' via: [:ok :fail | g at: 'fetcherRan' put: 'YES'. ok value: g nsProbeBytes. nil] ifSuccess: [:bytes | g at: 'cfGot' put: (g nsProbeDecode: bytes). nil] ifFailure: [:m | g at: 'cfFail' put: m printString. nil]. 'CF-REQUESTED'] value: platform js global";
const HELPERS = "window.nsProbeBytes = function(){ return new TextEncoder().encode('CF-PROBE-BYTES').buffer }; window.nsProbeDecode = function(b){ return new TextDecoder().decode(b) };";
const TICKS = "theModel.newspeakEvents.filter(e=>e.scope==='nstimer_'&&e.eventSpec==='model_timer_tick'&&e.fid==='/tprobe').map(e=>e.data).join(',')";
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-det-'+tag+'-'+SESSION,'--no-first-run','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(port,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  await send('Page.addScriptToEvaluateOnNewDocument',{source: HELPERS});
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  return { proc, ev, log, navigate: u => send('Page.navigate',{url:u}) };
}
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
const LASTCM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)) return true; await new Promise(r=>setTimeout(r,1000)); } return false; }
async function boot(b) {
  await b.navigate(URL);
  await waitFor(b, "document.body && document.body.innerText.includes('Workspaces')", 240000);
  await new Promise(r=>setTimeout(r,4000));
}
async function evalIn(b, doit, doneFlag) {
  await b.ev(`(function(){var cm=${LASTCM};cm.focus();cm.setValue(${JSON.stringify(doit)});cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,2500));
  await b.ev(click('Evaluate Selection'));
  return waitFor(b, doneFlag, 30000);
}
const PASS = (label, ok, detail) => console.log(label+':', ok ? 'PASS' : 'FAIL', detail||'');
async function main() {
  const A = await browser(9481,'a'); await boot(A);
  await A.ev(click('Workspaces'));
  await waitFor(A, "document.body.innerText.includes('Evaluate')", 30000);
  const B = await browser(9482,'b'); await boot(B);
  await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000);
  await new Promise(r=>setTimeout(r,3000));

  console.log('--- phase 1: syncRandom ---');
  await evalIn(A, RANDOM_DOIT, "typeof window.r3 === 'string'");
  await waitFor(B, "typeof window.r3 === 'string'", 20000);
  const triple = async b => JSON.stringify([await b.ev('window.r1'), await b.ev('window.r2'), await b.ev('window.r3')]);
  const tA = await triple(A), tB = await triple(B);
  PASS('RANDOM STREAMS AGREE (A==B)', tA === tB && tA.indexOf('null') < 0, tA === tB ? tA.slice(0,40)+'...' : tA+' vs '+tB);

  console.log('--- phase 2: coordinatedFetch election ---');
  await evalIn(A, CF_DOIT, "typeof window.cfGot === 'string' || typeof window.cfFail === 'string'");
  await waitFor(B, "typeof window.cfGot === 'string' || typeof window.cfFail === 'string'", 30000);
  const gotA = await A.ev('window.cfGot'), gotB = await B.ev('window.cfGot');
  const ranA = await A.ev('window.fetcherRan'), ranB = await B.ev('window.fetcherRan');
  PASS('BOTH CLIENTS GOT THE BYTES', gotA === 'CF-PROBE-BYTES' && gotB === 'CF-PROBE-BYTES', JSON.stringify([gotA,gotB,await A.ev('window.cfFail'),await B.ev('window.cfFail')]));
  PASS('FETCHER RAN ON EXACTLY ONE CLIENT', (ranA==='YES') !== (ranB==='YES'), 'A:'+ranA+' B:'+ranB);
  if (gotA !== 'CF-PROBE-BYTES' || gotB !== 'CF-PROBE-BYTES') {
    console.log('  cf events recorded:', await A.ev("JSON.stringify(theModel.newspeakEvents.filter(e=>e.scope&&String(e.scope).indexOf('nscoordfetch')>=0).map(e=>e.eventSpec+':'+e.fid)) "));
    console.log('  A console tail:', A.log.slice(-6).join(' || '));
    console.log('  B console tail:', B.log.slice(-6).join(' || '));
  }

  console.log('--- phase 3: late joiner ---');
  const total = await A.ev('theModel.newspeakEvents.length');
  const C = await browser(9483,'c');
  await C.navigate(URL);
  const caught = await waitFor(C, 'window.lastProcessedEvent >= '+total, 240000);
  await new Promise(r=>setTimeout(r,4000));
  const tC = await triple(C);
  PASS('C CATCH-UP', caught, (await C.ev('lastProcessedEvent'))+' of '+(await C.ev('theModel.newspeakEvents.length')));
  PASS('C RANDOM STREAM MATCHES', tC === tA, tC === tA ? '' : tC+' vs '+tA);
  PASS('C GOT BYTES WITHOUT FETCHING', (await C.ev('window.cfGot')) === 'CF-PROBE-BYTES' && (await C.ev('window.fetcherRan')) == null, 'cfGot:'+(await C.ev('window.cfGot'))+' fetcherRan:'+(await C.ev('window.fetcherRan')));
  PASS('C ORPHAN-FREE REPLAY', C.log.filter(l=>l.includes('no subscriber')).length === 0, '');

  console.log('--- phase 4: model-driven timer ---');
  await A.ev(`nsPublish('nstimer_','timer_start',{fid:'/tprobe',data:{interval:400,count:3}}); 'PUB'`);
  await new Promise(r=>setTimeout(r,3500));
  const ticksA = await A.ev(TICKS), ticksB = await B.ev(TICKS), ticksC = await C.ev(TICKS);
  PASS('TICKS RECORDED [2,1,0]', ticksA === '2,1,0', JSON.stringify(ticksA));
  PASS('TICKS IDENTICAL ON ALL CLIENTS', ticksA === ticksB && ticksB === ticksC, JSON.stringify([ticksA,ticksB,ticksC]));
  await B.ev(`nsPublish('nstimer_','timer_start',{fid:'/tprobe',data:{interval:400,count:3}}); 'PUB'`);
  await new Promise(r=>setTimeout(r,2500));
  const after = await A.ev(TICKS);
  PASS('COMPLETED TIMER IS IDEMPOTENT (one 0-tick, no restart)', after === '2,1,0,0', JSON.stringify(after));
  const errs = [A,B,C].map(b=>b.log.filter(l=>l.startsWith('[error]')).length);
  console.log('errors A/B/C:', errs.join('/'));
  A.proc.kill(); B.proc.kill(); C.proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
