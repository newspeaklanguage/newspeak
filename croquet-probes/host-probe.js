/* Synchronized host probe (platform host under Croquet - HostForCroquet).
   A and B live; A evaluates a workspace doIt requesting
   `platform host fetcher fetchText: 'hostprobe.txt'`. Assertions:
   - both clients' Newspeak promises fulfill with the file's content;
   - the network fetch of the probe file happened on EXACTLY ONE client
     (the reflector-elected initiator) - counted by wrapping window.fetch;
   - a late joiner C converges to the same content by replaying the
     recorded result, without fetching the file itself;
   - a second request for a missing file breaks both live clients'
     promises with a shared HTTP failure.
   Run: node host-probe.js [js] */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'hostprobe' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const COUNTER = "window.nsProbeFetches = 0; (function(){var of_ = window.fetch; window.fetch = function(u){ if (String(u).indexOf('hostprobe') >= 0) window.nsProbeFetches++; return of_.apply(this, arguments); };})();";
const OK_DOIT = "[:g | platform actors Promise when: (platform host fetcher fetchText: 'hostprobe.txt') fulfilled: [:t | g at: 'hostGot' put: t. nil] broken: [:m | g at: 'hostFail' put: m printString. nil]. 'HOST-REQ'] value: platform js global";
const BAD_DOIT = "[:g | platform actors Promise when: (platform host fetcher fetchText: 'no-such-hostprobe-404.txt') fulfilled: [:t | g at: 'badGot' put: t. nil] broken: [:m | g at: 'badFail' put: m printString. nil]. 'HOST-REQ2'] value: platform js global";
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-host-'+tag+'-'+SESSION,'--no-first-run','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(port,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  await send('Page.addScriptToEvaluateOnNewDocument',{source: COUNTER});
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  return { proc, ev, log, navigate: u => send('Page.navigate',{url:URL}) };
}
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)) return true; await new Promise(r=>setTimeout(r,1000)); } return false; }
async function boot(b) {
  await b.navigate(URL);
  await waitFor(b, "document.body && document.body.innerText.includes('Workspaces')", 240000);
  await new Promise(r=>setTimeout(r,4000));
}
async function evalIn(b, doit, doneFlag) {
  await b.ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(doit)});cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,2500));
  await b.ev(click('Evaluate Selection'));
  return waitFor(b, doneFlag, 30000);
}
const PASS = (label, ok, detail) => console.log(label+':', ok ? 'PASS' : 'FAIL', detail||'');
async function main() {
  const A = await browser(9493,'a'); await boot(A);
  await A.ev(click('Workspaces'));
  await waitFor(A, "document.body.innerText.includes('Evaluate')", 30000);
  const B = await browser(9494,'b'); await boot(B);
  await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000);
  await new Promise(r=>setTimeout(r,3000));

  console.log('--- coordinated host fetch ---');
  await evalIn(A, OK_DOIT, "typeof window.hostGot === 'string' || typeof window.hostFail === 'string'");
  await waitFor(B, "typeof window.hostGot === 'string' || typeof window.hostFail === 'string'", 30000);
  const gotA = await A.ev('window.hostGot'), gotB = await B.ev('window.hostGot');
  const want = 'HOST-PROBE-CONTENT-tulips-42\n';
  PASS('BOTH PROMISES FULFILLED WITH THE BODY', gotA === want && gotB === want,
    JSON.stringify([gotA, gotB, await A.ev('window.hostFail'), await B.ev('window.hostFail')]));
  const fA = await A.ev('window.nsProbeFetches'), fB = await B.ev('window.nsProbeFetches');
  PASS('EXACTLY ONE CLIENT FETCHED (election)', fA + fB === 1, 'A:'+fA+' B:'+fB);

  console.log('--- late joiner ---');
  const total = await A.ev('theModel.newspeakEvents.length');
  const C = await browser(9495,'c'); await C.navigate(URL);
  const caught = await waitFor(C, 'window.lastProcessedEvent >= '+total, 240000);
  await new Promise(r=>setTimeout(r,4000));
  PASS('C CATCH-UP', caught, (await C.ev('lastProcessedEvent'))+' of '+(await C.ev('theModel.newspeakEvents.length')));
  PASS('C GOT THE BODY FROM THE RECORDED RESULT', (await C.ev('window.hostGot')) === want, JSON.stringify(await C.ev('window.hostGot')));
  PASS('C DID NOT FETCH', (await C.ev('window.nsProbeFetches')) === 0, ''+(await C.ev('window.nsProbeFetches')));
  PASS('C ORPHAN-FREE REPLAY', C.log.filter(l=>l.includes('no subscriber')).length === 0, '');

  console.log('--- shared failure ---');
  await evalIn(A, BAD_DOIT, "typeof window.badGot === 'string' || typeof window.badFail === 'string'");
  await waitFor(B, "typeof window.badGot === 'string' || typeof window.badFail === 'string'", 30000);
  const failA = await A.ev('window.badFail'), failB = await B.ev('window.badFail');
  PASS('MISSING FILE BREAKS BOTH PROMISES ALIKE', typeof failA === 'string' && failA === failB, JSON.stringify([failA, failB]));
  const errs = [A,B,C].map(b=>b.log.filter(l=>l.startsWith('[error]')).length);
  console.log('errors A/B/C:', errs.join('/'));
  console.log('--- A errors ---'); console.log(A.log.filter(l=>l.startsWith('[error]')||l.startsWith('[warning]')).slice(0,4).join('\n'));
  console.log('--- A console tail ---'); console.log(A.log.slice(-8).join('\n'));
  A.proc.kill(); B.proc.kill(); C.proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
