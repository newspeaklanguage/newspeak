/* Late-join-through-disposal probe (plan CROQUET_FRAGMENT_IDENTITY_PLAN §5).
   Browser A: home -> Workspaces (page swap DISPOSES the home tree), evaluate
   w1, history.back() (disposes the workspace tree, retiring its CM/button
   subscriptions), Workspaces again (fresh lineages), evaluate w2.
   Browser B then cold-joins the same session: its replay must re-drive the
   navigations, subscribing and RETIRING at the same event positions, with
   NO 'no subscriber' skips (each orphan would cost a 15s poll), and must
   converge to A's page and registry. */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'ljprobe' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const CENSUS = `(function(){var c={button:0,imagebutton:0,codemirror:0,hyperlink:0,other:0};
  Array.from(newspeakSubscriptions.keys()).forEach(function(k){
    if(k.indexOf('nsbutton_')===0)c.button++;
    else if(k.indexOf('nsImagebutton_')===0)c.imagebutton++;
    else if(k.indexOf('nscodemirror_')===0)c.codemirror++;
    else if(k.indexOf('nshyperlink_')===0)c.hyperlink++;
    else c.other++;});
  return JSON.stringify(c)})()`;
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-lj-'+tag+'-'+SESSION,'--no-first-run','--disable-gpu','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(port,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  return { proc, ev, log, navigate: u => send('Page.navigate',{url:u}) };
}
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)) return true; await new Promise(r=>setTimeout(r,1000)); } return false; }
async function evalIn(b, flag, expr) {
  await b.ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(expr)});cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,2500));
  await b.ev(click('Evaluate Selection'));
  const ok = await waitFor(b, 'window.'+flag+' !== undefined', 20000);
  console.log('A '+flag+':', ok ? JSON.stringify(await b.ev('window.'+flag)) : 'TIMEOUT');
  return ok;
}
async function main() {
  const A = await browser(9471,'a');
  await A.navigate(URL);
  await waitFor(A, "document.body && document.body.innerText.includes('Workspaces')", 180000);
  await new Promise(r=>setTimeout(r,4000));
  await A.ev(click('Workspaces'));
  await waitFor(A, "document.body.innerText.includes('Evaluate')", 30000);
  await new Promise(r=>setTimeout(r,3000));
  await evalIn(A, 'w1', "platform js global at: 'w1' put: 'first'");
  console.log('A census after w1:', await A.ev(CENSUS));
  await A.ev('history.back(); "BACK"');
  await waitFor(A, "!document.body.innerText.includes('Evaluate Selection')", 30000);
  await new Promise(r=>setTimeout(r,3000));
  console.log('A back home; census (workspace lineages retired):', await A.ev(CENSUS));
  await A.ev(click('Workspaces'));
  await waitFor(A, "document.body.innerText.includes('Evaluate')", 30000);
  await new Promise(r=>setTimeout(r,3000));
  await evalIn(A, 'w2', "platform js global at: 'w2' put: 'second'");
  console.log('A census after w2:', await A.ev(CENSUS));
  const aTotal = await A.ev('theModel.newspeakEvents.length');
  const aProcessed = await A.ev('lastProcessedEvent');
  console.log('A events:', aProcessed, 'of', aTotal);

  console.log('--- late joiner B joins ---');
  const t0 = Date.now();
  const B = await browser(9472,'b');
  await B.navigate(URL);
  const caught = await waitFor(B, 'window.lastProcessedEvent >= '+aTotal, 240000);
  const secs = Math.round((Date.now()-t0)/1000);
  console.log('B catch-up:', caught ? 'COMPLETE' : 'INCOMPLETE', 'in '+secs+'s;',
    await B.ev('lastProcessedEvent'), 'of', await B.ev('theModel.newspeakEvents.length'));
  await new Promise(r=>setTimeout(r,3000));
  console.log('B census:', await B.ev(CENSUS));
  console.log('B on workspace page:', await B.ev("document.body.innerText.includes('Evaluate Selection')"));
  console.log('B sees w2 result:', await B.ev("document.body.innerText.includes('second')"));
  const skipsB = B.log.filter(l=>l.includes('no subscriber'));
  console.log('B replay orphan skips:', skipsB.length, skipsB.slice(0,3).join(' || ') || '(none)');
  const censusA = await A.ev(CENSUS), censusB = await B.ev(CENSUS);
  console.log('CENSUS MATCH:', censusA === censusB ? 'PASS' : 'FAIL ('+censusA+' vs '+censusB+')');
  console.log('ORPHAN-FREE REPLAY:', skipsB.length === 0 ? 'PASS' : 'FAIL');
  console.log('--- B console tail ---'); console.log(B.log.slice(-8).join('\n'));
  A.proc.kill(); B.proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
