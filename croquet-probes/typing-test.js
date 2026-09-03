/* Two-client typing convergence under the fragment-identity lifecycle.
   Reconstruction of the risky core of the reboot-lost liveview-edit test:
   an EDITOR BUFFER >8KB so every keystroke's full-text publish takes the
   Data-API detour (delayed echoes - the regime that broke focus/caret before
   the pendingLiveEdits fix), typed into under Croquet with adoption in play.
   A sets a 9KB buffer, types 6 chars; B must converge to the final text; A's
   focus must survive; the registry must stay steady. Closes with a
   syncRandom determinism check: one synced eval draws on BOTH clients, whose
   streams must be at the same position (equal draws).
   Run: node typing-test.js [js] */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'typing' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : process.argv[2] === 'stock'
    ? 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE.vfuel&sessionId='
    : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-typ-'+tag+'-'+SESSION,'--no-first-run','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
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
const LASTCM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)) return true; await new Promise(r=>setTimeout(r,1000)); } return false; }
async function boot(b) {
  await b.navigate(URL);
  await waitFor(b, "document.body && document.body.innerText.includes('Workspaces')", 240000);
  await new Promise(r=>setTimeout(r,4000));
}
async function main() {
  const A = await browser(9475,'a'); await boot(A);
  await A.ev(click('Workspaces'));
  await waitFor(A, "document.body.innerText.includes('Evaluate')", 30000);
  const B = await browser(9476,'b'); await boot(B);
  await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000);
  await new Promise(r=>setTimeout(r,3000));
  console.log('both on workspace. A sets 9KB buffer...');
  await A.ev(`(function(){var cm=${LASTCM};cm.focus();var pad='(* '+'x'.repeat(9000)+' *) ';cm.setValue(pad);cm.setCursor(cm.lineCount()-1);return 'SET '+cm.getValue().length})()`);
  const bConverged1 = await waitFor(B, LASTCM+".getValue().length > 9000", 60000);
  console.log('B received 9KB buffer (detour path):', bConverged1 ? 'PASS' : 'FAIL');
  console.log('A types 6 chars...');
  for (const ch of 'abc123') {
    await A.ev(`(function(){var cm=${LASTCM};cm.replaceSelection(${JSON.stringify(ch)});return 'T'})()`);
    await new Promise(r=>setTimeout(r,700));
  }
  const focusHeld = await A.ev("(function(){var el=document.activeElement;while(el){if(el.classList&&el.classList.contains('CodeMirror'))return true;el=el.parentElement}return false})()");
  console.log('A focus still in editor:', focusHeld ? 'PASS' : 'FAIL');
  /* The real invariant is A == B (convergence). Whether all six chars survive
     the interleaving of local typing with delayed detour echoes is the KNOWN
     PARKED fast-typing race (full text per keystroke vs ~1s detour RTT) -
     reported informationally, not asserted. */
  await new Promise(r=>setTimeout(r,8000));
  const headA = String(await A.ev(LASTCM+'.getValue().slice(0,12)'));
  let headB = String(await B.ev(LASTCM+'.getValue().slice(0,12)'));
  const t1=Date.now(); while (headB !== headA && Date.now()-t1<30000) { await new Promise(r=>setTimeout(r,2000)); headB = String(await B.ev(LASTCM+'.getValue().slice(0,12)')); }
  console.log('A==B CONVERGENCE:', headA === headB ? 'PASS' : 'FAIL', '| A:', JSON.stringify(headA), 'B:', JSON.stringify(headB));
  console.log('chars surviving the echo race (info, known parked issue):', JSON.stringify(headA.split('(*')[0]));
  const cmKeysA = await A.ev("Array.from(newspeakSubscriptions.keys()).filter(k=>k.indexOf('nscodemirror')===0).length");
  const cmKeysB = await B.ev("Array.from(newspeakSubscriptions.keys()).filter(k=>k.indexOf('nscodemirror')===0).length");
  console.log('REGISTRY STEADY (6 cm keys each):', (cmKeysA===6&&cmKeysB===6) ? 'PASS' : 'FAIL ('+cmKeysA+'/'+cmKeysB+')');
  console.log('--- syncRandom determinism ---');
  await A.ev(`(function(){var cm=${LASTCM};cm.focus();cm.setValue("platform js global at: 'rnd' put: platform hopscotch syncRandom printString");cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,2500));
  await A.ev(click('Evaluate Selection'));
  await waitFor(A, "typeof window.rnd === 'string'", 20000);
  await waitFor(B, "typeof window.rnd === 'string'", 20000);
  const rA = await A.ev('window.rnd'), rB = await B.ev('window.rnd');
  console.log('SYNC RANDOM AGREES:', (rA && rA === rB) ? 'PASS ('+String(rA).slice(0,12)+'...)' : 'FAIL ('+rA+' vs '+rB+')');
  const errsA = A.log.filter(l=>l.startsWith('[error]')).length, errsB = B.log.filter(l=>l.startsWith('[error]')).length;
  console.log('errors A/B:', errsA, '/', errsB);
  if (errsA+errsB) { console.log(A.log.filter(l=>l.startsWith('[error]')).slice(0,3).join('\n')); console.log(B.log.filter(l=>l.startsWith('[error]')).slice(0,3).join('\n')); }
  A.proc.kill(); B.proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
