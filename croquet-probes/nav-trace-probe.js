/* Trace subscription add/remove across navigation: boot -> Workspaces -> back.
   Diagnoses the latejoin-probe finding (fresh home page after back has no
   hyperlink subscriptions). */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'navtrace' + Math.floor(Date.now() / 1000);
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9473','--remote-allow-origins=*','--user-data-dir=/tmp/cq-navtrace-'+SESSION,'--no-first-run','--disable-gpu','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9473,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map();
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);}}catch(e){}});
  await send('Runtime.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  const diff = async label => console.log(label, await ev('(function(){var now=Array.from(newspeakSubscriptions.keys());var added=now.filter(k=>(window._pk||[]).indexOf(k)<0);var removed=(window._pk||[]).filter(k=>now.indexOf(k)<0);window._pk=now;return JSON.stringify({n:now.length,added:added,removed:removed})})()'));
  const click = label => ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&t.includes('Workspaces')) break; await new Promise(r=>setTimeout(r,1500)); }
  await new Promise(r=>setTimeout(r,4000));
  await diff('HOME BOOT:');
  await click('Workspaces');
  for (let i=0;i<30;i++){ if (await ev("document.body.innerText.includes('Evaluate')")) break; await new Promise(r=>setTimeout(r,1000)); }
  await new Promise(r=>setTimeout(r,3000));
  await diff('AFTER NAV TO WORKSPACES:');
  await ev('history.back(); "B"');
  await new Promise(r=>setTimeout(r,6000));
  await diff('AFTER BACK TO HOME:');
  console.log('home visible:', await ev("document.body.innerText.includes('Newspeak Source')"));
  console.log('anchors:', await ev("document.querySelectorAll('a').length"));
  console.log('events:', await ev('lastProcessedEvent'), 'of', await ev('theModel.newspeakEvents.length'));
  proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
