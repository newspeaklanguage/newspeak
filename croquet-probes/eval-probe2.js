/* Stepwise workspace-eval probe on the Croquet TEST IDE: evaluate a series of
   expressions, each setting a JS flag; report which step breaks and what the
   page/console show. */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'evprobe' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetHopscotchWebIDE.html?sessionId='
  : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const STEPS = [
  ["w1", "platform js global at: 'w1' put: 'basic'"],
  ["m1", "platform js global at: 'm1' put: ([:mb | platform js global at: 'mStart' put: 'STARTED'. mb nestedClasses addFromSource: 'public class ZY1 contents: c <String> = Document named: #ZY1 contents: c ()()'. platform js global at: 'mid' put: 'ADD-COMPLETED'. 'DONE'] value: ide documents documentHolderMixinBuilder)"],
];
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9468','--remote-allow-origins=*','--user-data-dir=/tmp/cq-evprobe-'+SESSION,'--no-first-run','--disable-gpu','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9468,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&t.includes('Workspaces')) break; await new Promise(r=>setTimeout(r,1500)); }
  await new Promise(r=>setTimeout(r,4000));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Workspaces');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  for (let i=0;i<30;i++){ const t=await ev('document.body.innerText'); if (typeof t==='string'&&t.includes('Evaluate')) break; await new Promise(r=>setTimeout(r,1000)); }
  await new Promise(r=>setTimeout(r,3000));
  await ev(`(function(){window._pubs=[];var op=theView.publish.bind(theView);theView.publish=function(s,e,d){window._pubs.push([s,e,typeof d]);return op(s,e,d)};return 'HOOKED'})()`);
  for (const [flag, expr] of STEPS) {
    await ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(expr)});cm.execCommand('selectAll');return 'SET'})()`);
    await new Promise(r=>setTimeout(r,2500));
    await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Evaluate Selection');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
    let v=null; const t0=Date.now();
    while (Date.now()-t0<15000){ v=await ev('window.'+flag); if (v!==undefined&&v!==null) break; await new Promise(r=>setTimeout(r,1000)); }
    console.log(flag+':', JSON.stringify(v));
    if (v===undefined||v===null) {
      const b=String(await ev('document.body.innerText'));
      console.log('page tail:', JSON.stringify(b.slice(-800)));
    }
  }
  console.log('mid flag:', JSON.stringify(await ev('window.mid')));
  console.log('waiting 60 more seconds...');
  let late=null; for (let i=0;i<60;i++){ late=await ev('window.m1'); if (late) break; await new Promise(r=>setTimeout(r,1000)); }
  console.log('m1 after long wait:', JSON.stringify(late));
  console.log('mStart flag:', JSON.stringify(await ev('window.mStart')));
  console.log('publishes since hook:', JSON.stringify(await ev('window._pubs')));
  console.log('events tail:', JSON.stringify(await ev('theModel && theModel.newspeakEvents.slice(-8).map(e=>{var s=JSON.stringify(e);return s.length>160?s.slice(0,160)+"...":s})')));
  console.log('nav back home:', await ev('history.back(); "BACK"'));
  await new Promise(r=>setTimeout(r,4000));
  const b2=String(await ev('document.body.innerText'));
  console.log('home reachable after wedge:', b2.includes('Workspaces') && !b2.includes('Evaluate Selection') ? 'YES' : 'checking: '+JSON.stringify(b2.slice(0,200)));
  console.log('lastProcessedEvent:', await ev('lastProcessedEvent'), 'of', await ev('theModel && theModel.newspeakEvents.length'));
  console.log('--- console tail ---'); console.log(log.slice(-10).join('\n'));
  proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
