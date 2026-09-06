/* propertyAt: parity probe. The SAME workspace evals must answer the SAME
   values on psoup and NS2JS, on a value where plain at: diverges (a
   Uint8Array: Alien with property-at: on psoup, bilingual ByteArray with
   1-based element-at: on NS2JS — see
   memory ns2js-alien-at-native-collision / the propertyAt: change).
   pp1: property read off a typed array.
   pp2: chained property reads (exercises NS2JS raw-result chaining).
   pp3: a raw property result passed back INTO a JS call (exercises the
        expatriate: pass-through on NS2JS; alien unwrap on psoup).
   Run: node property-parity-probe.js [js] */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'ppprobe' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const HELPERS = "window.nsProbeLen = function(b){ return b.byteLength };";
const STEPS = [
  ["pp1", "platform js global at: 'pp1' put: ((((platform js global at: #TextEncoder) new encode: 'HI') propertyAt: #byteLength)) printString", "2"],
  ["pp2", "platform js global at: 'pp2' put: (((((platform js global at: #TextEncoder) new encode: 'HI') propertyAt: #buffer) propertyAt: #byteLength)) printString", "2"],
  ["pp3", "platform js global at: 'pp3' put: (platform js global nsProbeLen: ((((platform js global at: #TextEncoder) new encode: 'HI') propertyAt: #buffer))) printString", "2"],
];
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9486','--remote-allow-origins=*','--user-data-dir=/tmp/cq-pp-'+SESSION,'--no-first-run','--disable-gpu','--disable-background-timer-throttling','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9486,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  await send('Page.addScriptToEvaluateOnNewDocument',{source: HELPERS});
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&t.includes('Workspaces')) break; await new Promise(r=>setTimeout(r,1500)); }
  await new Promise(r=>setTimeout(r,4000));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Workspaces');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  for (let i=0;i<30;i++){ if (await ev("document.body.innerText.includes('Evaluate')")) break; await new Promise(r=>setTimeout(r,1000)); }
  await new Promise(r=>setTimeout(r,3000));
  let allPass = true;
  for (const [flag, expr, expect] of STEPS) {
    await ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(expr)});cm.execCommand('selectAll');return 'SET'})()`);
    await new Promise(r=>setTimeout(r,2500));
    await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Evaluate Selection');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
    let v=null; const t0=Date.now();
    while (Date.now()-t0<20000){ v=await ev('window.'+flag); if (v!=null) break; await new Promise(r=>setTimeout(r,1000)); }
    const ok = v === expect;
    allPass = allPass && ok;
    console.log(flag+':', ok ? 'PASS' : 'FAIL', JSON.stringify(v), ok ? '' : '(expected '+JSON.stringify(expect)+')');
  }
  console.log('PROPERTY PARITY ('+(process.argv[2]==='js'?'NS2JS':'psoup')+'):', allPass ? 'ALL PASS' : 'FAIL');
  if (!allPass) console.log(log.slice(-8).join('\n'));
  proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
