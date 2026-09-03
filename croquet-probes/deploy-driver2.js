/* Package a Croquet JS deploy of the whole IDE from a headless plain psoup
   IDE (HopscotchWebIDE-TEST.vfuel), via a workspace doIt, and stage the four
   artifacts as out/CroquetJSIDE-TEST.* (names rewritten from the packager's
   CroquetHopscotchWebIDE so the stock JS deploy is never clobbered).
   Reconstruction of the reboot-lost deploy-driver-test.js. Packaging itself
   takes ~25s once background-tab throttling is disabled. */
const { spawn } = require('child_process');
const http = require('http');
const fs = require('fs');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const OUT = '/Users/gbracha/newspeak/dev/web/newspeak/out/';
const URL = 'http://localhost:8080/primordialsoup.html?snapshot=HopscotchWebIDE-TEST.vfuel';
const DOIT = "[:d | platform js global at: #depPage put: d page. platform js global at: #depScript put: d script. platform js global at: #depSources put: d sources. platform js global at: #depCroquet put: d croquetSupport. 'PACKAGED-OK'] value: ((ide deployment jsPackagerForPlatform: platform) packageCroquetApplicationConfiguration: (ide namespacing Root at: #HopscotchWebIDE) withRuntimeConfiguration: ide deployment CroquetRuntime usingNamespace: ide namespacing Root)";
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9474','--remote-allow-origins=*','--user-data-dir=/tmp/cq-deploy2','--no-first-run','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9474,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false, maxPayload: 64*1024*1024});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){}});
  await send('Runtime.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&t.includes('Workspaces')) break; await new Promise(r=>setTimeout(r,1500)); }
  await new Promise(r=>setTimeout(r,3000));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Workspaces');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  for (let i=0;i<30;i++){ if (await ev("document.body.innerText.includes('Evaluate')")) break; await new Promise(r=>setTimeout(r,1000)); }
  await new Promise(r=>setTimeout(r,2000));
  await ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(DOIT)});cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,1500));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Evaluate Selection');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  console.log('packaging...');
  const t0=Date.now(); let done=false;
  while (Date.now()-t0<600000){ if (await ev('typeof window.depCroquet === "string"')) { done=true; break; } await new Promise(r=>setTimeout(r,2000)); }
  if (!done) { console.log('PACKAGING TIMED OUT'); console.log(log.slice(-10).join('\n')); const b=String(await ev('document.body.innerText')); console.log('page tail:', b.slice(-500)); proc.kill(); process.exit(1); }
  console.log('packaged in', Math.round((Date.now()-t0)/1000)+'s');
  const RENAME = s => s.split('CroquetHopscotchWebIDE').join('CroquetJSIDE-TEST');
  async function save(globalName, file) {
    const len = await ev('window.'+globalName+'.length');
    const CH = 4*1024*1024; let out='';
    for (let off=0; off<len; off+=CH) out += await ev('window.'+globalName+'.slice('+off+','+(off+CH)+')');
    fs.writeFileSync(OUT+file, RENAME(out));
    console.log(file+':', fs.statSync(OUT+file).size, 'bytes');
  }
  await save('depPage', 'CroquetJSIDE-TEST.html');
  await save('depScript', 'CroquetJSIDE-TEST.js');
  await save('depSources', 'CroquetJSIDE-TEST.sources.js');
  await save('depCroquet', 'CroquetJSIDE-TEST.croquet.js');
  proc.kill();
  console.log('DEPLOY STAGED');
}
main().catch(e=>{console.error(e);process.exit(1);});
