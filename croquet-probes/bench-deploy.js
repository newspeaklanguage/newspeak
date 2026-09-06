/* Package a plain-JS BenchmarkRunner deploy from a headless psoup IDE.
   Usage: node bench-deploy.js <ide-vfuel-name> <output-prefix>
   Writes <prefix>.js and <prefix>.sources.js into this bench/ dir. */
const { spawn } = require('child_process');
const http = require('http');
const fs = require('fs');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const OUT = '/private/tmp/claude-503/-Users-gbracha-newspeak-dev-web-newspeak/05357d29-a0e8-4bac-b993-9ce5fc0addad/scratchpad/bench/';
const VFUEL = process.argv[2];
const PREFIX = process.argv[3];
const URL = 'http://localhost:8080/primordialsoup.html?snapshot=' + VFUEL;
const DOIT = "[:d | platform js global at: #depScript put: d script. platform js global at: #depSources put: d sources. 'PACKAGED-OK'] value: ((ide deployment jsPackagerForPlatform: platform) packageApplicationConfiguration: (ide namespacing Root at: #BenchmarkRunner) withRuntimeConfiguration: ide deployment Runtime usingNamespace: ide namespacing Root)";
/* The Benchmarks-category classes are compiled into the image but not
   registered in the IDE's Root namespace, which the packager resolves
   against - install them from source first. */
const BENCH_SRC_DIR = '/Users/gbracha/newspeak/dev/web/primordialsoup/newspeak/';
const BENCH_FILES = ['BenchmarkRunner','ClosureDefFibonacci','ClosureFibonacci','DeltaBlue','MethodFibonacci','NLRImmediate','NLRLoop','ParserCombinators','Richards','SlotRead','SlotWrite','Splay'];
const INSTALL_DOIT = "[:g | (ide installFromBuilders: ((0 to: " + (BENCH_FILES.length-1) + ") collect: [:i | platform mirrors ClassDeclarationBuilder fromUnitSource: (g at: 'benchSrc', i printString)]) asArray) do: [:mm | ide namespacing Root at: mm name asSymbol put: mm declaration applyToObject reflectee]. (ide namespacing Root includesKey: #BenchmarkRunner) printString] value: platform js global";
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9490','--remote-allow-origins=*','--user-data-dir=/tmp/cq-benchdep-'+Date.now(),'--no-first-run','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9490,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false, maxPayload: 64*1024*1024});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map();
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);}}catch(e){}});
  await send('Runtime.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&(t.includes('Workspaces')||t.includes('backup changes'))) break; await new Promise(r=>setTimeout(r,1500)); }
  if (await ev("document.body.innerText.includes('backup changes')")) {
    await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim().indexOf('Use current version')===0);var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'D'})()`);
    for (let i=0;i<40;i++){ if (await ev("document.body.innerText.includes('Workspaces')")) break; await new Promise(r=>setTimeout(r,1500)); }
  }
  await new Promise(r=>setTimeout(r,3000));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Workspaces');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  for (let i=0;i<30;i++){ if (await ev("document.body.innerText.includes('Evaluate')")) break; await new Promise(r=>setTimeout(r,1000)); }
  await new Promise(r=>setTimeout(r,2000));
  for (let i=0;i<BENCH_FILES.length;i++) {
    const src = fs.readFileSync(BENCH_SRC_DIR+BENCH_FILES[i]+'.ns','utf8');
    await send('Runtime.evaluate',{expression:'window.benchSrc'+i+' = '+JSON.stringify(src)+'; "S"'});
  }
  await ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(INSTALL_DOIT)});cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,1500));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Evaluate Selection');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  await new Promise(r=>setTimeout(r,8000));
  const installed = String(await ev('document.body.innerText')).includes('true');
  console.log('benchmark classes installed into Root:', installed);
  await ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(DOIT)});cm.execCommand('selectAll');return 'SET'})()`);
  await new Promise(r=>setTimeout(r,1500));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Evaluate Selection');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  const t0=Date.now(); let done=false;
  while (Date.now()-t0<600000){ if (await ev('typeof window.depSources === "string"')) { done=true; break; } await new Promise(r=>setTimeout(r,2000)); }
  if (!done) { console.log('PACKAGING TIMED OUT'); console.log(String(await ev('document.body.innerText')).slice(-400)); proc.kill(); process.exit(1); }
  async function save(globalName, file) {
    const len = await ev('window.'+globalName+'.length');
    const CH = 4*1024*1024; let out='';
    for (let off=0; off<len; off+=CH) out += await ev('window.'+globalName+'.slice('+off+','+(off+CH)+')');
    fs.writeFileSync(OUT+file, out);
    console.log(file+':', fs.statSync(OUT+file).size, 'bytes');
  }
  await save('depScript', PREFIX+'.js');
  await save('depSources', PREFIX+'.sources.js');
  proc.kill();
  console.log('DEPLOY STAGED: '+PREFIX);
}
main().catch(e=>{console.error(e);process.exit(1);});
