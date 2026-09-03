/* Fragment-identity verification probe (plan: CROQUET_FRAGMENT_IDENTITY_PLAN
   _2026-08-27.md §5). Runs the original eval-"stall" scenario against the TEST
   IDE vfuel with EVERY step in the plain 2.5s flow -- no reselect hack. Before
   the fix, w2 (plain second eval) and m1 failed with an empty selection at
   click dispatch. Also asserts the registry invariant: the number of
   nsbutton_/nscodemirror_ subscription keys must stay CONSTANT across
   evaluations (one generation per visual). nsImagebutton_ keys are reported
   but NOT asserted: ImageButtonFragment is not yet converted. */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'evprobe5' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const STEPS = [
  ["w1", "platform js global at: 'w1' put: 'basic'"],
  ["w2", "platform js global at: 'w2' put: 'plain-second'"],
  ["m1", "platform js global at: 'm1' put: ([:mb | platform js global at: 'mStart' put: 'STARTED'. mb nestedClasses addFromSource: 'public class ZY1 contents: c <String> = Document named: #ZY1 contents: c ()()'. platform js global at: 'mid' put: 'ADD-COMPLETED'. 'DONE'] value: ide documents documentHolderMixinBuilder)"],
];
const CENSUS = `(function(){var c={button:0,imagebutton:0,codemirror:0,other:0};
  Array.from(newspeakSubscriptions.keys()).forEach(function(k){
    if(k.indexOf('nsbutton_')===0)c.button++;
    else if(k.indexOf('nsImagebutton_')===0)c.imagebutton++;
    else if(k.indexOf('nscodemirror_')===0)c.codemirror++;
    else c.other++;});
  return JSON.stringify(c)})()`;
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9469','--remote-allow-origins=*','--user-data-dir=/tmp/cq-evprobe5-'+SESSION,'--no-first-run','--disable-gpu','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9469,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.exceptionThrown'){log.push('[EXC] '+JSON.stringify(m.params.exceptionDetails.exception&&m.params.exceptionDetails.exception.description||m.params.exceptionDetails.text).slice(0,300));}
    else if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){log.push('[WS-PARSE-ERR] '+String(e).slice(0,120));}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&t.includes('Workspaces')) break; await new Promise(r=>setTimeout(r,1500)); }
  await new Promise(r=>setTimeout(r,4000));
  console.log('build:', JSON.stringify(String(await ev('document.title'))),'| home census:', await ev(CENSUS));
  await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Workspaces');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
  for (let i=0;i<30;i++){ const t=await ev('document.body.innerText'); if (typeof t==='string'&&t.includes('Evaluate')) break; await new Promise(r=>setTimeout(r,1000)); }
  await new Promise(r=>setTimeout(r,3000));
  const baseline = JSON.parse(await ev(CENSUS));
  console.log('workspace census (baseline):', JSON.stringify(baseline));
  await ev('window._prevKeys = Array.from(newspeakSubscriptions.keys()); "SNAP"');
  const censuses = [];
  for (const [flag, expr] of STEPS) {
    await ev(`(function(){var cms=document.querySelectorAll('.CodeMirror');var cm=cms[cms.length-1].CodeMirror;cm.focus();cm.setValue(${JSON.stringify(expr)});cm.execCommand('selectAll');return 'SET'})()`);
    await new Promise(r=>setTimeout(r, 2500));
    await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()==='Evaluate Selection');var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`);
    let v=null; const t0=Date.now();
    while (Date.now()-t0<20000){ v=await ev('window.'+flag); if (v!==undefined&&v!==null) break; await new Promise(r=>setTimeout(r,1000)); }
    const census = JSON.parse(await ev(CENSUS));
    censuses.push(census);
    console.log(flag+':', JSON.stringify(v), '| census:', JSON.stringify(census));
    console.log('  keys added:', await ev('(function(){var now=Array.from(newspeakSubscriptions.keys());var added=now.filter(k=>window._prevKeys.indexOf(k)<0);var removed=window._prevKeys.filter(k=>now.indexOf(k)<0);window._prevKeys=now;return JSON.stringify({added:added,removed:removed})})()'));
    if (v===undefined||v===null) {
      const b=String(await ev('document.body.innerText'));
      console.log('page tail:', JSON.stringify(b.slice(-600)));
    }
  }
  console.log('DOM anchors:', await ev("document.querySelectorAll('a').length"),
    '| results visible:', await ev("JSON.stringify(['basic','plain-second','DONE'].map(s=>document.body.innerText.includes(s)))"));
  console.log('mid flag:', JSON.stringify(await ev('window.mid')));
  console.log('mStart flag:', JSON.stringify(await ev('window.mStart')));
  /* The workspace ACCUMULATES evaluation results (all three stay visible), so
     each eval legitimately mints one new hyperlink lineage, and the first eval
     materializes the result row's image button. The invariant is therefore:
     from the first eval on, the converted families gain NO further keys -- one
     generation per live visual. (Before the fix each eval added a full
     generation: +6 codemirror, +4 button, +12 imagebutton keys.) */
  const w1c = censuses[0];
  const stable = censuses.every(c => c.button === w1c.button && c.codemirror === w1c.codemirror && c.imagebutton === w1c.imagebutton);
  console.log('REGISTRY INVARIANT (converted families steady after first eval):', stable ? 'PASS' : 'FAIL');
  console.log('codemirror keys:', JSON.stringify(await ev("Array.from(newspeakSubscriptions.keys()).filter(k=>k.indexOf('nscodemirror')===0)")));
  console.log('button keys:', JSON.stringify(await ev("Array.from(newspeakSubscriptions.keys()).filter(k=>k.indexOf('nsbutton')===0)")));
  console.log('events tail:', await ev('theModel ? theModel.newspeakEvents.slice(-6).map(e=>{var s="";try{s=JSON.stringify(e)}catch(x){s="[unserializable]"}return s.length>140?s.slice(0,140)+"...":s}).join(" | ") : "no model"'));
  console.log('lastProcessedEvent:', await ev('lastProcessedEvent'), 'of', await ev('theModel && theModel.newspeakEvents.length'));
  console.log('js errors:', JSON.stringify(await ev('window._errs||[]')));
  console.log('--- console tail ---'); console.log(log.slice(-12).join('\n'));
  proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
