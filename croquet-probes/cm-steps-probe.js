/* One client, one workspace editor, three CodeMirror operations done ONE AT A
   TIME - select all, replace the selection as a user edit, select all again -
   printing after each what the session recorded, the editor's state, and
   everything the page logged or threw. For telling apart "the handler raised",
   "the handler never ran" and "the timer published it" when the determinism
   suite shows a selection or change event missing (2026-09-18: the second
   selection publish went missing on the JS platform only).

     croquet-probes/run.sh cm-steps-probe.js        psoup TEST build
     croquet-probes/run.sh cm-steps-probe.js js     Croquet JS IDE test deploy
     GAP_MS=20 ...                                  pause between the operations (default 1500);
                                                    a short one keeps them inside the 80ms publishing window */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'cmsteps' + Math.floor(Date.now() / 1000);
const PAGE = process.argv[2] === 'js'
  ? 'CroquetJSIDE-TEST.html?sessionId='
  : (process.env.NS_PAGE || 'croquetpsoup-test.html') + '?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const GAP = Number(process.env.GAP_MS || 1500);
const sleep = ms => new Promise(r => setTimeout(r, ms));
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const STORY = "theModel.newspeakEvents.map((e,i)=>i+' '+e.scope+e.fid+':'+e.eventSpec).join(' | ')";
const STATE = `(function(){var cm=${CM};return JSON.stringify({len:cm.getValue().length,sel:cm.getSelection().length,cursor:cm.getCursor().ch})})()`;
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9487','--remote-allow-origins=*','--user-data-dir=/tmp/cq-cmsteps-'+SESSION,'--no-first-run','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  const done = code => { try { proc.kill(); } catch (e) {} process.exit(code); };
  setTimeout(() => { console.log('BAIL: deadline'); done(1); }, 300000).unref();
  let page; for (let i=0;i<300;i++){ try { const t=await getJson(9487,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await sleep(300); }
  if (!page) { console.log('BAIL: no page target'); done(1); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){log.push('['+m.params.type+'] '+m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ').slice(0,300));}
    if(m.method==='Runtime.exceptionThrown'){const d=m.params.exceptionDetails;log.push('[THROWN] '+(d.exception&&d.exception.description||d.text||'').slice(0,500));}}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); if (r&&r.exceptionDetails) return 'EVAL-THREW: '+(r.exceptionDetails.exception&&r.exceptionDetails.exception.description||r.exceptionDetails.text); return r&&r.result&&r.result.value; };
  const waitFor = async (pred, ms) => { const t0=Date.now(); while (Date.now()-t0<ms){ if (await ev(pred)===true) return true; await sleep(1000);} return false; };
  await send('Page.navigate',{url:URL});
  const t0 = Date.now();
  if (!await waitFor("!!(document.body && document.body.innerText.includes('Workspaces'))", 150000)) { console.log('BAIL: no home page'); done(1); }
  console.log('booted in ' + Math.round((Date.now()-t0)/1000) + 's  ' + PAGE);
  await sleep(4000);
  await ev(click('Workspaces'));
  if (!await waitFor("document.body.innerText.includes('Evaluate')", 40000)) { console.log('BAIL: no workspace'); done(1); }
  await sleep(3000);
  let seen = log.length;
  const report = async label => {
    await sleep(GAP);
    console.log('--- after ' + label);
    console.log('  storyline: ' + await ev(STORY));
    console.log('  editor:    ' + await ev(STATE));
    const fresh = log.slice(seen); seen = log.length;
    console.log('  page said: ' + (fresh.length ? fresh.join('\n             ') : '(nothing)'));
  };
  await report('opening the workspace');
  console.log('  selectAll command is patched: ' + await ev("String(CodeMirror.commands.selectAll).slice(0,120)"));
  /* Log every call the page makes to the editor's selection API, with its
     arguments as the editor receives them - the measurement that tells a bad
     event payload from a bad call across the alien bridge. */
  console.log('  spy: ' + await ev(`(function(){var cm=${CM};['setSelection','setCursor','setValue'].forEach(function(n){var o=cm[n];cm[n]=function(){var a=Array.from(arguments).map(function(x){try{return JSON.stringify(x)}catch(e){return String(x)}});console.log('SPY '+n+'('+a.join(', ').slice(0,260)+')');return o.apply(this,arguments)}});return 'installed'})()`));
  /* ...and every selection and change CodeMirror announces, in order, with the
     ranges as they stand when the LAST handler sees them. */
  console.log('  events: ' + await ev(`(function(){var cm=${CM};var P=function(p){return p.line+':'+p.ch};cm.on('beforeSelectionChange',function(c,o){console.log('CM beforeSelectionChange origin='+o.origin+' '+o.ranges.map(function(r){return P(r.anchor)+'-'+P(r.head)}).join(','))});cm.on('beforeChange',function(c,o){console.log('CM beforeChange origin='+o.origin+' '+P(o.from)+'-'+P(o.to)+' lines='+o.text.length)});cm.on('change',function(c,o){console.log('CM change origin='+o.origin+' docLines='+c.lineCount()+' sel='+c.listSelections().map(function(r){return P(r.anchor)+'-'+P(r.head)}).join(','))});return 'listening'})()`));
  const EVT = i => `(function(){var e=theModel.newspeakEvents[${i}];return e?JSON.stringify(e).slice(0,400):'(none)'})()`;
  const SELS = `(function(){var cm=${CM};return JSON.stringify(cm.listSelections())})()`;
  /* A cursor move with NO origin, on a valid position, caught: if a selection
     handler throws, this prints ITS error rather than whatever CodeMirror
     complains about afterwards. */
  console.log('0> untagged cursor move: ' + await ev(`(function(){var cm=${CM};try{cm.setCursor({line:0,ch:1});return 'ok, cursor '+JSON.stringify(cm.getCursor())}catch(e){return 'THREW: '+(e&&e.stack||e)}})()`));
  await report('untagged cursor move');
  console.log('1> ' + await ev(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');return 'selectAll #1'})()`));
  await report('selectAll #1');
  console.log('  recorded event 1: ' + await ev(EVT(1)));
  console.log('  selections now:   ' + await ev(SELS));
  console.log('2> ' + await ev(`(function(){var cm=${CM};cm.replaceSelection('3 + 4', null, '+input');return 'replaceSelection'})()`));
  await report('replaceSelection (+input)');
  console.log('3> ' + await ev(`(function(){var cm=${CM};cm.execCommand('selectAll');return 'selectAll #2'})()`));
  await report('selectAll #2');
  await sleep(1500);
  await report('a further 1.5s');
  done(0);
}
main().catch(e=>{console.error(e);process.exit(1);});
