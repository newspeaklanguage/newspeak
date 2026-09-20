/* Typing in an Ampleforth document's LIVE (WYSIWYG) view must reach the other
   clients. It did not between 2026-09-12 (9141e50, which stopped publishing
   programmatic editor changes) and 2026-09-19: the live view writes what was
   typed into the raw pane, that write was a plain setValue, setValue-origin
   changes are not published, and native contenteditable insertion is not a
   Newspeak event either - so nothing was published at all. Every client
   replayed the recorded history, stopped where it ended, and then edited
   locally with no effect on the others, with no console error, because the
   divergence alarm only fires for events that WERE recorded. The fix tags the
   live view's write 'liveview' (Documents updater, CodeMirrorFragment
   text:origin:), which isUserOrigin: accepts.

     croquet-probes/run.sh ampleforth-sync-probe.js [js]

   N (12 characters)  CADENCE_MS (120)  NS_PAGE (croquetpsoup-test.html)
   NS_SNAPSHOT (CroquetHopscotchWebIDE-TEST.vfuel)

   Negative control - a green probe proves nothing on its own. Build the same
   tree with the fix undone and run against it; the first assertion must fail:

     cd tool && ./build-bugged-test-vfuel.sh
     NS_SNAPSHOT=CroquetHopscotchWebIDE-BUG.vfuel \
       croquet-probes/run.sh ampleforth-sync-probe.js

   The first assertion is the regression itself: typing in the live view must
   record events. A probe that only compared the two views would have passed
   for a week while nothing synchronized, because both views were equally
   stale.

   The navigation was the hard part and is now solved with no production code
   at all: `ide browsing navigateTo:` (see openDocument below). An earlier note
   here concluded that only a click from a presenter could navigate, because
   the verb is on neither the Workspace model nor `ide`; it is on the Browsing
   module, put there for the AI tools, which have no presenter either. */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'ample' + Math.floor(Date.now() / 1000);
const JS = process.argv[2] === 'js';
const PAGE = JS ? 'CroquetJSIDE-TEST.html?sessionId='
                : (process.env.NS_PAGE || 'croquetpsoup-test.html') + '?snapshot=' +
                  (process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE-TEST.vfuel') + '&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const N = Number(process.env.N || 12), CADENCE = Number(process.env.CADENCE_MS || 120);
const sleep = ms => new Promise(r => setTimeout(r, ms));
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
/* Any element whose own trimmed text is exactly the label; the last match is
   the innermost, which is the one a person would hit. Hopscotch renders
   controls as several kinds of node (button:, link:, image buttons), so this
   deliberately does not restrict the tag. */
const click = label => `(function(){var m=Array.from(document.querySelectorAll('*')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});if(!m.length)return 'NOBTN';var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
const nearLabel = label => `(function(){var out=[];Array.from(document.querySelectorAll('*')).forEach(function(e){var t=(e.innerText||'').trim();if(t.indexOf(${JSON.stringify(label)})>=0&&t.length<60&&e.children.length<3)out.push(e.tagName+':'+JSON.stringify(t))});return out.slice(-12).join(' | ')})()`;
/* The live view: the document body's contenteditable host. */
const LIVE = "document.querySelector('.self_ampleforth')";
const LIVE_TEXT = `(${LIVE}?${LIVE}.innerText.replace(/\\s+/g,' ').trim():'(none)')`;
const EVENTS = "(typeof theModel==='undefined'||!theModel?-1:theModel.newspeakEvents.length)";
const live = [];
function bail(why) {
  console.log('BAIL: ' + why);
  for (const b of live) { console.log('  ' + b.tag + ' console tail: ' + b.log.slice(-6).join(' || ')); try { b.proc.kill(); } catch (e) {} }
  process.exit(1);
}
setTimeout(() => bail('overall deadline passed'), Number(process.env.DEADLINE_MS || 420000)).unref();
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-amp-'+tag+'-'+SESSION,'--no-first-run','--window-size=1400,1000','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<300;i++){ try { const t=await getJson(port,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await sleep(300); }
  if (!page) { try { proc.kill(); } catch (e) {} bail('no page target on port ' + port); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'&&(m.params.type==='error'||m.params.type==='warning'))log.push('['+m.params.type+'] '+m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ').slice(0,200));
    if(m.method==='Runtime.exceptionThrown')log.push('[THROWN] '+((m.params.exceptionDetails.exception||{}).description||'').slice(0,300));}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); if (r&&r.exceptionDetails) return 'EVAL-THREW: '+((r.exceptionDetails.exception||{}).description||r.exceptionDetails.text); return r&&r.result&&r.result.value; };
  const b = { proc, ev, send, log, tag };
  live.push(b);
  return b;
}
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)===true) return true; await sleep(500); } return false; }
async function boot(b) {
  await b.send('Page.navigate',{url:URL});
  if (!await waitFor(b, "!!(document.body && document.body.innerText.includes('Workspaces'))", 150000)) bail(b.tag + ' never showed the home page');
  console.log(b.tag + ' booted'); await sleep(4000);
}
/* Open a document. The IDE has no one-click 'new document', so the workspace
   evaluates one into existence AND navigates to it.

   An evaluation can navigate after all. Browsing>>navigateTo: (public, it
   just sends currentWindow enterSubject:) exists precisely for "callers that
   need to drive navigation without holding a presenter" - the AI tools are in
   that position too, and AI_IDE_Support drives a document with exactly the
   expression below. The earlier belief that only a click from a presenter
   could navigate came from looking for the verb on the Workspace model and on
   `ide`, where it is indeed absent; it lives on the Browsing module.

   `ide documents DocumentSubject` is the right subject, not
   TwoViewEditorSubject: its presenter is DocumentPresenter, which HOLDS a
   TwoViewEditorPresenter (slot `twoViewEditor`) and is what the IDE shows for
   a document, chrome and all. TwoViewEditorSubject alone would still render a
   live view, but through a presenter no IDE path builds, so a break in the
   IDE's own wrapper would go unseen.

   The candidates are kept as a list so that a scope change names itself: the
   first expression that puts a .self_ampleforth host on the page wins, and
   every failure prints what the workspace answered. */
const MAKE = "(ide documents freshDocumentNamed: #ProbeDoc initialText: 'Probe body.')";
const CANDIDATES = [
  'ide browsing navigateTo: (ide documents DocumentSubject onModel: ' + MAKE + ')',
  'ide browsing navigateTo: (ide documents TwoViewEditorSubject onModel: ' + MAKE + ')',
];
/* The workspace's control is 'Evaluate Selection': it evaluates what is
   selected, and replaceSelection leaves the caret after the insertion with
   nothing selected, so the text is selected again before the click. */
async function evaluateInWorkspace(b, src) {
  await b.ev(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');cm.replaceSelection(${JSON.stringify(src)},null,'+input');cm.execCommand('selectAll');return 1})()`);
  await sleep(800);
  const r = await b.ev(click('Evaluate Selection'));
  if (r === 'NOBTN') bail('no Evaluate Selection control in the workspace; candidates: ' + await b.ev(nearLabel('Evaluate')));
  await sleep(3000);
}
/* What the workspace shows after an evaluation: its printString, or the error
   it reported. Printed for every attempt, so a wrong name or scope names
   itself instead of just failing to produce a document. */
const TAIL = "document.body.innerText.replace(/\\s+/g,' ').trim().slice(-260)";
async function openDocument(b) {
  for (const src of (process.env.SCOUT ? ['1 + 1', 'ide printString', 'ide documents printString'] : []).concat(CANDIDATES)) {
    await evaluateInWorkspace(b, src);
    const answered = await b.ev(TAIL);
    if (await waitFor(b, `!!${LIVE}`, 12000)) { console.log('  opened with: ' + src); return true; }
    console.log('  no document from: ' + src + '\n      answered: ' + JSON.stringify(answered));
  }
  return false;
}
/* Type into the live view: focus the contenteditable and put the caret at the
   very end, then send real key events, so the browser inserts the characters
   itself exactly as it does for a person - which is the whole point, that
   insertion being what no Newspeak event describes. */
async function typeIntoLiveView(b, ch, n) {
  await b.ev(`(function(){var el=${LIVE};el.focus();var r=document.createRange();r.selectNodeContents(el);r.collapse(false);var s=getSelection();s.removeAllRanges();s.addRange(r);return 1})()`);
  for (let i = 0; i < n; i++) {
    const t0 = Date.now();
    await b.send('Input.dispatchKeyEvent', { type: 'keyDown', text: ch, unmodifiedText: ch, key: ch });
    await b.send('Input.dispatchKeyEvent', { type: 'keyUp', key: ch });
    const rest = CADENCE - (Date.now() - t0); if (rest > 0) await sleep(rest);
  }
}
let fails = 0;
const ok = (name, pass, detail) => { if (!pass) fails++; console.log((pass ? '  PASS  ' : '  FAIL  ') + name + (detail ? '   ' + detail : '')); };
async function main() {
  console.log('N=' + N + ' CADENCE_MS=' + CADENCE + '  ' + PAGE);
  const A = await browser(9495, 'A'); await boot(A);
  await A.ev(click('Workspaces'));
  if (!await waitFor(A, "document.body.innerText.includes('Evaluate')", 40000)) bail('A never reached the workspace');
  const B = await browser(9496, 'B'); await boot(B);
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000)) bail('B never followed A to the workspace');
  await sleep(3000);

  if (!await openDocument(A)) bail('no candidate expression opened a document on A');
  if (!await waitFor(B, `!!${LIVE}`, 60000)) bail('B never followed A into the document');
  await sleep(3000);
  console.log('A live view: ' + JSON.stringify(await A.ev(LIVE_TEXT)));
  console.log('B live view: ' + JSON.stringify(await B.ev(LIVE_TEXT)));

  const evBefore = await A.ev(EVENTS);
  await typeIntoLiveView(A, 'z', N);
  console.log('typed ' + N + " 'z' into A's live view; settling...");
  let ta, tb, stable = 0, t0 = Date.now();
  while (Date.now() - t0 < 60000 && stable < 5) {
    await sleep(1000);
    const na = await A.ev(LIVE_TEXT), nb = await B.ev(LIVE_TEXT);
    stable = (na === ta && nb === tb && na === nb) ? stable + 1 : 0; ta = na; tb = nb;
  }
  const evAfter = await A.ev(EVENTS);
  console.log('A live view: ' + JSON.stringify(ta));
  console.log('B live view: ' + JSON.stringify(tb));

  const zs = s => (String(s).match(/z/g) || []).length;
  ok('LIVE-VIEW TYPING RECORDS EVENTS', evAfter > evBefore, 'events ' + evBefore + ' -> ' + evAfter);
  ok('B RECEIVES THE TYPED TEXT', zs(tb) >= N, "B has " + zs(tb) + " 'z' of " + N);
  ok('LIVE VIEWS AGREE', ta === tb);
  const divs = [await A.ev('String(nsDivergences.length)'), await B.ev('String(nsDivergences.length)')];
  ok('NO DIVERGENCE REPORTED', divs[0] === '0' && divs[1] === '0', 'A=' + divs[0] + ' B=' + divs[1]);
  console.log('errors/warnings A/B: ' + A.log.length + ' / ' + B.log.length + (A.log.length + B.log.length ? '\n  ' + A.log.concat(B.log).slice(-6).join('\n  ') : ''));
  console.log('==== ' + (fails ? fails + ' FAILED' : 'all passed') + ' ====');
  for (const b of live) { try { b.proc.kill(); } catch (e) {} }
  process.exit(fails ? 1 : 0);
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
