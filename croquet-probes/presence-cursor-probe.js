/* Multiple cursors, end to end: does a participant's caret appear on the OTHER
 * client, and does it cost the session nothing?
 *
 *   croquet-probes/run.sh presence-cursor-probe.js [js]
 *
 * Two clients in one workspace editor. B moves its caret; A must DRAW it.
 *
 * WHY EACH ASSERTION HAS A CONTROL
 *
 * Every interesting claim here is a claim that something is ABSENT -- no
 * recorded event, no publish during typing, no cursor after exit. A counter
 * that never fires reads zero whatever happens, so an absence is only worth
 * reading once the same observable has been seen to move. So:
 *
 *   - before asserting that caret moves record NOTHING, the probe shows an
 *     EDIT recording something on the same counter, and measures the session's
 *     idle drift over a comparable interval (a live session publishes on its
 *     own account; the question is whether presence ADDS to that);
 *   - before asserting that continuous typing publishes no presence, it shows
 *     the presence publish counter going up on a caret move that comes to rest;
 *   - before asserting that B's cursor is gone after B exits, it shows the
 *     cursor was there.
 *
 * WHAT IS UNDER TEST (CROQUET_PRESENCE_DESIGN_2026-09-21.md)
 *
 *   layer (a)  a ring on the editor a participant is focused in
 *   layer (b)  their caret, drawn with setBookmark, inside it
 *   dwell      caret positions are published only once the caret RESTS
 *   ephemeral  presence_post is republished by the model without addEvent,
 *              so newspeakEvents does not grow
 *   no adoption  the old behaviour -- a remote selection applied as this
 *              client's OWN cursor, which is why everyone shared one cursor --
 *              must be gone: A's cursor stays where A put it
 *   view-exit  B leaving removes B's cursor everywhere, no heartbeat, no timeout
 */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'presence' + Math.floor(Date.now() / 1000);
const JS = process.argv[2] === 'js';
const PAGE = JS ? 'CroquetJSIDE-TEST.html?sessionId='
                : (process.env.NS_PAGE || 'croquetpsoup-test.html') + '?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const sleep = ms => new Promise(r => setTimeout(r, ms));
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
const live = [];
function bail(why) {
  console.log('BAIL: ' + why);
  for (const b of live) { console.log('  ' + b.tag + ' console tail: ' + b.log.slice(-6).join(' || ')); try { b.proc.kill(); } catch (e) {} }
  process.exit(1);
}
setTimeout(() => bail('overall deadline passed'), Number(process.env.DEADLINE_MS || 420000)).unref();
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-pres-'+tag+'-'+SESSION,'--no-first-run','--window-size=1400,1000','--disable-gpu','--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank'], {stdio:'ignore'});
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
async function typeChars(b, ch, n, cadence) {
  for (let i = 0; i < n; i++) {
    const t0 = Date.now();
    await b.send('Input.dispatchKeyEvent', { type: 'keyDown', text: ch, unmodifiedText: ch, key: ch });
    await b.send('Input.dispatchKeyEvent', { type: 'keyUp', key: ch });
    const rest = cadence - (Date.now() - t0); if (rest > 0) await sleep(rest);
  }
}

// Presence as A sees it: one entry per REMOTE participant.
const PRES = "(typeof nsPresence==='undefined')?'n/a':JSON.stringify(Array.from(nsPresence.entries()).map(function(e){return {view:e[0].slice(0,6),fid:e[1].fid,head:e[1].head,marks:e[1].marks.length}}))";
const CARETS = "String(document.querySelectorAll('.ns-presence-caret').length)";
const RINGS = `(function(){var w=${CM}.getWrapperElement();return String(w.style.boxShadow||'')})()`;
const EVENTS = "String(theModel.newspeakEvents.length)";
// Count publishes by channel. nsPublish is the single outbound funnel, so a
// presence publish and an ordinary one are distinguishable at one place.
const COUNTER = "(function(){if(window.__nsCount)return 'already';window.__nsCount={presence:0,other:0};var f=nsPublish;nsPublish=function(s,e,d){if(s==='nspresence_')window.__nsCount.presence++;else window.__nsCount.other++;return f(s,e,d)};return 'wrapped'})()";
const COUNTS = "JSON.stringify(window.__nsCount)";
/* Count the HOOKS themselves, not just publishes. "no presence was published"
   has two very different causes -- the hook never fired, or it fired and the
   dwell suppressed it -- and only this tells them apart. */
const HOOKC = "(function(){if(window.__hk)return 'already';window.__hk={caret:0,focus:0};var c=nsPresenceCaret,f=nsPresenceFocus;nsPresenceCaret=function(a,b){window.__hk.caret++;return c(a,b)};nsPresenceFocus=function(a,b){window.__hk.focus++;return f(a,b)};return 'wrapped'})()";
const HOOKS = "JSON.stringify(window.__hk)";

let fails = 0;
const ok = (name, pass, detail) => { if (!pass) fails++; console.log((pass ? '  PASS  ' : '  FAIL  ') + name + (detail ? '   ' + detail : '')); };
const info = (name, detail) => console.log('  ....  ' + name + '   ' + detail);

async function main() {
  console.log(PAGE);
  const A = await browser(9495, 'A'); await boot(A);
  await A.ev(click('Workspaces'));
  if (!await waitFor(A, "document.body.innerText.includes('Evaluate')", 40000)) bail('A never reached the workspace');
  const B = await browser(9496, 'B'); await boot(B);
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000)) bail('B never followed A to the workspace');
  await sleep(3000);

  if (await A.ev("typeof nsPresence") === 'undefined') bail('no nsPresence in the page: this build predates multiple cursors');
  const START = 'first line:\\nmiddle line\\nlast line:';
  await A.ev(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');cm.replaceSelection("${START}",null,'+input');return 1})()`);
  if (!await waitFor(B, `${CM}.getValue()==="${START}"`, 30000)) bail('B never received the starting text');
  await sleep(2000);
  await B.ev(COUNTER);
  await B.ev(HOOKC);

  // A parks its own cursor at the very start and never touches it again.
  await A.ev(`(function(){var cm=${CM};cm.focus();cm.setCursor(0,0);return 1})()`);
  await sleep(1500);
  const aCursorBefore = await A.ev(`JSON.stringify(${CM}.getCursor())`);

  /* ---- CONTROL: B's caret, at rest, reaches A ------------------------
     Moved with REAL key events. A bare cm.setCursor carries no origin, and
     isUserOrigin: requires a string one -- so a programmatic cursor move is
     deliberately not presence, and using one here would test nothing. The
     position is read back from B rather than assumed. */
  console.log('\n-- B moves its caret with real arrow keys and rests --');
  await B.ev(`(function(){var cm=${CM};cm.focus();cm.setCursor(0,0);return 1})()`);
  await sleep(800);
  for (let i = 0; i < 2; i++) await B.send('Input.dispatchKeyEvent', { type: 'rawKeyDown', key: 'ArrowDown', windowsVirtualKeyCode: 40, nativeVirtualKeyCode: 40 });
  for (let i = 0; i < 4; i++) await B.send('Input.dispatchKeyEvent', { type: 'rawKeyDown', key: 'ArrowRight', windowsVirtualKeyCode: 39, nativeVirtualKeyCode: 39 });
  await sleep(1500);                               // longer than the 300ms dwell
  const bCursor = JSON.parse(await B.ev(`JSON.stringify(${CM}.getCursor())`));
  info('B\'s own cursor after the arrows', JSON.stringify(bCursor));
  info('B\'s publish counts', await B.ev(COUNTS));

  const arrived = await waitFor(A, "typeof nsPresence!=='undefined' && nsPresence.size>0", 20000);
  if (!arrived) {
    // Bisect before giving up: did B publish at all, or did A fail to receive?
    const c = JSON.parse(await B.ev(COUNTS));
    console.log('  DIAGNOSIS: B presence publishes = ' + c.presence + ', other = ' + c.other);
    console.log('  DIAGNOSIS: B nsPresenceFocus is ' + await B.ev("typeof nsPresenceFocus"));
    console.log('  DIAGNOSIS: A nsPresence is ' + await A.ev("typeof nsPresence")
                + ', A nsEditors size = ' + await A.ev("String(nsEditors.size)"));
    console.log(c.presence > 0 ? '  => B PUBLISHED; the failure is delivery or A-side handling.'
                               : '  => B PUBLISHED NOTHING; the failure is the publish hook.');
  }
  ok('CONTROL: B\'s caret reaches A at all', arrived, await A.ev(PRES));
  if (!arrived) bail('nothing was delivered; every absence below would be meaningless');

  const pres = JSON.parse(await A.ev(PRES));
  ok('B\'s caret is where B actually put it',
     pres.length === 1 && pres[0].head && pres[0].head.line === bCursor.line && pres[0].head.ch === bCursor.ch,
     'A sees ' + JSON.stringify(pres.map(p => p.head)) + ', B is at ' + JSON.stringify(bCursor));
  ok('LAYER (b): a caret is DRAWN in A\'s editor', await A.ev(CARETS) !== '0', 'carets=' + await A.ev(CARETS));
  ok('LAYER (a): A\'s editor is ringed for B', (await A.ev(RINGS)).includes('inset'), JSON.stringify(await A.ev(RINGS)));
  ok('NO ADOPTION: A\'s own cursor did not move', await A.ev(`JSON.stringify(${CM}.getCursor())`) === aCursorBefore,
     'before=' + aCursorBefore + ' after=' + await A.ev(`JSON.stringify(${CM}.getCursor())`));
  info('presence publishes by B so far', await B.ev(COUNTS));

  // ---- the caret costs the session no RECORDED event ------------------
  console.log('\n-- what a caret move records --');
  const idle0 = Number(await A.ev(EVENTS));
  await sleep(6000);
  const idleDrift = Number(await A.ev(EVENTS)) - idle0;
  info('idle drift over 6s (the session publishes on its own account)', idleDrift + ' event(s)');

  const before = Number(await A.ev(EVENTS));
  // '+move' is the origin CodeMirror's own cursor-movement commands carry, so
  // this exercises the same path the arrow keys above did, without driving five
  // positions by keystroke.
  for (const [l, c] of [[0, 3], [1, 5], [2, 2], [0, 8], [1, 1]]) {
    await B.ev(`(function(){var cm=${CM};cm.focus();var p=CodeMirror.Pos(${l},${c});cm.setSelection(p,p,{origin:'+move'});return 1})()`);
    await sleep(1100);                       // longer than the 300ms dwell
  }
  await sleep(1500);
  const recorded = Number(await A.ev(EVENTS)) - before;
  ok('5 caret moves RECORD nothing beyond idle drift', recorded <= idleDrift,
     recorded + ' recorded vs ' + idleDrift + ' idle');
  const cAfterMoves = JSON.parse(await B.ev(COUNTS));
  ok('CONTROL: those moves DID publish presence', cAfterMoves.presence >= 5, JSON.stringify(cAfterMoves));

  // CONTROL for the counter that just read "nothing": an edit records.
  const beforeEdit = Number(await A.ev(EVENTS));
  await B.ev(`(function(){var cm=${CM};cm.focus();cm.setCursor(0,11);return 1})()`);
  await sleep(600);
  await typeChars(B, 'x', 3, 120);
  await sleep(2500);
  ok('CONTROL: an EDIT does record', Number(await A.ev(EVENTS)) > beforeEdit,
     (Number(await A.ev(EVENTS)) - beforeEdit) + ' event(s)');

  // ---- dwell: continuous typing publishes no presence -----------------
  console.log('\n-- dwell: typing without pausing --');
  const cBefore = JSON.parse(await B.ev(COUNTS));
  const hBefore = JSON.parse(await B.ev(HOOKS));
  await typeChars(B, 'y', 20, 80);           // 1.6s of typing, no pause > 300ms
  const cDuring = JSON.parse(await B.ev(COUNTS));
  const hDuring = JSON.parse(await B.ev(HOOKS));
  info('caret hook calls during 20 keystrokes', hBefore.caret + ' -> ' + hDuring.caret);
  ok('CONTROL: typing DOES move the caret through the presence hook',
     hDuring.caret > hBefore.caret,
     'without this, "published nothing" below would be vacuous');
  ok('typing published NO presence while the caret kept moving',
     cDuring.presence === cBefore.presence,
     cBefore.presence + ' -> ' + cDuring.presence + ' over 20 keystrokes');
  await sleep(1500);                          // now let it rest
  const cRest = JSON.parse(await B.ev(COUNTS));
  ok('CONTROL: coming to rest published exactly one', cRest.presence === cDuring.presence + 1,
     cDuring.presence + ' -> ' + cRest.presence);

  // ---- view-exit: B leaves --------------------------------------------
  console.log('\n-- B leaves --');
  ok('CONTROL: B\'s cursor is on A before B goes', await A.ev(CARETS) !== '0', 'carets=' + await A.ev(CARETS));
  try { B.proc.kill(); } catch (e) {}
  const gone = await waitFor(A, "nsPresence.size===0", 60000);
  ok('B\'s presence record is dropped on view-exit', gone, 'presence=' + await A.ev(PRES));
  ok('B\'s drawn cursor is gone', await A.ev(CARETS) === '0', 'carets=' + await A.ev(CARETS));
  ok('B\'s ring is gone', !(await A.ev(RINGS)).includes('inset'), JSON.stringify(await A.ev(RINGS)));

  const divA = await A.ev('String(nsDivergences.length)');
  ok('NO DIVERGENCE REPORTED', divA === '0', 'A=' + divA);
  console.log('errors/warnings A: ' + A.log.length + (A.log.length ? '\n  ' + A.log.slice(-6).join('\n  ') : ''));
  console.log('==== ' + (fails ? fails + ' FAILED' : 'all passed') + ' ====');
  for (const b of live) { try { b.proc.kill(); } catch (e) {} }
  process.exit(fails ? 1 : 0);
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
