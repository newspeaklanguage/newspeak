/* How fast does the glue's shadow map grow?
 *
 * Since 2026-09-19 a CodeMirrorFragment's shadow CodeMirror.Doc is KEPT at
 * noticeDisposal (a shadow re-created later from the visible text of a client
 * that had typed by then took that client's own echo a second time - the
 * doubled chat draft in the late-join probe). The session summary recorded the
 * consequence as a known, knowingly-shipped defect: "one CodeMirror.Doc per
 * editor ever built", worst case an Ampleforth document, which rebuilds its
 * editors continuously.
 *
 * Before designing a sweep, measure. Adoption already drops the adopter's own
 * pre-adoption shadow (adoptCroquetIdentityFrom:), so a same-kind re-render
 * need not accumulate at all; the question is what actually happens on the
 * path that was called the worst case.
 *
 *   croquet-probes/run.sh shadow-census-probe.js
 *
 *   ROUNDS (6)        typing rounds in the document's live view
 *   CHARS (10)        characters per round
 *   TRIPS (3)         navigate away from the document and back, at the end
 *   NS_PAGE / NS_SNAPSHOT   as for ampleforth-sync-probe
 *
 * Reports nsShadows.size at every step. Flat across rounds means the retention
 * is bounded in practice and the "defect" is theoretical; a count that climbs
 * with the typing means it is real, and the slope is the budget a fix must beat.
 */
const { sleep, launchBrowser, waitFor } = require('./harness');

const SESSION = 'shadow' + Math.floor(Date.now() / 1000);
const PAGE = (process.env.NS_PAGE || 'croquetpsoup-test.html') + '?snapshot=' +
             (process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE-TEST.vfuel') + '&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION +
            '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const ROUNDS = Number(process.env.ROUNDS || 6);
const CHARS = Number(process.env.CHARS || 10);
const TRIPS = Number(process.env.TRIPS || 3);

const MOUSE = "['mousedown','mouseup','click'].forEach(function(t){T.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window}))})";
/* Click the last element whose own trimmed text is exactly the label. Not
   restricted by tag: Hopscotch renders controls as several kinds of node. */
const click = label =>
  `(function(){var m=Array.from(document.querySelectorAll('*')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});` +
  `if(!m.length)return 'NOBTN';var T=m[m.length-1];${MOUSE};return 'CLICKED'})()`;
/* Toolbar buttons are image buttons: the handler is on the img, not the
   titled wrapper, so clicking the wrapper does nothing (cost an early run). */
const clickTitle = t =>
  `(function(){var e=document.querySelector('[title=' + ${JSON.stringify(JSON.stringify(t))} + ']');` +
  `if(!e)return 'NOEL';var T=e.querySelector('img')||e;${MOUSE};return 'CLICKED'})()`;

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const LIVE = "document.querySelector('.self_ampleforth')";
const SHADOWS = "(typeof nsShadows==='undefined'?-1:nsShadows.size)";
const EDITORS = "document.querySelectorAll('.CodeMirror').length";
const PENDING = "(typeof nsPendingEdits==='undefined'?-1:nsPendingEdits.size)";
const EVENTS = "(typeof theModel==='undefined'||!theModel?-1:theModel.newspeakEvents.length)";
const OPEN_DOC = "ide browsing navigateTo: (ide documents DocumentSubject onModel: " +
                 "(ide documents freshDocumentNamed: #ProbeDoc initialText: 'Probe body.'))";

let B = null;
function bail(msg) {
  console.log('BAIL: ' + msg);
  if (B) B.logs.slice(-8).forEach(l => console.log('  ' + l.slice(0, 200)));
  if (B) try { B.proc.kill() } catch (e) {}
  process.exit(1);
}

async function census(label) {
  const s = await B.v(SHADOWS), e = await B.v(EDITORS), p = await B.v(PENDING), n = await B.v(EVENTS);
  console.log('  ' + label.padEnd(28) + 'shadows=' + String(s).padStart(4) +
              '  editors=' + String(e).padStart(3) + '  pending=' + p + '  events=' + n);
  return s;
}

/* Evaluate in the workspace: select all, replace as a USER edit, re-select
   (a render between the two collapses the selection), then Evaluate Selection. */
async function evaluate(src) {
  await B.v(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');` +
            `cm.replaceSelection(${JSON.stringify(src)},null,'+input');cm.execCommand('selectAll');return 1})()`);
  await sleep(1200);
  const r = await B.v(click('Evaluate Selection'));
  if (r === 'NOBTN') bail('no Evaluate Selection control in the workspace');
  await sleep(3000);
}

/* Real key events into the contenteditable live view, caret at the end, so the
   browser inserts the characters itself exactly as it does for a person. */
async function typeLive(ch, n) {
  await B.v(`(function(){var el=${LIVE};el.focus();var r=document.createRange();r.selectNodeContents(el);` +
            `r.collapse(false);var s=getSelection();s.removeAllRanges();s.addRange(r);return 1})()`);
  for (let i = 0; i < n; i++) {
    await B.send('Input.dispatchKeyEvent', { type: 'keyDown', text: ch, unmodifiedText: ch, key: ch });
    await B.send('Input.dispatchKeyEvent', { type: 'keyUp', key: ch });
    await sleep(120);
  }
  await sleep(2500);
}

async function main() {
  console.log('ROUNDS=' + ROUNDS + ' CHARS=' + CHARS + ' TRIPS=' + TRIPS + '  ' + PAGE);
  B = await launchBrowser({ port: Number(process.env.PORT || 9497), tag: 'shadow', session: SESSION });
  await B.navigate(URL);
  if (!await waitFor(B, "document.body && document.body.innerText.includes('Workspaces')", 240000))
    bail('never showed the home page');
  console.log('booted'); await sleep(5000);
  const base = await census('home, before anything');

  await B.v(click('Workspaces'));
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 40000)) bail('never reached the workspace');
  await sleep(2500);
  await census('workspace');

  await evaluate(OPEN_DOC);
  if (!await waitFor(B, `!!${LIVE}`, 20000)) bail('the document did not open');
  await sleep(3000);
  const opened = await census('document open');

  const marks = [];
  for (let r = 1; r <= ROUNDS; r++) {
    await typeLive('z', CHARS);
    marks.push(await census('after typing round ' + r));
  }

  /* Leaving the document disposes its editors; coming back builds new ones.
     This is the path noticeDisposal's kept shadow is about.

     Re-entry goes through the HISTORY page, NOT another freshDocumentNamed:.
     Evaluating the opener again would mint a genuinely new document with
     genuinely new editors, and counting those as leaked shadows would be a
     measurement of nothing (an earlier run of this probe did exactly that and
     reported a confident "~2 per visit"). */
  const trips = [];
  for (let t = 1; t <= TRIPS; t++) {
    if (await B.v(clickTitle('Return to home screen')) !== 'CLICKED') bail('no home button');
    if (!await waitFor(B, "document.body.innerText.includes('Workspaces')", 40000)) bail('home never reopened');
    await sleep(3000);
    await census('trip ' + t + ': home');

    if (await B.v(clickTitle('history')) !== 'CLICKED') bail('no history button');
    if (!await waitFor(B, "document.body.innerText.includes('ProbeDoc')", 30000))
      bail('the history page does not list ProbeDoc: ' +
           await B.v("document.body.innerText.replace(/\\s+/g,' ').trim().slice(0,300)"));
    await sleep(2000);
    let r = await B.v(click('Document ProbeDoc'));
    if (r === 'NOBTN') r = await B.v(click('ProbeDoc'));
    if (r === 'NOBTN') bail('no ProbeDoc entry to click on the history page');
    if (!await waitFor(B, `!!${LIVE}`, 30000)) bail('the document did not reopen on trip ' + t);
    await sleep(3000);
    trips.push(await census('trip ' + t + ': same document again'));
  }

  console.log('\nbaseline ' + base + ', document open ' + opened);
  console.log('after each typing round: ' + marks.join(' -> '));
  const typingGrowth = marks[marks.length - 1] - opened;
  console.log('growth across ' + ROUNDS + ' rounds of ' + CHARS + ' characters: ' + typingGrowth +
              ' shadow(s) for ' + (ROUNDS * CHARS) + ' keystrokes');
  console.log('after each away-and-back trip: ' + trips.join(' -> '));
  const tripDeltas = trips.map((x, i) => x - (i ? trips[i - 1] : marks[marks.length - 1]));
  console.log('growth per trip: ' + tripDeltas.join(', '));

  console.log('\nVERDICT');
  console.log('  typing: ' + (typingGrowth <= 1
    ? 'bounded - a live-view rebuild does NOT mint a shadow per keystroke.'
    : 'accumulating ' + (typingGrowth / (ROUNDS * CHARS)).toFixed(2) + ' shadows per keystroke.'));
  const tripAvg = tripDeltas.length ? tripDeltas.reduce((a, d) => a + d, 0) / tripDeltas.length : 0;
  console.log('  re-entry (same document, via history): ' + (tripAvg <= 0.5
    ? 'bounded - a disposed-and-rebuilt document reuses its shadows.'
    : 'accumulating ~' + tripAvg.toFixed(1) + ' shadows per visit.'));
  console.log('errors/warnings: ' + B.logs.filter(l => /error|warn/i.test(l)).length);
  try { B.proc.kill() } catch (e) {}
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
