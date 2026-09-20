/* What does a keystroke cost in an AMPLEFORTH DOCUMENT, as opposed to a code
 * editor?
 *
 * editor-cost-decompose-probe.js measured the WORKSPACE CODE EDITOR and found
 * two causes: the unbounded editor height defeating CodeMirror's viewport
 * virtualization, and the whole buffer being re-colorized on every keystroke
 * (3704 markText per key). Gilad's question: Ampleforth documents are not
 * colorized, so which of that carries over?
 *
 * A document is three different things and they must not be lumped together:
 *   - the LIVE view: a contenteditable div (.self_ampleforth). Not a CodeMirror
 *     at all. Each keystroke runs onkeyup="updateRawHTML()" -> updater ->
 *     scrubbedLiveViewSource (a DOMParser pass over the whole document) ->
 *     cm text:origin: -> updateFromRawView (rebuild of the AmpleforthFragment).
 *   - the RAW view: a CodeMirrorFragment holding the document's HTML, built by
 *     the same createVisual as every other editor, so cause 1 should apply.
 *   - the amplets inside the live view, which may themselves be editors.
 *
 * This probe reports, for a document of SIZE_KB, the per-key cost of typing in
 * the live view and in the raw view, the markText count per key in each (0
 * means nothing is colorized there), and the raw view's rendered-line count and
 * wrapper height (the cause-1 signature).
 *
 *   croquet-probes/run.sh document-cost-probe.js
 *
 *   SIZE_KB (100)  N (12 keys per step)
 *
 * Plain IDE: no Croquet, no reflector, one browser.
 */
const { sleep, launchBrowser, waitFor } = require('./harness');

const SESSION = 'doccost' + Math.floor(Date.now() / 1000);
const SIZE_KB = Number(process.env.SIZE_KB || 100);
const N = Number(process.env.N || 12);
const URL = 'http://localhost:8080/primordialsoup.html?snapshot=' +
            (process.env.NS_SNAPSHOT || 'HopscotchWebIDE-TEST.vfuel');

const MOUSE = "['mousedown','mouseup','click'].forEach(function(t){T.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window}))})";
const click = label =>
  `(function(){var m=Array.from(document.querySelectorAll('*')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});` +
  `if(!m.length)return 'NOBTN';var T=m[m.length-1];${MOUSE};return 'CLICKED'})()`;
const CLICK_CONTAINS = label => `(function(){var want=${JSON.stringify(label)};` +
  `var m=Array.from(document.querySelectorAll('*')).filter(function(e){var t=(e.innerText||'').trim();` +
  `return t.indexOf(want)>=0&&t.length<40&&e.children.length<3});` +
  `if(!m.length)return 'NOBTN';var T=m[m.length-1];${MOUSE};return 'CLICKED '+JSON.stringify((T.innerText||'').trim())})()`;
const CLICK_TITLE = t => `(function(){var e=document.querySelector('[title=' + ${JSON.stringify(JSON.stringify(t))} + ']');` +
  `if(!e)return 'NOEL';var T=e.querySelector('img')||e;${MOUSE};return 'CLICKED'})()`;
const TOOLTIPS = `(function(){return Array.from(document.querySelectorAll('[title]')).map(function(e){return e.getAttribute('title')}).slice(0,30).join(' | ')})()`;
const LABELS = `(function(){var out=[];Array.from(document.querySelectorAll('*')).forEach(function(e){` +
  `var t=(e.innerText||'').trim();if(t&&t.length<30&&e.children.length===0)out.push(t)});` +
  `return Array.from(new Set(out)).slice(0,40).join(' | ')})()`;
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const LIVE = "document.querySelector('.self_ampleforth')";
/* Build the body in NEWSPEAK, by doubling a paragraph with a block applied
   repeatedly: a single expression (the evaluator parses a doIt expression, not
   a statement sequence, so no temporaries), and no giant literal has to be
   typed into the workspace editor. Growing the document through the raw view
   instead would need the raw view to exist, which is what we are here to find
   out. */
const PARA = '<p>probe paragraph of document body text</p>';
function bigBody(kb) {
  let e = "'" + PARA + "'", n = PARA.length;
  while (n * 2 <= kb * 1024) { e = '([:s | s , s ] value: ' + e + ')'; n *= 2 }
  return { src: e, chars: n };
}
const BODY = bigBody(SIZE_KB);
const OPEN_DOC = "ide browsing navigateTo: (ide documents DocumentSubject onModel: " +
                 "(ide documents freshDocumentNamed: #CostDoc initialText: " + BODY.src + "))";

let B = null;
function bail(msg) {
  console.log('BAIL: ' + msg);
  if (B) B.logs.slice(-8).forEach(l => console.log('  ' + l.slice(0, 200)));
  if (B) try { B.proc.kill() } catch (e) {}
  process.exit(1);
}
const pct = (a, p) => a.length ? a[Math.min(a.length - 1, Math.floor(a.length * p))] : -1;

/* Hook markText on EVERY CodeMirror now on the page, so "is anything colorized
   here" is answered by counting rather than by reading code. */
const HOOK_ALL = `(function(){window.__mt=0;var n=0;` +
  `Array.from(document.querySelectorAll('.CodeMirror')).forEach(function(el){var cm=el.CodeMirror;` +
  `if(!cm||cm.__hooked)return;cm.__hooked=1;n++;var mt=cm.markText;` +
  `cm.markText=function(){window.__mt++;return mt.apply(this,arguments)}});return 'hooked '+n})()`;

const RAWSTATE = `(function(){var els=document.querySelectorAll('.CodeMirror');if(!els.length)return '(no raw view)';` +
  `var cm=els[els.length-1].CodeMirror;var w=cm.getWrapperElement();return JSON.stringify({` +
  `lines:cm.lineCount(),rendered:cm.display.view.length,lineEls:w.querySelectorAll('.CodeMirror-line').length,` +
  `wrapperH:Math.round(w.getBoundingClientRect().height),scrollbarStyle:String(cm.getOption('scrollbarStyle'))})})()`;

async function evaluate(src) {
  await B.v(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');` +
            `cm.replaceSelection(${JSON.stringify(src)},null,'+input');cm.execCommand('selectAll');return 1})()`);
  await sleep(1200);
  if (await B.v(click('Evaluate Selection')) === 'NOBTN') bail('no Evaluate Selection control');
  await sleep(3000);
}

/* Real key events. focusExpr puts the caret where the characters should go. */
async function typeRun(label, focusExpr) {
  const f = await B.v(focusExpr);
  if (f !== 1) { console.log('  ' + label.padEnd(30) + 'SKIPPED (' + f + ')'); return -1 }
  await B.v('window.__mt=0');
  await sleep(400);
  const cost = [], t0 = Date.now();
  for (let i = 0; i < N; i++) {
    const s0 = Date.now();
    await B.send('Input.dispatchKeyEvent', { type: 'keyDown', text: 'x', unmodifiedText: 'x', key: 'x' });
    await B.send('Input.dispatchKeyEvent', { type: 'keyUp', key: 'x' });
    cost.push(Date.now() - s0);
    const rest = 120 - (Date.now() - s0); if (rest > 0) await sleep(rest);
  }
  const took = Date.now() - t0, k = cost.slice().sort((x, y) => x - y), mt = await B.v('window.__mt');
  console.log('  ' + label.padEnd(30) + String(took).padStart(6) + 'ms total   median=' +
              String(pct(k, 0.5)).padStart(5) + '  p90=' + String(pct(k, 0.9)).padStart(5) +
              '  markText/key=' + (mt === undefined ? '?' : Math.round(mt / N)));
  return pct(k, 0.5);
}

const FOCUS_LIVE = `(function(){var el=${LIVE};if(!el)return 'no live view';el.focus();var r=document.createRange();` +
  `r.selectNodeContents(el);r.collapse(false);var s=getSelection();s.removeAllRanges();s.addRange(r);return 1})()`;
const FOCUS_RAW = `(function(){var els=document.querySelectorAll('.CodeMirror');if(!els.length)return 'no raw view';` +
  `var cm=els[els.length-1].CodeMirror;cm.focus();cm.setCursor(cm.lineCount(),0);return 1})()`;

async function main() {
  console.log('SIZE_KB=' + SIZE_KB + ' N=' + N + '  plain IDE, no Croquet; body built as ' + BODY.chars + ' chars');
  B = await launchBrowser({ port: Number(process.env.PORT || 9500), tag: 'doccost', session: SESSION });
  await B.navigate(URL);
  if (!await waitFor(B, "document.body && document.body.innerText.includes('Workspaces')", 240000))
    bail('never showed the home page');
  await sleep(4000);
  await B.v(click('Workspaces'));
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 40000)) bail('never reached the workspace');
  await sleep(3000);

  await evaluate(OPEN_DOC);
  if (!await waitFor(B, `!!${LIVE}`, 25000)) bail('the document did not open');
  await sleep(4000);
  console.log('document open. CodeMirrors on the page: ' + await B.v("document.querySelectorAll('.CodeMirror').length"));

  /* The raw view is collapsible and starts collapsed. An exact-text match on
     'Toggle Raw HTML' finds nothing (the control does not render as one element
     whose whole text is the label), so match on CONTAINS and report what was
     actually hit; if that fails too, print the candidates rather than guess. */
  if (await B.v("document.querySelectorAll('.CodeMirror').length") === 0) {
    /* The document page opens in VIEW mode: the editing chrome, and with it
       the raw-view toggle, is behind the toolbar's Edit button (an image
       button, so it has a tooltip and no text). */
    console.log('  click Edit: ' + await B.v(CLICK_TITLE('Edit')));
    await sleep(6000);
    console.log('  toggle raw view: ' + await B.v(CLICK_CONTAINS('Toggle Raw')));
    await sleep(6000);
    if (await B.v("document.querySelectorAll('.CodeMirror').length") === 0)
      console.log('  still no raw view. text controls: ' + await B.v(LABELS) +
                  '\n  tooltips: ' + await B.v(TOOLTIPS));
  }
  console.log('  raw view: ' + await B.v(RAWSTATE));

  /* Grow the document through its own pipeline: put a large HTML body into the
     raw view as a user edit and let updateFromRawView rebuild the live view. */
  const grew = await B.v(`(function(){var els=document.querySelectorAll('.CodeMirror');if(!els.length)return 'no raw view';` +
    `var cm=els[els.length-1].CodeMirror;var p='<p>probe paragraph of document body text</p>';` +
    `var body=p.repeat(Math.ceil(${SIZE_KB}*1024/p.length));var v=cm.getValue();` +
    `var i=v.indexOf('</div>',v.indexOf('ampleforthDocumentBody'));` +
    `if(i<0)return 'no document body div';cm.focus();` +
    `cm.replaceRange(body,cm.posFromIndex(i),cm.posFromIndex(i),'+input');return cm.getValue().length})()`);
  console.log('raw view after growing: ' + grew + ' chars');
  await sleep(20000);
  console.log('  raw view: ' + await B.v(RAWSTATE));
  console.log('  live view text length: ' + await B.v(`(${LIVE}?${LIVE}.innerText.length:-1)`));
  console.log('  ' + await B.v(HOOK_ALL));

  console.log('\n(warm-up in the live view, discarded)');
  await typeRun('warm-up', FOCUS_LIVE);

  console.log('\nwhere typed                       total      per key            colorizing');
  const live = await typeRun('LIVE view (contenteditable)', FOCUS_LIVE);
  await sleep(3000);
  const raw = await typeRun('RAW view (CodeMirror)', FOCUS_RAW);

  console.log('\nper-key median, ms:  live=' + live + '  raw=' + raw);
  console.log('page errors: ' + B.logs.filter(l => /error/i.test(l)).length);
  try { B.proc.kill() } catch (e) {}
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
