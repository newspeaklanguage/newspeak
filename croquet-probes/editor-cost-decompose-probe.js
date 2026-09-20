/* What makes an IDE editor 51x slower than a bare CodeMirror on the same page?
 * (typing-cost-control.js SIZE_KB=300 BARE=1: 1593ms/key vs 31ms, no Croquet.)
 *
 * editor-viewport-probe.js established the first factor and its mechanism
 * beyond doubt: CodeMirrorFragment builds every editor with
 * `scrollbarStyle: 'null'` and the wrapper height set to 'unset', so CodeMirror
 * has no scroller to virtualize inside and renders EVERY line - at 300KB,
 * 3703 line elements in the DOM and a wrapper 125893px tall, against 19 lines
 * when the height is bounded. But bounding it only reached ~545ms/key, still
 * 17x the bare floor, so the viewport is not the whole story.
 *
 * This probe peels the differences off ONE editor, one at a time, measuring
 * after each, and counts the per-keystroke work the IDE does that a bare
 * editor does not:
 *
 *   warm  discarded - the first run after a 300KB insert pays one-off layout
 *   A     as the IDE builds it
 *   B     + bounded height, native scrollbars   (viewport virtualization back)
 *   C     + lineWrapping off                    (IDE sets it; the bare control does not)
 *   D     + our change handlers detached        (colorizer, presenter, Hopscotch reactivity)
 *   BARE  a fresh CodeMirror on the same page, same text: the floor
 *
 * Each step also reports markText calls per keystroke, which is the colorizer
 * re-marking the whole document, and a CPU bucket summary. Whichever step
 * collapses the cost names the cause.
 *
 *   croquet-probes/run.sh editor-cost-decompose-probe.js
 *
 *   SIZE_KB (300)  N (12 keys per step)  HEIGHT (500)
 */
const { sleep, launchBrowser, waitFor } = require('./harness');

const SESSION = 'decomp' + Math.floor(Date.now() / 1000);
const SIZE_KB = Number(process.env.SIZE_KB || 300);
const N = Number(process.env.N || 12);
const HEIGHT = Number(process.env.HEIGHT || 500);
const URL = 'http://localhost:8080/primordialsoup.html?snapshot=' +
            (process.env.NS_SNAPSHOT || 'HopscotchWebIDE-TEST.vfuel');

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const MOUSE = "['mousedown','mouseup','click'].forEach(function(t){T.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window}))})";
const click = label =>
  `(function(){var m=Array.from(document.querySelectorAll('*')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});` +
  `if(!m.length)return 'NOBTN';var T=m[m.length-1];${MOUSE};return 'CLICKED'})()`;

const RENDERED = cm => `(function(){var cm=${cm};var w=cm.getWrapperElement();return JSON.stringify({` +
  `rendered:cm.display.view.length,lineEls:w.querySelectorAll('.CodeMirror-line').length,` +
  `wrapperH:Math.round(w.getBoundingClientRect().height),wrap:!!cm.getOption('lineWrapping'),` +
  `handlers:(cm._handlers&&cm._handlers.change?cm._handlers.change.length:-1)})})()`;

const DETACH = `(function(){var cm=${CM};var h=cm._handlers;window.__saved={};` +
  `['change','changes','beforeChange','cursorActivity','beforeSelectionChange','keydown'].forEach(function(k){` +
  `if(h[k]){window.__saved[k]=h[k].slice();h[k].length=0}});return Object.keys(window.__saved).join(',')})()`;
const REATTACH = `(function(){var cm=${CM};var h=cm._handlers;Object.keys(window.__saved).forEach(function(k){` +
  `h[k]=window.__saved[k]});return 1})()`;

let B = null;
function bail(msg) {
  console.log('BAIL: ' + msg);
  if (B) B.logs.slice(-8).forEach(l => console.log('  ' + l.slice(0, 200)));
  if (B) try { B.proc.kill() } catch (e) {}
  process.exit(1);
}
const pct = (a, p) => a.length ? a[Math.min(a.length - 1, Math.floor(a.length * p))] : -1;

/* Count the editor's own markText calls, so the colorizer's whole-document
   re-marking is visible per step rather than inferred. */
const countFrom = cm => `(function(){var cm=${cm};if(cm.__counted)return 'already';cm.__counted=1;` +
  `window.__mt=0;var mt=cm.markText;cm.markText=function(){window.__mt++;return mt.apply(this,arguments)};return 'hooked'})()`;

async function typeRun(label, cmExpr, profile) {
  await B.v(`(function(){var cm=${cmExpr};cm.focus();cm.setCursor(cm.lineCount(),0);return 1})()`);
  await B.v('window.__mt=0');
  await sleep(400);
  if (profile) { await B.send('Profiler.enable'); await B.send('Profiler.setSamplingInterval', { interval: 1000 }); await B.send('Profiler.start') }
  const cost = [], t0 = Date.now();
  for (let i = 0; i < N; i++) {
    const s0 = Date.now();
    await B.send('Input.dispatchKeyEvent', { type: 'keyDown', text: 'x', unmodifiedText: 'x', key: 'x' });
    await B.send('Input.dispatchKeyEvent', { type: 'keyUp', key: 'x' });
    cost.push(Date.now() - s0);
    const rest = 100 - (Date.now() - s0); if (rest > 0) await sleep(rest);
  }
  const took = Date.now() - t0, k = cost.slice().sort((x, y) => x - y);
  const mt = await B.v('window.__mt');
  let buckets = '';
  if (profile) {
    const prof = await B.send('Profiler.stop');
    buckets = '   ' + summarize(prof.profile);
  }
  console.log('  ' + label.padEnd(30) + String(took).padStart(6) + 'ms total   median=' +
              String(pct(k, 0.5)).padStart(5) + '  p90=' + String(pct(k, 0.9)).padStart(5) +
              '  markText/key=' + (mt === undefined ? '?' : Math.round(mt / N)) + buckets);
  return pct(k, 0.5);
}

/* Roll the profile's self-times up by source file, which is enough to tell
   CodeMirror's own work from the Newspeak VM's from ours. */
function summarize(profile) {
  const byId = new Map(); (profile.nodes || []).forEach(n => byId.set(n.id, n));
  const self = new Map();
  const total = (profile.timeDeltas || []).reduce((a, d) => a + Math.max(0, d), 0) / 1000;
  (profile.samples || []).forEach((sid, i) => {
    const n = byId.get(sid); if (!n) return;
    const url = (n.callFrame && n.callFrame.url) || '';
    const b = /codemirror/i.test(url) ? 'codemirror'
      : /\.wasm/i.test(url) ? 'newspeak-vm'
      : /primordialsoup|croquetpsoup/i.test(url) ? 'glue'
      : url ? 'other-js' : (n.callFrame && n.callFrame.functionName) || '(program)';
    const d = Math.max(0, (profile.timeDeltas || [])[i] || 0) / 1000;
    self.set(b, (self.get(b) || 0) + d);
  });
  return [...self.entries()].sort((a, b) => b[1] - a[1]).slice(0, 4)
    .map(([b, ms]) => b + ' ' + Math.round(100 * ms / (total || 1)) + '%').join(', ');
}

async function main() {
  console.log('SIZE_KB=' + SIZE_KB + ' N=' + N + ' HEIGHT=' + HEIGHT + '  plain IDE, no Croquet');
  B = await launchBrowser({ port: Number(process.env.PORT || 9499), tag: 'decomp', session: SESSION });
  await B.navigate(URL);
  if (!await waitFor(B, "document.body && document.body.innerText.includes('Workspaces')", 240000))
    bail('never showed the home page');
  await sleep(4000);
  await B.v(click('Workspaces'));
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 40000)) bail('never reached the workspace');
  await sleep(3000);

  const filled = await B.v(`(function(){var cm=${CM};cm.focus();var line='(* '+'x'.repeat(76)+' *)\\n';` +
    `var pad=line.repeat(Math.ceil(${SIZE_KB}*1024/line.length));cm.execCommand('selectAll');` +
    `cm.replaceSelection(pad,null,'+input');return cm.getValue().length})()`);
  console.log('buffer: ' + filled + ' chars');
  await sleep(12000);
  console.log('hook markText: ' + await B.v(countFrom(CM)));

  console.log('\n(warm-up run, discarded)');
  await typeRun('warm-up', CM, false);

  console.log('\nstate                              total      per key            work');
  console.log('  ' + await B.v(RENDERED(CM)));
  const a = await typeRun('A  as the IDE builds it', CM, true);

  /* A2: the SHIPPED configuration (unbounded) with only the colorizing
     handlers gone. Cause 1 is deferred, so this - not the C-to-D step - is what
     fixing cause 2 alone would actually buy. Handlers are restored after. */
  await B.v(DETACH);
  await sleep(3000);
  const a2 = await typeRun('A2 unbounded, handlers off', CM, true);
  await B.v(REATTACH);
  await sleep(3000);

  await B.v(`(function(){var cm=${CM};cm.setOption('scrollbarStyle','native');cm.setSize(null,${HEIGHT});` +
            `cm.getWrapperElement().style.height='${HEIGHT}px';cm.refresh();return 1})()`);
  await sleep(6000);
  console.log('  ' + await B.v(RENDERED(CM)));
  const b = await typeRun('B  + bounded height', CM, true);

  await B.v(`(function(){var cm=${CM};cm.setOption('lineWrapping',false);cm.refresh();return 1})()`);
  await sleep(5000);
  console.log('  ' + await B.v(RENDERED(CM)));
  const c = await typeRun('C  + lineWrapping off', CM, true);

  /* Detach OUR change handlers: everything the IDE runs per keystroke -
     colorizer, presenter response, Hopscotch reactivity - without touching
     CodeMirror's own internals. Restored afterwards. */
  await B.v(DETACH);
  await sleep(3000);
  console.log('  ' + await B.v(RENDERED(CM)));
  const d = await typeRun('D  + our handlers detached', CM, true);
  await B.v(REATTACH);

  /* The floor, same page, same text, built the way the control builds it. */
  await B.v(`(function(){var d=document.createElement('div');` +
    `d.style.cssText='position:fixed;left:0;top:0;width:900px;height:${HEIGHT}px;z-index:99999;background:white';` +
    `document.body.appendChild(d);var line='(* '+'x'.repeat(76)+' *)\\n';` +
    `window.__bare=CodeMirror(d,{value:line.repeat(Math.ceil(${SIZE_KB}*1024/line.length)),lineNumbers:false});return 1})()`);
  await sleep(6000);
  await B.v(countFrom('window.__bare'));
  console.log('  ' + await B.v(RENDERED('window.__bare')));
  const bare = await typeRun('BARE  the floor', 'window.__bare', true);

  console.log('\nper-key median, ms:  A=' + a + '  A2=' + a2 + '  B=' + b + '  C=' + c + '  D=' + d + '  BARE=' + bare);
  console.log('  colorizing alone, in the SHIPPED config: ' + (a - a2) + 'ms/key of ' + a +
              '  (' + Math.round(100 * (a - a2) / (a || 1)) + '% of the total)');
  const step = (from, to, name) => console.log('  ' + name.padEnd(26) + (from - to >= 0 ? '-' : '+') +
    String(Math.abs(from - to)).padStart(5) + 'ms' + (from > 0 ? '   (' + (to / from).toFixed(2) + 'x)' : ''));
  step(a, b, 'bounding the height');
  step(b, c, 'lineWrapping off');
  step(c, d, 'detaching our handlers');
  step(d, bare, 'remaining vs bare');
  console.log('page errors: ' + B.logs.filter(l => /error/i.test(l)).length);
  try { B.proc.kill() } catch (e) {}
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
