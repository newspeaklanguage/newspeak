/* WHY is a large editor 51x slower inside the IDE than a bare CodeMirror on the
   same page? (typing-cost-control.js SIZE_KB=300 BARE=1, 2026-09-19: 1593ms
   per key against 31ms, with no Croquet loaded at all.)
 *
 * Hypothesis: CodeMirror only virtualizes its viewport when it has a bounded
 * height to scroll inside. CodeMirrorFragment>>createVisual builds every editor
 * with `scrollbarStyle: 'null'` and then sets the wrapper's height to 'unset',
 * so the editor grows to fit its whole content inside the Hopscotch flow
 * layout - and CodeMirror therefore renders and re-measures EVERY line on every
 * change. The control's bare editor lives in a fixed 500px div, so it renders
 * about a screenful. That would explain the hot functions exactly
 * (updateHeightsInViewport, iterN, findViewIndex) and why Croquet, the shadow
 * machinery and the colorizer all profile as innocent.
 *
 * This probe tests that causally, A/B/A on the SAME editor, so nothing differs
 * but the height constraint:
 *
 *   A  as the IDE builds it            (height unset, scrollbarStyle null)
 *   B  cm.setSize(null, 500) + native scrollbars + refresh
 *   A' constraint removed again
 *
 * Reports rendered line count and per-key cost at each step. If B collapses the
 * cost and A' brings it back, the height constraint IS the cause and the fix is
 * one option in createVisual - not the colorizer, not the sync layer. A' also
 * rules out warm-up: a JIT that had simply grown warm would not get slow again.
 *
 *   croquet-probes/run.sh editor-viewport-probe.js
 *
 *   SIZE_KB (300)  N (12 keys per step)  HEIGHT (500)
 */
const { sleep, launchBrowser, waitFor } = require('./harness');

const SESSION = 'viewport' + Math.floor(Date.now() / 1000);
const SIZE_KB = Number(process.env.SIZE_KB || 300);
const N = Number(process.env.N || 12);
const HEIGHT = Number(process.env.HEIGHT || 500);
/* The PLAIN IDE: no Croquet, no reflector, one browser. */
const URL = 'http://localhost:8080/primordialsoup.html?snapshot=' +
            (process.env.NS_SNAPSHOT || 'HopscotchWebIDE-TEST.vfuel');

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const MOUSE = "['mousedown','mouseup','click'].forEach(function(t){T.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window}))})";
const click = label =>
  `(function(){var m=Array.from(document.querySelectorAll('*')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});` +
  `if(!m.length)return 'NOBTN';var T=m[m.length-1];${MOUSE};return 'CLICKED'})()`;

/* What CodeMirror is actually rendering: display.view is its list of rendered
   line views, viewFrom/viewTo the range it believes it must cover. With a
   bounded height these stay near a screenful however long the document is. */
const RENDERED = `(function(){var cm=${CM};var w=cm.getWrapperElement();return JSON.stringify({` +
  `lines:cm.lineCount(),rendered:cm.display.view.length,viewFrom:cm.display.viewFrom,viewTo:cm.display.viewTo,` +
  `lineEls:w.querySelectorAll('.CodeMirror-line').length,` +
  `wrapperH:Math.round(w.getBoundingClientRect().height),scrollbarStyle:String(cm.getOption('scrollbarStyle')),` +
  `viewportMargin:String(cm.getOption('viewportMargin'))})})()`;

let B = null;
function bail(msg) {
  console.log('BAIL: ' + msg);
  if (B) B.logs.slice(-8).forEach(l => console.log('  ' + l.slice(0, 200)));
  if (B) try { B.proc.kill() } catch (e) {}
  process.exit(1);
}
const pct = (a, p) => a.length ? a[Math.min(a.length - 1, Math.floor(a.length * p))] : -1;

async function typeRun(label) {
  await B.v(`(function(){var cm=${CM};cm.focus();cm.setCursor(cm.lineCount(),0);return 1})()`);
  await sleep(500);
  const cost = [], t0 = Date.now();
  for (let i = 0; i < N; i++) {
    const s0 = Date.now();
    await B.send('Input.dispatchKeyEvent', { type: 'keyDown', text: 'x', unmodifiedText: 'x', key: 'x' });
    await B.send('Input.dispatchKeyEvent', { type: 'keyUp', key: 'x' });
    cost.push(Date.now() - s0);
    const rest = 100 - (Date.now() - s0); if (rest > 0) await sleep(rest);
  }
  const took = Date.now() - t0, k = cost.slice().sort((x, y) => x - y);
  console.log('  ' + label.padEnd(34) + N + ' keys in ' + String(took).padStart(6) + 'ms   per key: median=' +
              String(pct(k, 0.5)).padStart(5) + ' p90=' + String(pct(k, 0.9)).padStart(5) + ' max=' + k[k.length - 1]);
  return pct(k, 0.5);
}

async function main() {
  console.log('SIZE_KB=' + SIZE_KB + ' N=' + N + ' HEIGHT=' + HEIGHT + '  plain IDE, no Croquet');
  B = await launchBrowser({ port: Number(process.env.PORT || 9498), tag: 'viewport', session: SESSION });
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

  console.log('\nA  as the IDE builds it');
  console.log('  ' + await B.v(RENDERED));
  const a = await typeRun('IDE default (height unset)');

  console.log('\nB  same editor, bounded height + native scrollbars');
  await B.v(`(function(){var cm=${CM};cm.setOption('scrollbarStyle','native');cm.setSize(null,${HEIGHT});` +
            `cm.getWrapperElement().style.height='${HEIGHT}px';cm.refresh();return 1})()`);
  await sleep(6000);
  console.log('  ' + await B.v(RENDERED));
  const b = await typeRun('bounded to ' + HEIGHT + 'px');

  console.log("\nA' constraint removed again (rules out warm-up)");
  await B.v(`(function(){var cm=${CM};cm.setOption('scrollbarStyle','null');cm.setSize(null,'auto');` +
            `cm.getWrapperElement().style.height='unset';cm.refresh();return 1})()`);
  await sleep(6000);
  console.log('  ' + await B.v(RENDERED));
  const a2 = await typeRun('back to height unset');

  console.log('\nper-key median, ms:  A=' + a + '   B=' + b + "   A'=" + a2);
  const speedup = b > 0 ? (a / b) : 0;
  console.log('bounding the height is ' + speedup.toFixed(1) + 'x faster; removing it again costs ' +
              (b > 0 ? (a2 / b).toFixed(1) : '?') + 'x');
  console.log('\nVERDICT: ' + (b > 0 && a / b >= 3 && a2 / b >= 3
    ? 'CONFIRMED - the unbounded editor height is the cause. CodeMirror cannot\n' +
      '  virtualize without a scroller, so it renders and re-measures every line of\n' +
      '  the document on every change. The fix belongs in CodeMirrorFragment>>createVisual.'
    : 'NOT confirmed by this run - read the rendered counts above before theorizing.'));
  console.log('page errors: ' + B.logs.filter(l => /error/i.test(l)).length);
  try { B.proc.kill() } catch (e) {}
}
main().catch(e => bail('probe threw: ' + (e && e.stack || e)));
