/* Does drawing a remote cursor echo?
 *
 * Multiple cursors (2026-09-21) will draw every OTHER client's caret and
 * selection into this client's editor. In CodeMirror 5 the tools for that are
 * markText (a styled range) and setBookmark (a collapsed position carrying a
 * DOM widget). Both touch the editor. The editor publishes what happens to it.
 * So before designing on top of them, the question is whether a decoration is
 * visible to the publish hooks -- because if it is, every drawn cursor is an
 * event, every event is another client's drawn cursor, and the thing builds a
 * feedback loop out of itself.
 *
 * The suspicion is not idle. HopscotchForCroquet's croquetOrigin machinery
 * (~:294) exists because CodeMirror delivers some signals -- beforeSelectionChange
 * above all -- only when its operation or display update ENDS, after the
 * reflecting flag has been put back, and the resulting echo of every applied
 * event stormed the reflector past its send rate limit. A bookmark widget is a
 * DOM insertion that forces measurement. That is exactly the shape of thing
 * that arrived late last time.
 *
 * WHAT IS MEASURED
 *
 * nsPublish is the single outbound funnel (out/croquetpsoup.js:2409): every
 * synchronized event leaves through it. The probe wraps it on client A and
 * counts. Counting inside the client under test is the weaker kind of
 * measurement, so B is watched too: B's editor must not move.
 *
 * A count of zero means nothing on its own -- a counter that never fires reads
 * zero whatever happens. So the probe first shows the SAME counter going up on
 * two things known to publish: a user-origin edit, and a user-origin selection
 * move with no edit (the closer control, since the thing under test is also
 * selection-shaped). Only then is a zero worth reading. It also takes an idle
 * baseline, because a live session publishes on its own account and the
 * question is whether decorations add to that, not whether the session is
 * silent.
 *
 * Two further questions, cheap to ask while a session is up:
 *   - do marks TRACK edits? If CodeMirror maintains their positions across a
 *     replaceRange, remote cursors need no per-keystroke recomputation, which
 *     matters given what per-keystroke whole-document work cost us before
 *     (the editor was 87x a bare one).
 *   - what does mark churn COST on a large buffer?
 *
 * Run:
 *   croquet-probes/run.sh remote-cursor-echo-probe.js
 *
 * Needs the front door on :8080 and the reflector on :9090.
 */
const { sleep, launchBrowser, bootIDE, makeChecker } = require('./harness');

const SESSION = 'rcursor' + Math.floor(Date.now() / 1000);
const SNAPSHOT = process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE.vfuel';
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=' + SNAPSHOT
  + '&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files';

setTimeout(() => { console.log('BAIL: overall deadline passed'); process.exit(1); },
  Number(process.env.DEADLINE_MS || 480000)).unref();

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";

/* Wrap the outbound funnel. nsPublish is a top-level function declaration in a
   classic script, so the global binding IS window.nsPublish and its internal
   callers resolve it at call time -- reassigning here is seen by them. */
const HOOK = `(function(){
  if (window.__nsPubs) return 'ALREADY';
  if (typeof window.nsPublish !== 'function') return 'NOFUNC';
  window.__nsPubs = [];
  var orig = window.nsPublish;
  window.nsPublish = function(scope, spec, data){
    try { window.__nsPubs.push(String(scope) + ' ' + String(spec)) } catch (e) {}
    return orig.apply(this, arguments);
  };
  return 'HOOKED';
})()`;

const RESET = "(function(){window.__nsPubs=[];return 1})()";
/* Total, and the editor's own. Both are reported: the cm count is the answer,
   the total says how much unrelated traffic the session carries. */
const COUNTS = `(function(){
  var all = window.__nsPubs || [];
  var cm = all.filter(function(s){ return s.indexOf('nscodemirror') === 0 });
  return JSON.stringify({total: all.length, cm: cm.length, sample: all.slice(0, 6)});
})()`;

const SELSTATE = `(function(){var cm=${CM};return JSON.stringify({
  len: cm.getValue().length,
  sel: cm.listSelections().map(function(r){return r.anchor.line+':'+r.anchor.ch+'-'+r.head.line+':'+r.head.ch})
})})()`;

async function counts(b) { return JSON.parse(await b.v(COUNTS)); }

async function main() {
  const t = makeChecker();

  console.log('booting A...');
  const A = await launchBrowser({ port: 9481, tag: 'rca', session: SESSION });
  const aUp = await bootIDE(A, URL);
  t.check('client A booted to a workspace', aUp);
  if (!aUp) { t.summary(); A.proc.kill(); return }

  console.log('booting B...');
  const B = await launchBrowser({ port: 9482, tag: 'rcb', session: SESSION });
  const bUp = await bootIDE(B, URL);
  t.check('client B booted to a workspace', bUp);
  if (!bUp) { t.summary(); A.proc.kill(); B.proc.kill(); return }
  await sleep(3000);

  const hooked = await A.v(HOOK);
  t.check('nsPublish hooked on A', hooked === 'HOOKED', 'got ' + hooked);
  if (hooked !== 'HOOKED') { t.summary(); A.proc.kill(); B.proc.kill(); return }

  /* --- noise floor: what a live session publishes unprompted --- */
  await A.v(RESET);
  await sleep(4000);
  const idle = await counts(A);
  console.log('idle 4s baseline:', JSON.stringify(idle));

  /* --- control 1: a user edit must publish (does the counter work at all?) --- */
  await A.v(RESET);
  await A.v(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');` +
            `cm.replaceSelection('probe text line one\\nline two here', null, '+input');return 1})()`);
  await sleep(2500);
  const afterEdit = await counts(A);
  t.check('CONTROL: a user-origin edit publishes', afterEdit.cm > 0,
          JSON.stringify(afterEdit));

  /* --- control 2: a user selection move, no edit. The closest control there
         is, because a decoration is also selection-shaped. --- */
  await A.v(RESET);
  await A.v(`(function(){var cm=${CM};cm.focus();` +
            `cm.setSelection({line:0,ch:0},{line:0,ch:5},{origin:'*mouse'});return 1})()`);
  await sleep(2500);
  const afterSel = await counts(A);
  t.check('CONTROL: a user-origin selection move publishes', afterSel.cm > 0,
          JSON.stringify(afterSel));

  const controlsOk = afterEdit.cm > 0 && afterSel.cm > 0;
  if (!controlsOk)
    console.log('\n*** controls did not fire: a zero below would prove NOTHING ***\n');

  const bBefore = await B.v(SELSTATE);

  /* --- the question: decorations, of both kinds --- */
  await A.v(RESET);
  const drew = await A.v(`(function(){var cm=${CM};
    window.__marks = [];
    for (var i = 0; i < 3; i++) {
      window.__marks.push(cm.markText({line:0,ch:i},{line:0,ch:i+3},
        {className:'ns-remote-sel-'+i, title:'client '+i}));
      var w = document.createElement('span');
      w.className = 'ns-remote-caret';
      w.style.cssText = 'border-left:2px solid hsl('+(i*120)+',70%,50%);height:1em;display:inline-block;margin-left:-1px';
      window.__marks.push(cm.setBookmark({line:0,ch:i+5},{widget:w}));
    }
    return window.__marks.length})()`);
  t.check('6 decorations created on A', drew === 6, 'got ' + drew);
  await sleep(3000);
  const afterDraw = await counts(A);
  t.check('drawing decorations publishes nothing', afterDraw.cm === 0,
          JSON.stringify(afterDraw));

  /* --- and removing them --- */
  await A.v(RESET);
  await A.v("(function(){window.__marks.forEach(function(m){m.clear()});return 1})()");
  await sleep(3000);
  const afterClear = await counts(A);
  t.check('clearing decorations publishes nothing', afterClear.cm === 0,
          JSON.stringify(afterClear));

  /* --- far end: B must not have moved --- */
  const bAfter = await B.v(SELSTATE);
  t.check('FAR END: B\'s editor unchanged by A\'s decorations', bBefore === bAfter,
          'before ' + bBefore + ' after ' + bAfter);

  /* --- do marks track edits, or must we recompute? --- */
  const tracked = await A.v(`(function(){var cm=${CM};
    var bm = cm.setBookmark({line:1,ch:4});
    var before = bm.find();
    cm.replaceRange('INSERTED ', {line:1,ch:0}, {line:1,ch:0}, 'croquet');
    var after = bm.find();
    bm.clear();
    return JSON.stringify({before: before && before.ch, after: after && after.ch})})()`);
  const tr = JSON.parse(tracked);
  t.check('marks track edits without recomputation', tr.after === tr.before + 9,
          'ch ' + tr.before + ' -> ' + tr.after + ' after a 9-char insert before it');

  /* --- cost of churn on a large buffer (reported, not asserted) --- */
  await A.v(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');` +
            `cm.replaceSelection('(* '+'x'.repeat(120000)+' *)', null, '+input');return 1})()`);
  await sleep(6000);
  const cost = await A.v(`(function(){var cm=${CM};
    var n = cm.getValue().length;
    var t0 = performance.now();
    for (var i = 0; i < 100; i++) {
      var m = cm.markText({line:0,ch:0},{line:0,ch:8},{className:'ns-remote-sel-0'});
      var w = document.createElement('span'); w.style.cssText='border-left:2px solid red;height:1em;display:inline-block';
      var b = cm.setBookmark({line:0,ch:12},{widget:w});
      m.clear(); b.clear();
    }
    return JSON.stringify({docChars: n, ms: Math.round(performance.now() - t0)})})()`);
  console.log('churn cost (100 create+clear cycles):', cost);

  /* --- did the big edit plus churn provoke anything? --- */
  await A.v(RESET);
  await sleep(3000);
  const settled = await counts(A);
  console.log('post-churn idle:', JSON.stringify(settled));

  const errsA = A.logs.filter(l => l.startsWith('[error]'));
  const errsB = B.logs.filter(l => l.startsWith('[error]'));
  t.check('no console errors on A', errsA.length === 0, errsA.slice(0, 3).join(' | '));
  t.check('no console errors on B', errsB.length === 0, errsB.slice(0, 3).join(' | '));

  t.summary();
  A.proc.kill(); B.proc.kill();
}

main().catch(e => { console.error(e); process.exit(1) });
