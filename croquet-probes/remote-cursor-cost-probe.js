/* What does drawing a remote cursor COST?
 *
 * The echo probe (remote-cursor-echo-probe.js) answered the safety question --
 * markText and setBookmark publish nothing -- and then produced a cost number
 * that cannot be taken at face value: 100 create+clear cycles in 16.9 SECONDS.
 * Its fixture was a single 120,006-character line, which is CodeMirror 5's
 * known pathological case and nothing like a Newspeak class source. A number
 * measured on the worst possible shape says nothing about the real one.
 *
 * So this probe varies the two things separately:
 *
 *   small      40 lines x 40 chars      ~1.6KB    a small method
 *   manyLines  3000 lines x 40 chars    ~120KB    a big source file
 *   oneLine    1 line x 120000 chars    ~120KB    the echo probe's fixture
 *
 * manyLines and oneLine are the SAME number of characters. If they cost the
 * same, size drives the cost and remote cursors are expensive on any large
 * document. If oneLine is far worse, line LENGTH drives it, the 169ms was an
 * artifact, and real sources are fine. That contrast is the whole point of the
 * probe; neither number means anything alone.
 *
 * One client, no second browser: this measures local rendering, not sync.
 *
 * Run: croquet-probes/run.sh remote-cursor-cost-probe.js
 */
const { sleep, launchBrowser, bootIDE, makeChecker } = require('./harness');

const SESSION = 'rcost' + Math.floor(Date.now() / 1000);
const SNAPSHOT = process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE.vfuel';
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=' + SNAPSHOT
  + '&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files';

setTimeout(() => { console.log('BAIL: overall deadline passed'); process.exit(1); },
  Number(process.env.DEADLINE_MS || 420000)).unref();

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";

const FIXTURES = [
  { name: 'small',     js: "Array(40).fill('x'.repeat(40)).join('\\n')" },
  { name: 'manyLines', js: "Array(3000).fill('x'.repeat(40)).join('\\n')" },
  { name: 'oneLine',   js: "'x'.repeat(120000)" },
];

/* Decorate at a position that exists in every fixture (line 0), so the only
   variable is the document around it.
 *
 * THREE modes, because the first run's numbers were indefensible -- 42.9ms per
 * cycle on a FORTY-LINE document, which no amount of document size explains:
 *
 *   unbatched  markText, setBookmark, clear, clear as four separate calls.
 *              Each forces its own CodeMirror display update. This is what the
 *              echo probe measured, and it is not how anyone would write it.
 *   batched    the same four calls inside one cm.operation(), which is how
 *              CodeMirror is meant to be driven and how the real code would.
 *   move       the realistic unit of work: one remote cursor MOVES. Clear its
 *              old mark and bookmark, create them at the new position, in one
 *              operation. This is the per-remote-keystroke cost, and the
 *              number the design actually rides on.
 *
 * Also reported: the viewport. If CodeMirror's rendered range covers the whole
 * document, viewport virtualization is off -- the known cause of the IDE
 * editor's 87x cost -- and every display update is touching every line. That
 * would make the cost a property of the IDE's editor, not of marks. */
const BODY = {
  unbatched: `
    var m = cm.markText({line:0,ch:0},{line:0,ch:8},{className:'ns-remote-sel-0'});
    var w = document.createElement('span');
    w.style.cssText = 'border-left:2px solid red;height:1em;display:inline-block';
    var b = cm.setBookmark({line:0,ch:12},{widget:w});
    m.clear(); b.clear();`,
  batched: `
    cm.operation(function(){
      var m = cm.markText({line:0,ch:0},{line:0,ch:8},{className:'ns-remote-sel-0'});
      var w = document.createElement('span');
      w.style.cssText = 'border-left:2px solid red;height:1em;display:inline-block';
      var b = cm.setBookmark({line:0,ch:12},{widget:w});
      m.clear(); b.clear();
    });`,
  move: `
    cm.operation(function(){
      if (window.__m) { window.__m.clear(); window.__b.clear() }
      var ch = i % 8;
      window.__m = cm.markText({line:0,ch:ch},{line:0,ch:ch+8},{className:'ns-remote-sel-0'});
      var w = document.createElement('span');
      w.style.cssText = 'border-left:2px solid red;height:1em;display:inline-block';
      window.__b = cm.setBookmark({line:0,ch:ch+12},{widget:w});
    });`,
};

const measure = (setup, cycles, mode) => `(function(){var cm=${CM};
  cm.setValue(${setup});
  cm.refresh();
  window.__m = null; window.__b = null;
  var t0 = performance.now();
  for (var i = 0; i < ${cycles}; i++) {${BODY[mode]}
  }
  var ms = performance.now() - t0;
  if (window.__m) { window.__m.clear(); window.__b.clear() }
  var vp = cm.getViewport();
  return JSON.stringify({chars: cm.getValue().length, lines: cm.lineCount(),
                         rendered: vp.to - vp.from,
                         ms: Math.round(ms), perCycle: Math.round(ms/${cycles}*10)/10})})()`;

async function main() {
  const t = makeChecker();
  const CYCLES = Number(process.env.CYCLES || 100);

  console.log('booting...');
  const A = await launchBrowser({ port: 9483, tag: 'rcost', session: SESSION });
  const up = await bootIDE(A, URL);
  t.check('client booted to a workspace', up);
  if (!up) { t.summary(); A.proc.kill(); return }
  await sleep(2000);

  const results = {};
  for (const mode of ['unbatched', 'batched', 'move']) {
    results[mode] = {};
    console.log('\n--- ' + mode + ' ---');
    for (const f of FIXTURES) {
      const r = JSON.parse(await A.v(measure(f.js, CYCLES, mode)));
      results[mode][f.name] = r;
      console.log('  ' + f.name.padEnd(10), JSON.stringify(r));
      await sleep(1000);
    }
  }

  const u = results.unbatched, b = results.batched, m = results.move;

  console.log('\nper-cycle ms, by mode and fixture:');
  for (const f of FIXTURES)
    console.log('  ' + f.name.padEnd(10)
      + ' unbatched ' + String(u[f.name].perCycle).padStart(7)
      + '   batched ' + String(b[f.name].perCycle).padStart(7)
      + '   move ' + String(m[f.name].perCycle).padStart(7));

  /* Is the editor virtualizing at all? If the rendered range is the whole
     document, it is not, and every display update touches every line. */
  const vp = b.manyLines;
  console.log('\nviewport on a 3000-line doc: ' + vp.rendered + ' of ' + vp.lines + ' lines rendered');
  t.check('CodeMirror is virtualizing the viewport (not rendering every line)',
          vp.rendered < vp.lines, vp.rendered + '/' + vp.lines + ' lines rendered');

  /* The artifact check: was the first run's number about marks, or about
     driving CodeMirror four un-batched times per cycle? */
  t.check('batching is what the first measurement was missing',
          b.small.perCycle < u.small.perCycle / 2,
          'small: unbatched ' + u.small.perCycle + 'ms -> batched ' + b.small.perCycle + 'ms');

  /* The number the design rides on: moving one remote cursor on a realistic
     big source, once per remote keystroke. A frame is 16ms. */
  t.check('moving a remote cursor on a 120KB multi-line source is under 5ms',
          m.manyLines.perCycle < 5, m.manyLines.perCycle + 'ms per move');

  t.check('cursor move cost does not explode with document size',
          m.manyLines.perCycle < m.small.perCycle + 5,
          'small ' + m.small.perCycle + 'ms -> manyLines ' + m.manyLines.perCycle + 'ms');

  const errs = A.logs.filter(l => l.startsWith('[error]'));
  t.check('no console errors', errs.length === 0, errs.slice(0, 3).join(' | '));

  t.summary();
  A.proc.kill();
}

main().catch(e => { console.error(e); process.exit(1) });
