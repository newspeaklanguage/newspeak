/* What does view-exit actually deliver?
 *
 * The presence design (2026-09-21) wants free cleanup: when a client leaves,
 * its cursor disappears everywhere, with no heartbeat and no timeout. The
 * sketch adds a model handler
 *
 *     viewExited(viewId){ this.publish('nspresence_', 'presence_gone', viewId); }
 *
 * which assumes the handler is passed the viewId directly. Depending on the
 * Croquet version it may be handed {viewId, viewData} instead -- and a
 * presence cleanup that silently never matches anybody is exactly the kind of
 * bug that shows up weeks later as "stale cursors pile up". Cheaper to look.
 *
 * No rebuild required: the model handler does not exist yet, but view-join and
 * view-exit are published into the island on the sessionId scope, so a VIEW
 * subscription sees the same payload a model handler would. If it turns out a
 * view subscription does not fire at all, that is also worth knowing -- it
 * would mean this can only be settled after a build.
 *
 * CONTROL: C joining must make A record a view-join. If nothing is ever
 * recorded, an empty view-exit list proves nothing -- it would just mean the
 * subscription never worked. So the probe reports the join shape first and
 * treats it as the discriminator.
 *
 * RESULT 2026-09-21: THIS APPROACH DOES NOT WORK, and the probe is kept only
 * to record why. A view-level subscription to view-join/view-exit never fires:
 * the Croquet client publishes them with publishFromModelOnly, so only a MODEL
 * handler sees them. The control caught it -- C joined and A recorded zero
 * view-joins -- so the equally empty view-exit list was correctly read as
 * proving nothing rather than as "view-exit does not fire".
 *
 * The question was settled by reading the client instead (out/croquet.min.js,
 * generateJoinExit):
 *
 *     const r = t => { const {data: e, loc: s} = this.views[t];
 *                      if (!e) return t;                        // bare viewId
 *                      const n = {viewId: t, viewData: e};
 *                      if (s) n.location = s; return n; };
 *
 * So the payload is the bare viewId STRING unless the client supplied viewData
 * at join. Neither platform does -- meta/croquet-post.js:1651 and
 * tool/croquet-glue-js/startup.js:28 both call Session.join without it -- so a
 * handler taking a string is correct TODAY. It is conditional, though, and
 * presence is exactly the feature that would tempt someone to start passing a
 * display name or colour as viewData, at which point the payload silently
 * becomes an object. The presence handler therefore accepts both shapes.
 *
 * To verify against a real model handler, this needs a rebuild; at that point
 * the cheap check is to log the payload from viewExited directly.
 *
 * Run: croquet-probes/run.sh view-exit-shape-probe.js
 */
const { sleep, launchBrowser, bootIDE, makeChecker } = require('./harness');

const SESSION = 'vexit' + Math.floor(Date.now() / 1000);
const SNAPSHOT = process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE.vfuel';
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=' + SNAPSHOT
  + '&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files';

setTimeout(() => { console.log('BAIL: overall deadline passed'); process.exit(1); },
  Number(process.env.DEADLINE_MS || 560000)).unref();

/* Record the RAW argument, not an interpretation of it: its typeof, its JSON,
   and whether it has a viewId property. Reading it as a string when it is an
   object is precisely the mistake this probe exists to prevent. */
const RECORD = `(function(){
  if (!window.theView) return 'NOVIEW';
  window.__vj = []; window.__vx = [];
  var shape = function(a){
    var j; try { j = JSON.stringify(a) } catch (e) { j = String(a) }
    return {type: typeof a, json: j,
            hasViewId: !!(a && typeof a === 'object' && 'viewId' in a),
            asString: String(a)};
  };
  theView.subscribe(theView.sessionId, 'view-join', function(a){ window.__vj.push(shape(a)) });
  theView.subscribe(theView.sessionId, 'view-exit', function(a){ window.__vx.push(shape(a)) });
  return 'RECORDING';
})()`;

const VJ = "JSON.stringify(window.__vj||[])";
const VX = "JSON.stringify(window.__vx||[])";
const MYID = "(window.theView ? String(theView.viewId) : 'NOVIEW')";

async function main() {
  const t = makeChecker();

  console.log('booting A and B...');
  const A = await launchBrowser({ port: 9487, tag: 'vxa', session: SESSION });
  const B = await launchBrowser({ port: 9488, tag: 'vxb', session: SESSION });
  const [aUp, bUp] = await Promise.all([bootIDE(A, URL), bootIDE(B, URL)]);
  t.check('client A booted', aUp);
  t.check('client B booted', bUp);
  if (!aUp || !bUp) { t.summary(); A.proc.kill(); B.proc.kill(); return }
  await sleep(2000);

  t.check('A is recording', await A.v(RECORD) === 'RECORDING');
  t.check('B is recording', await B.v(RECORD) === 'RECORDING');

  /* C joins AFTER the recorders are installed, so its join is observable. */
  console.log('booting C (its join is the control)...');
  const C = await launchBrowser({ port: 9489, tag: 'vxc', session: SESSION });
  const cUp = await bootIDE(C, URL);
  t.check('client C booted', cUp);
  if (!cUp) { t.summary(); A.proc.kill(); B.proc.kill(); C.proc.kill(); return }
  const cId = await C.v(MYID);
  console.log('C viewId: ' + cId);
  await sleep(4000);

  const joinsA = JSON.parse(await A.v(VJ));
  console.log('A recorded ' + joinsA.length + ' view-join(s): ' + JSON.stringify(joinsA));
  t.check('CONTROL: a view-level subscription to view-join fires', joinsA.length > 0,
          'A recorded ' + joinsA.length);
  const controlOk = joinsA.length > 0;
  if (!controlOk)
    console.log('\n*** control failed: an empty view-exit below proves NOTHING ***\n');

  /* C leaves cleanly: navigating away closes the session rather than waiting
     for the reflector to time out a dropped socket. */
  console.log('C leaving...');
  await C.navigate('about:blank');
  let exitsA = [];
  for (let i = 0; i < 40 && exitsA.length === 0; i++) {
    await sleep(1500);
    exitsA = JSON.parse(await A.v(VX));
  }
  const exitsB = JSON.parse(await B.v(VX));
  console.log('A recorded ' + exitsA.length + ' view-exit(s): ' + JSON.stringify(exitsA));
  console.log('B recorded ' + exitsB.length + ' view-exit(s): ' + JSON.stringify(exitsB));

  t.check('view-exit reaches the remaining clients', exitsA.length > 0,
          'A recorded ' + exitsA.length);

  if (exitsA.length) {
    const e = exitsA[0];
    console.log('\n>>> view-exit payload: typeof=' + e.type + '  json=' + e.json
                + '  hasViewId=' + e.hasViewId);
    /* THE question the sketch rides on. */
    t.check('the handler receives the viewId DIRECTLY (a string)',
            e.type === 'string', 'typeof is ' + e.type + ', json ' + e.json);
    t.check('the departing client is identifiable from the payload',
            e.asString.indexOf(cId) >= 0 || (e.json || '').indexOf(cId) >= 0,
            'looking for ' + cId + ' in ' + e.json);
  }

  const errs = A.logs.filter(l => l.startsWith('[error]'));
  t.check('no console errors on A', errs.length === 0, errs.slice(0, 2).join(' | '));

  t.summary();
  A.proc.kill(); B.proc.kill(); C.proc.kill();
}

main().catch(e => { console.error(e); process.exit(1) });
