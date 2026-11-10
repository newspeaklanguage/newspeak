/* Is there a channel for presence -- one that reaches the other clients and
 * does NOT become part of the session's permanent record?
 *
 * Presence (a pointer, a caret, who is looking at what) is the most frequent
 * and least durable thing we would ever send. The only cross-client path we
 * have is theView.publish (out/croquetpsoup.js:2444), and the session's state
 * IS its recorded event history (:2755). Sending pointer motion down that path
 * would make every twitch permanent and replay it to every late joiner.
 *
 * But reading the model showed the picture is not that simple. There are two
 * kinds of model-routed event:
 *
 *   publishEvent / publishEventAndData (:2834, :2843) call addEvent, which
 *   pushes onto this.newspeakEvents -- "a list of all events ever sent to the
 *   model" -- and that list is what doPersistTick persists (:2820).
 *
 *   the mouse handlers (:2955-2978) do NOT. mouseMove(fid) only re-publishes
 *   to the views. The event crosses the reflector and reaches every client,
 *   and leaves NOTHING in the persisted list.
 *
 * Nothing publishes those mouse events today -- the hooks are dormant, a
 * leftover of "Leaf fragment support". So the question is whether that dormant
 * shape is the presence channel we need.
 *
 * THREE CHANNELS, MEASURED THE SAME WAY
 *
 *   view     theView.publish on a scope no model subscribes to, with only view
 *            subscriptions. If this crosses clients it is free. Expected NOT
 *            to: Croquet handles a view event locally when no model wants it.
 *            Measured rather than assumed, because "free" would change the
 *            design.
 *   light    the dormant onMouseMove path: view -> model -> views, no addEvent.
 *            Crosses the reflector, should leave no persisted trace.
 *   full     a real editor edit, which goes through nsPublish -> model ->
 *            addEvent. The CONTROL: it must both reach the other client AND
 *            grow newspeakEvents. If it doesn't, the measurement is broken and
 *            every "no trace" below is meaningless.
 *
 * The persisted-history question is read directly off theModel.newspeakEvents
 * on both clients, which is the structure doPersistTick writes. That is what a
 * late joiner restores from. Croquet ALSO replays raw reflector messages since
 * the last snapshot, which this probe does not see; LATEJOIN=1 adds a third
 * client to test that separately, and costs another browser boot.
 *
 * Presence traffic is sent at 10Hz for 5s, which is both a realistic presence
 * rate and a test of whether it survives the reflector's send rate limit -- a
 * limit an echo storm has already blown past once (HopscotchForCroquet.ns:294).
 *
 * Run: croquet-probes/run.sh presence-channel-probe.js
 *      croquet-probes/run.sh LATEJOIN=1 presence-channel-probe.js
 */
const { sleep, launchBrowser, bootIDE, makeChecker } = require('./harness');

const SESSION = 'presence' + Math.floor(Date.now() / 1000);
const SNAPSHOT = process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE.vfuel';
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=' + SNAPSHOT
  + '&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files';

setTimeout(() => { console.log('BAIL: overall deadline passed'); process.exit(1); },
  Number(process.env.DEADLINE_MS || 560000)).unref();

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const PING_SCOPE = 'nspresenceprobe_';
const PING_FID = 'nspresenceprobe_fid';
const RATE_HZ = 10, SECONDS = 5;
const N = RATE_HZ * SECONDS;

/* Receiver side: count arrivals on both channels. The 'light' subscription is
   on the scope and event the model's mouseMove handler republishes to. */
const LISTEN = `(function(){
  if (!window.theView) return 'NOVIEW';
  window.__rx = {view: 0, light: 0};
  theView.subscribe(${JSON.stringify(PING_SCOPE)}, 'ping', function(){ window.__rx.view++ });
  theView.subscribe(${JSON.stringify(PING_FID)}, 'model_mouseMove', function(){ window.__rx.light++ });
  return 'LISTENING';
})()`;

/* Sender side. Spread over SECONDS so the rate is realistic and the reflector's
   limiter is actually exercised rather than hit with a burst. */
const send = kind => `(function(){
  var n = 0;
  var t = setInterval(function(){
    if (n++ >= ${N}) { clearInterval(t); return }
    ${kind === 'view'
      ? `theView.publish(${JSON.stringify(PING_SCOPE)}, 'ping', {x: n, y: n});`
      : `theView.publish(theView.sessionId, 'onMouseMove', ${JSON.stringify(PING_FID)});`}
  }, ${Math.round(1000 / RATE_HZ)});
  return 'SENDING ${N}';
})()`;

const HISTLEN = "(function(){return (window.theModel && theModel.newspeakEvents) ? theModel.newspeakEvents.length : -1})()";
const RX = "JSON.stringify(window.__rx || {})";

async function main() {
  const t = makeChecker();

  console.log('booting A and B...');
  const A = await launchBrowser({ port: 9484, tag: 'pra', session: SESSION });
  const B = await launchBrowser({ port: 9485, tag: 'prb', session: SESSION });
  const [aUp, bUp] = await Promise.all([bootIDE(A, URL), bootIDE(B, URL)]);
  t.check('client A booted', aUp);
  t.check('client B booted', bUp);
  if (!aUp || !bUp) { t.summary(); A.proc.kill(); B.proc.kill(); return }
  await sleep(3000);

  t.check('A is listening', await A.v(LISTEN) === 'LISTENING');
  t.check('B is listening', await B.v(LISTEN) === 'LISTENING');

  const h0 = await A.v(HISTLEN);
  t.check('the model\'s event list is readable', h0 >= 0, 'length ' + h0);
  if (h0 < 0) { t.summary(); A.proc.kill(); B.proc.kill(); return }

  /* ---- CONTROL: a real edit must cross AND be recorded ---- */
  await A.v(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');` +
            `cm.replaceSelection('presence probe control edit', null, '+input');return 1})()`);
  await sleep(3000);
  const hAfterEdit = await A.v(HISTLEN);
  const bSawEdit = await B.v(`${CM}.getValue().indexOf('control edit') >= 0`);
  t.check('CONTROL: a recorded event reaches B', !!bSawEdit);
  t.check('CONTROL: a recorded event grows the persisted list',
          hAfterEdit > h0, h0 + ' -> ' + hAfterEdit);
  const controlOk = bSawEdit && hAfterEdit > h0;
  if (!controlOk)
    console.log('\n*** control failed: "leaves no trace" below would prove NOTHING ***\n');

  /* ---- CHANNEL 1: view-only ---- */
  const hBeforeView = await A.v(HISTLEN);
  await A.v(send('view'));
  await sleep(SECONDS * 1000 + 3000);
  const rxViewB = JSON.parse(await B.v(RX)), rxViewA = JSON.parse(await A.v(RX));
  const hAfterView = await A.v(HISTLEN);
  console.log('view-only: A received ' + rxViewA.view + ', B received ' + rxViewB.view + ' of ' + N);
  t.check('view-only publish does NOT cross to B', rxViewB.view === 0,
          'B got ' + rxViewB.view);
  t.check('view-only publish leaves no persisted trace',
          hAfterView === hBeforeView, hBeforeView + ' -> ' + hAfterView);

  /* ---- CHANNEL 2: the dormant mouse path ---- */
  const hBeforeLight = await A.v(HISTLEN);
  const t0 = Date.now();
  await A.v(send('light'));
  await sleep(SECONDS * 1000 + 4000);
  const rxLightB = JSON.parse(await B.v(RX));
  const hAfterLight = await A.v(HISTLEN);
  const hAfterLightB = await B.v(HISTLEN);
  console.log('light: B received ' + rxLightB.light + ' of ' + N
              + ' in ' + (Date.now() - t0) + 'ms');
  t.check('LIGHT: reaches B', rxLightB.light > 0, 'B got ' + rxLightB.light + '/' + N);
  t.check('LIGHT: delivery is not lossy at ' + RATE_HZ + 'Hz',
          rxLightB.light >= N * 0.9, 'B got ' + rxLightB.light + '/' + N);
  t.check('LIGHT: leaves NO persisted trace',
          hAfterLight === hBeforeLight, hBeforeLight + ' -> ' + hAfterLight);
  t.check('A and B agree on the persisted list',
          hAfterLight === hAfterLightB, 'A ' + hAfterLight + ' B ' + hAfterLightB);

  /* ---- did the rate survive? ---- */
  const warnsA = A.logs.filter(l => /detached|rate|limit|disconnect/i.test(l));
  t.check('no disconnect or rate-limit warnings at ' + RATE_HZ + 'Hz',
          warnsA.length === 0, warnsA.slice(0, 3).join(' | '));

  /* ---- optional: does a late joiner replay the presence traffic? ---- */
  if (process.env.LATEJOIN === '1') {
    console.log('booting late joiner C...');
    const C = await launchBrowser({ port: 9486, tag: 'prc', session: SESSION });
    const cUp = await bootIDE(C, URL);
    t.check('late joiner C booted', cUp);
    if (cUp) {
      await C.v(LISTEN);
      await sleep(5000);
      const rxC = JSON.parse(await C.v(RX));
      const hC = await C.v(HISTLEN);
      console.log('late joiner: rx ' + JSON.stringify(rxC) + ' history ' + hC);
      t.check('late joiner replays the same persisted list',
              hC === hAfterLight, 'C ' + hC + ' vs A ' + hAfterLight);
      t.check('late joiner does NOT replay presence traffic',
              rxC.light === 0 && rxC.view === 0, JSON.stringify(rxC));
    }
    C.proc.kill();
  }

  const errsA = A.logs.filter(l => l.startsWith('[error]'));
  const errsB = B.logs.filter(l => l.startsWith('[error]'));
  t.check('no console errors on A', errsA.length === 0, errsA.slice(0, 2).join(' | '));
  t.check('no console errors on B', errsB.length === 0, errsB.slice(0, 2).join(' | '));

  t.summary();
  A.proc.kill(); B.proc.kill();
}

main().catch(e => { console.error(e); process.exit(1) });
