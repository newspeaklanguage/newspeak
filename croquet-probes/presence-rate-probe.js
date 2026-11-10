/* How much presence traffic does the session actually take?
 *
 * presence-channel-probe.js found the channel: a model handler that
 * re-publishes without addEvent (out/croquetpsoup.js:2963) reaches every
 * client and leaves nothing in the persisted history. It measured ONE sender
 * at 10Hz: 50 of 50 delivered, no warnings.
 *
 * That number does not support the design, because presence scales with
 * PARTICIPANTS. The reflector budget is shared -- the editor's own design
 * budgets around ~20 msg/s for the whole session -- and an echo storm has
 * already blown past the send rate limit once, taking the session down with it
 * (HopscotchForCroquet.ns:294). Two clients at 10Hz each is 20/s from presence
 * alone, before anyone types. So the question is not "does 10Hz work" but
 * "where is the knee, and how does it move with the number of senders".
 *
 * METHOD
 *
 * Three clients. Each sender gets its OWN fid, because the mouseMove handler
 * republishes with no payload -- there is nowhere to put a sequence number, so
 * per-sender scopes are how arrivals are attributed. Every client subscribes
 * to all three and counts. Delivery ratio is received/sent for each
 * (sender, receiver) pair; the figure of merit is the WORST pair, since one
 * client starved is a broken feature.
 *
 * Swept: 5, 10, 20, 30 Hz per sender, with 2 senders and then 3. Aggregate
 * offered load therefore runs from 10/s to 90/s across the sweep.
 *
 * THE HEALTH CHECK IS THE POINT
 *
 * A dropped ping is a cosmetic failure. A DETACHED VIEW is a broken session --
 * that is what the echo storm did. So after the sweep the probe makes an
 * ordinary edit and requires it to reach the other clients. If presence
 * traffic can wedge the session, that is the finding, and it matters far more
 * than any delivery percentage above it.
 *
 * Run: croquet-probes/run.sh presence-rate-probe.js
 *      croquet-probes/run.sh RATES=5,10,20,30,60 presence-rate-probe.js
 */
const { sleep, launchBrowser, bootIDE, makeChecker } = require('./harness');

const SESSION = 'prate' + Math.floor(Date.now() / 1000);
const SNAPSHOT = process.env.NS_SNAPSHOT || 'CroquetHopscotchWebIDE.vfuel';
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=' + SNAPSHOT
  + '&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files';

setTimeout(() => { console.log('BAIL: overall deadline passed'); process.exit(1); },
  Number(process.env.DEADLINE_MS || 570000)).unref();

const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const RATES = (process.env.RATES || '5,10,20,30').split(',').map(Number);
const BURST_S = Number(process.env.BURST_S || 3);
const TAGS = ['a', 'b', 'c'];
const FID = tag => 'nspresence_' + tag;

const LISTEN = `(function(){
  if (!window.theView) return 'NOVIEW';
  window.__rx = {a: 0, b: 0, c: 0};
  ${TAGS.map(tg =>
    `theView.subscribe(${JSON.stringify(FID(tg))}, 'model_mouseMove', function(){ window.__rx.${tg}++ });`
  ).join('\n  ')}
  return 'LISTENING';
})()`;

/* Cancel any burst still in flight. Without this a slow burst runs on into the
   next configuration and is counted there: the first sweep showed a sender
   asked for 10Hz delivering 44/s, and a bogus 68% where the denominator kept
   growing after the numerator was read. */
const RESET = "(function(){if(window.__t){clearInterval(window.__t);window.__t=null}" +
              "window.__sending=false;window.__sent=0;window.__rx={a:0,b:0,c:0};return 1})()";
const RX = "JSON.stringify(window.__rx||{})";
const SENDING = "(window.__sending===true)";
const ALIVE = "(function(){return !!(window.theView && theView.session)})()";

/* The sender counts what it ACTUALLY published. Dividing by the intended count
   would be a lie at high rates: browsers clamp setInterval to about 4ms, so
   asking for 240Hz gets something slower, and a ratio against the request
   would read as loss that never happened -- or, worse, hide real loss behind a
   sender that never sent. */
const send = (tag, n, hz) => `(function(){
  if (window.__t) clearInterval(window.__t);
  var i = 0;
  window.__sent = 0;
  window.__sending = true;
  window.__t = setInterval(function(){
    if (i++ >= ${n}) { clearInterval(window.__t); window.__t = null; window.__sending = false; return }
    theView.publish(theView.sessionId, 'onMouseMove', ${JSON.stringify(FID(tag))});
    window.__sent++;
  }, ${Math.max(1, Math.round(1000 / hz))});
  return 'S';
})()`;

const SENT = "(window.__sent||0)";

async function main() {
  const t = makeChecker();

  console.log('booting three clients...');
  const cl = {};
  for (const [i, tg] of TAGS.entries())
    cl[tg] = await launchBrowser({ port: 9490 + i, tag: 'pr' + tg, session: SESSION });
  const ups = await Promise.all(TAGS.map(tg => bootIDE(cl[tg], URL)));
  TAGS.forEach((tg, i) => t.check('client ' + tg.toUpperCase() + ' booted', ups[i]));
  if (ups.some(u => !u)) { t.summary(); TAGS.forEach(tg => cl[tg].proc.kill()); return }
  await sleep(3000);

  for (const tg of TAGS)
    t.check(tg.toUpperCase() + ' is listening', await cl[tg].v(LISTEN) === 'LISTENING');

  const rows = [];
  for (const nSenders of [2, 3]) {
    const senders = TAGS.slice(0, nSenders);
    for (const hz of RATES) {
      const n = hz * BURST_S;
      for (const tg of TAGS) await cl[tg].v(RESET);
      /* Start them as close to together as the protocol allows: fire without
         awaiting, then await the acks. */
      await Promise.all(senders.map(tg => cl[tg].v(send(tg, n, hz))));
      /* Wait for sending to actually STOP before measuring anything. A burst
         that is still running makes the denominator grow after the numerator
         was read, which is how the first sweep invented a 68%. */
      let stillSending = true;
      for (let i = 0; i < 60 && stillSending; i++) {
        await sleep(500);
        const flags = await Promise.all(senders.map(tg => cl[tg].v(SENDING)));
        stillSending = flags.some(Boolean);
      }
      if (stillSending)
        console.log('    (warning: a burst never finished; this row is suspect)');
      await sleep(4000);   // settle: let in-flight arrivals land

      const rx = {}, sent = {};
      for (const tg of TAGS) rx[tg] = JSON.parse(await cl[tg].v(RX));
      for (const s of senders) sent[s] = await cl[s].v(SENT);
      /* Worst cross-client pair: sender s -> receiver r, s !== r. Ratios are
         against what the sender really sent, and are NOT clamped at 1 -- an
         over-count would otherwise hide behind a healthy-looking 100%. */
      let worst = Infinity, worstPair = '';
      for (const s of senders) for (const r of TAGS) {
        if (s === r) continue;
        const ratio = sent[s] ? rx[r][s] / sent[s] : 0;
        if (ratio < worst) { worst = ratio; worstPair = s + '->' + r }
      }
      const over = senders.some(s => TAGS.some(r => r !== s && rx[r][s] > sent[s]));
      const achieved = senders.map(s => (sent[s] / BURST_S).toFixed(0)).join('/');
      const alive = (await Promise.all(TAGS.map(tg => cl[tg].v(ALIVE)))).every(Boolean);
      rows.push({ nSenders, hz, offered: nSenders * hz, n, sent: Object.assign({}, sent),
                  rx: JSON.parse(JSON.stringify(rx)), worst, worstPair, over, alive });
      console.log('  ' + nSenders + ' senders @ ' + String(hz).padStart(3) + 'Hz'
        + '  asked ' + String(n).padStart(4) + ' each, sent ' + String(achieved).padStart(9)
        + '/s  worst ' + (worst * 100).toFixed(0).padStart(4) + '% (' + (worstPair || '-') + ')'
        + (over ? '  OVER-DELIVERED' : '')
        + '  alive ' + alive);
      await sleep(2000);
    }
  }

  console.log('');
  /* The low end must work, or the channel is not usable at all. */
  const low = rows.find(r => r.nSenders === 2 && r.hz === RATES[0]);
  t.check('2 senders at ' + RATES[0] + 'Hz deliver >=90%',
          low && low.worst >= 0.9, low && (low.worst * 100).toFixed(0) + '%');

  /* Where it stops working -- reported, since the knee is the deliverable. */
  const bad = rows.filter(r => r.worst < 0.9);
  console.log(bad.length
    ? 'KNEE: delivery drops below 90% at ' + bad.map(r => r.nSenders + 'x' + r.hz + 'Hz').join(', ')
    : 'no delivery knee found up to ' + Math.max(...rows.map(r => r.offered)) + ' msg/s offered');

  /* Every view still attached: a lost ping is cosmetic, a detached view is a
     broken session. */
  t.check('no view detached during the sweep', rows.every(r => r.alive),
          rows.filter(r => !r.alive).map(r => r.nSenders + 'x' + r.hz).join(', '));

  /* --- the health check: does the session still work afterwards? --- */
  await sleep(3000);
  const marker = 'rate probe survived ' + Date.now();
  await cl.a.v(`(function(){var cm=${CM};cm.focus();cm.execCommand('selectAll');` +
               `cm.replaceSelection(${JSON.stringify(marker)}, null, '+input');return 1})()`);
  let crossed = false;
  for (let i = 0; i < 20 && !crossed; i++) {
    await sleep(1000);
    crossed = !!(await cl.b.v(`${CM}.getValue().indexOf('rate probe survived') >= 0`));
  }
  t.check('HEALTH: an ordinary edit still crosses after the sweep', crossed);

  for (const tg of TAGS) {
    const warns = cl[tg].logs.filter(l => /detached|rate limit|too many|disconnect/i.test(l));
    if (warns.length) console.log(tg.toUpperCase() + ' warnings: ' + warns.slice(0, 3).join(' | '));
    const errs = cl[tg].logs.filter(l => l.startsWith('[error]'));
    t.check('no console errors on ' + tg.toUpperCase(), errs.length === 0,
            errs.slice(0, 2).join(' | '));
  }

  t.summary();
  for (const tg of TAGS) cl[tg].proc.kill();
}

main().catch(e => { console.error(e); process.exit(1) });
