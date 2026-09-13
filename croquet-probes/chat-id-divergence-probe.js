/* Does the chat status block mint a DIFFERENT NUMBER of synchronized fragment
   ids depending on client-local state?

   Every synchronized fragment takes its Croquet event address from a per-type
   counter incremented at construction, so two clients agree about which widget
   an event names only while they mint in the same order and number
   (CROQUET_SCOPED_FRAGMENT_IDS_2026-08-18.md). ChatStatusPresenter>>definition
   selects among four shapes on `subject waiting`, `subject errorMessage` and
   `subject canRetry` — all per-client — and those shapes contain different
   numbers of buttons and dropdowns.

   Section A proves that by construction, on one client, with no race: build the
   real presenter over a real subject, flip the subject's state, and count what
   the ledger records. A fresh presenter per state, because a presenter caches
   its substance and its visual after the first build. If the counts differ,
   divergence is not a possibility but a certainty, since the deciding state is
   client-local.

   Section B checks the instrument itself: two clients that do the same things
   must produce identical ledgers. A false alarm here would make everything the
   ledger says worthless, so it is asserted before anything is concluded from it.

   Needs: reflector on 9090. The ledger is opt-in, so the page URL carries
   &mintLedger=on (localStorage 'ns_mint_ledger' = 'on' does the same for a
   hand-driven session). Point NS_WEB_ROOT at a staged out/ to avoid writing
   into a live tree.
   Run: node chat-id-divergence-probe.js                                      */
const { spawn } = require('child_process');
const path = require('path');
const http = require('http');
const { sleep, launchBrowser, bootIDE, evalDoIt, makeChecker } = require('./harness');

const A_PORT = 8094, B_PORT = 8095;
const A_ORIGIN = 'http://localhost:' + A_PORT, B_ORIGIN = 'http://localhost:' + B_PORT;
const SESSION = 'cmid' + Math.floor(Date.now() / 1000);
const { check, summary } = makeChecker();

const ideUrl = origin => origin
  + '/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.cmid&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files&mintLedger=on';

function startFrontDoor(port) {
  const args = [path.join(__dirname, '..', 'tool', 'cors-proxy.py'), String(port), '--bus'];
  if (process.env.NS_WEB_ROOT) args.push('--root', process.env.NS_WEB_ROOT);
  return spawn('python3', args, { stdio: 'ignore' });
}
function portFree(port) {
  return new Promise(res => { const s = require('net').createServer();
    s.once('error', () => res(false)); s.once('listening', () => s.close(() => res(true)));
    s.listen(port, '127.0.0.1') });
}
function tokenOf(origin) {
  return new Promise(async res => {
    for (let i = 0; i < 60; i++) {
      try { const b = await new Promise((ok, no) =>
        http.get(origin + '/_ns/token', r => { let s = ''; r.on('data', c => s += c); r.on('end', () => ok(s)) }).on('error', no));
        return res(JSON.parse(b).token) } catch (e) { await sleep(500) }
    }
    res(undefined);
  });
}

/* Section A. The real ChatStatusPresenter on a real ChatSubject over a real
   Session. A BusProvider is used because it needs no API key and no network:
   only the SHAPE of the fragment tree is under test. `definition` is called
   directly rather than through the shell, so nothing but this presenter mints. */
const SHAPE_DOIT =
  "[:g | [ | prov sess subj shape |" +
  "  prov:: platform aiAccess BusProvider agentName: 'probeagent' chat: 'ProbeShape' port: ide aiSupport." +
  "  sess:: platform aiAccess Session provider: prov tools: platform collections List new." +
  "  subj:: platform hopscotch ChatSubject onModel: sess." +
  "  shape:: [:label :prep |" +
  "      | p |" +
  "      prep value." +
  "      p:: platform hopscotch ChatStatusPresenter onSubject: subj." +
  "      g nsLedgerReset: nil." +
  "      p visual." +
  "      label , '=' , ((g at: 'JSON') stringify: (g nsLedgerTotals: nil)) ]." +
  "  g at: 'shapes' put: ((shape value: 'waiting' value: [ subj waiting: true. subj errorMessage: nil ])" +
  "      , ' | ' , (shape value: 'idle' value: [ subj waiting: false. subj errorMessage: nil ])" +
  "      , ' | ' , (shape value: 'errored' value: [ subj waiting: false. subj markError: 'probe' ]))." +
  "  g nsLedgerReset: nil." +
  "] on: Exception do: [:e | g at: 'shapes' put: 'ERR ' , e printString ]. 'GO'] value: platform js global";

const countOf = (s, label) => {
  const m = new RegExp(label + '=(\\{.*?\\})(?: \\||$)').exec(s);
  if (!m) return null;
  try { return JSON.parse(m[1]) } catch (e) { return null }
};

async function main() {
  for (const p of [A_PORT, B_PORT]) if (!await portFree(p)) {
    console.log('port ' + p + ' already in use - stale front door from an earlier run?');
    process.exitCode = 1; return;
  }
  const proxies = [startFrontDoor(A_PORT), startFrontDoor(B_PORT)];
  if (!await tokenOf(A_ORIGIN) || !await tokenOf(B_ORIGIN)) {
    console.log('a front door never came up'); proxies.forEach(p => p.kill()); process.exitCode = 1; return;
  }

  const clients = [];
  const A = await launchBrowser({ port: 9831, tag: 'cmid-a', session: SESSION }); clients.push(A);
  if (!await bootIDE(A, ideUrl(A_ORIGIN))) {
    check('A boots', false, A.logs.slice(-4).join(' | ')); return done(clients, proxies);
  }
  check('the ledger is present in this build', await A.v('typeof nsRecordMint') === 'function',
    await A.v('typeof nsRecordMint'));

  console.log('\n--- A: does ChatStatusPresenter mint a state-dependent number of ids? ---');
  const shapes = await evalDoIt(A, SHAPE_DOIT, 'shapes', 60);
  console.log('  ' + String(shapes).replace(/ \| /g, '\n  '));
  const waiting = countOf(String(shapes), 'waiting'), idle = countOf(String(shapes), 'idle');
  const errored = countOf(String(shapes), 'errored');
  check('all three states were measured', !!(waiting && idle && errored), String(shapes).slice(0, 200));
  if (waiting && idle) {
    /* THE ASSERTION. Equal totals means the fragment tree's synchronized shape
       does not depend on client-local state, which is the invariant. It fails
       today; it must pass once the transient controls stop synchronizing. */
    check('waiting and idle mint the SAME ids (the invariant)',
      JSON.stringify(waiting.counts) === JSON.stringify(idle.counts),
      'waiting=' + JSON.stringify(waiting.counts) + ' idle=' + JSON.stringify(idle.counts));
    check('idle and errored mint the SAME ids (the invariant)',
      JSON.stringify(idle.counts) === JSON.stringify(errored.counts),
      'idle=' + JSON.stringify(idle.counts) + ' errored=' + JSON.stringify(errored.counts));
  }

  console.log('\n--- B: two clients doing the same things must agree (instrument check) ---');
  const B = await launchBrowser({ port: 9832, tag: 'cmid-b', session: SESSION }); clients.push(B);
  if (!await bootIDE(B, ideUrl(B_ORIGIN))) check('B boots', false, B.logs.slice(-4).join(' | '));
  else {
    await sleep(6000);
    const hashes = b => b.v('JSON.stringify(nsLedgerBlockHashes(200))');
    const [ha, hb] = [JSON.parse(await hashes(A) || '[]'), JSON.parse(await hashes(B) || '[]')];
    const first = firstDivergence(ha, hb);
    console.log('  A mints=' + (await A.v('nsLedgerCount()')) + '  B mints=' + (await B.v('nsLedgerCount()')));
    /* The context label is the diagnostic's whole value - a bare ordinal says a
       divergence happened, a label says who caused it. Shown every run so a
       build that silently stopped labelling is noticed here, not later. */
    console.log('  sample A entries: ' + await A.v('JSON.stringify(nsLedgerSlice(0,3))'));
    if (first === null) check('the two clients\' ledgers agree', true);
    else {
      console.log('  first differing block at index ' + first + '; slices:');
      for (const [n, b] of [['A', A], ['B', B]]) {
        const sl = await b.v(`JSON.stringify(nsLedgerSlice(${Math.max(0, first - 6)}, ${first + 2}))`);
        console.log('    ' + n + ' ' + sl);
      }
      /* A and B are NOT equivalent here: B is a joiner and replays. A genuine
         mismatch is expected to involve local-only renders, so this is reported
         rather than asserted - the assertion that matters is Section A's. */
      check('the two clients\' ledgers agree', false, 'diverge near index ' + first);
    }
  }
  return done(clients, proxies);
}

function firstDivergence(ha, hb) {
  for (let i = 0; i < Math.min(ha.length, hb.length); i++)
    if (ha[i].h !== hb[i].h) return ha[i].i;
  return ha.length === hb.length ? null : Math.min(ha.length, hb.length) * 200;
}
function done(bs, proxies) {
  bs.forEach(b => { try { b.proc.kill() } catch (e) {} });
  proxies.forEach(p => { try { p.kill() } catch (e) {} });
  summary();
}
main().catch(e => { console.error(e); process.exit(1) });
