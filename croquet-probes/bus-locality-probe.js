/* Does a bus completion go out from the machine the AGENT is actually on?

   The other bus probe puts every client behind one front door, so any elected
   client can reach the agent and locality never comes up. Here the two clients
   sit behind DIFFERENT front doors - A on 8080, where the agent holds its
   subscription, B on a second one this probe starts - which is the real shape:
   the bus is per-machine, an agent is a process listening on ONE participant's
   front door, and the reflector's election knows nothing about that.

   Without the capability gate the failure is not a wrong answer but a hang:
   B is elected, posts into its own bus where the IDE clients are subscribers
   and the agent is not, and the turn waits for a reply nobody will send.

   What is asserted:
     - both clients end with the SAME reply text (B consumed the recording),
     - the agent saw EXACTLY ONE request,
     - that request arrived on A's bus, not B's - measured by which front door
       the POST reached, since each probe run counts its own bus traffic,
     - a late joiner that also lacks the agent converges from the recording
       without re-issuing anything.

   Both front doors are started here, on scratch ports, rather than reusing the
   one on 8080: a live IDE and its agent bridge usually hang off that one, and
   the measurement is which door a POST reached, which other traffic would
   muddy.

   Needs: a reflector on 9090 and the -TEST vfuels.
   Run: node bus-locality-probe.js                                           */
const http = require('http');
const { spawn } = require('child_process');
const path = require('path');
const { sleep, launchBrowser, bootIDE, evalDoIt, makeChecker } = require('./harness');

const A_PORT = 8091;                            // the agent's machine
const B_PORT = 8092;                            // a second, agent-less front door
const A_ORIGIN = 'http://localhost:' + A_PORT;
const B_ORIGIN = 'http://localhost:' + B_PORT;
const AGENT = 'localagent', CHAT = 'ProbeLocalChat', REPLY = 'LOCALITY-REPLY-909090';
const SESSION = 'busloc' + Math.floor(Date.now() / 1000);
const { check, summary } = makeChecker();

const ideUrl = origin => origin
  + '/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=' + SESSION
  + '&pwd=test&appId=org.newspeaklanguage.busloc&apiKey=none'
  + '&reflector=ws://localhost:9090&files=/files';

function get(origin, p) {
  return new Promise((res, rej) => { http.get(origin + p, r => {
    let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) }).on('error', rej) });
}
function agentsOn(origin, token) {
  return new Promise((res, rej) => {
    http.get(origin + '/_ns/bus/agents', { headers: { 'X-NS-Token': token } }, r => {
      let b = ''; r.on('data', c => b += c);
      r.on('end', () => { try { res(JSON.parse(b).agents) } catch (e) { rej(e) } });
    }).on('error', rej);
  });
}
function post(origin, p, obj, token) {
  return new Promise((res, rej) => {
    const d = JSON.stringify(obj);
    const rq = http.request(origin + p, { method: 'POST', headers: {
      'Content-Type': 'application/json', 'X-NS-Token': token,
      'Content-Length': Buffer.byteLength(d) } },
      r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) });
    rq.on('error', rej); rq.end(d);
  });
}

/* Count every completion_request that reaches a given bus, and answer only the
   ones on A's - that is what makes a misrouted request show up as a hang plus
   a nonzero count on the wrong door, rather than silently working. */
function watchBus(origin, token, name, counter, answer) {
  return new Promise(resolve => {
    const url = origin + '/_ns/bus?token=' + encodeURIComponent(token)
      + (name ? '&name=' + encodeURIComponent(name) : '');
    const req = http.get(url, res => {
      let buf = '';
      res.on('data', chunk => { buf += chunk;
        let i; while ((i = buf.indexOf('\n\n')) >= 0) {
          const frame = buf.slice(0, i); buf = buf.slice(i + 2);
          const line = frame.split('\n').find(l => l.startsWith('data:'));
          if (!line) continue;
          let msg; try { msg = JSON.parse(line.slice(5).trim()) } catch (e) { continue }
          if (msg.kind !== 'completion_request' || msg.to !== AGENT) continue;
          counter.n++; counter.corr.push(msg.corr_id);
          if (!answer) continue;
          post(origin, '/_ns/bus', { to: msg.from, from: AGENT, kind: 'completion_response',
            corr_id: msg.corr_id, response: { id: 'msg_1', type: 'message', role: 'assistant',
              content: [{ type: 'text', text: REPLY }], stop_reason: 'end_turn',
              usage: { input_tokens: 1, output_tokens: 1 } } }, token).catch(() => {});
        }
      });
      resolve(req);
    });
  });
}

const DOIT = "[:g | [ | p msgs | p:: platform aiAccess BusProvider agentName: '" + AGENT
  + "' chat: '" + CHAT + "' port: ide aiSupport. "
  + "msgs:: platform collections List new. p addUserText: 'ping' toMessages: msgs. "
  + "(p complete: (p messagesAsRequestPayload: msgs) system: '' notices: platform collections List new tools: nil maxTokens: 16) "
  + "then: [:r | g at: 'reply' put: (p extractTextFromResponse: r). nil ] "
  + "onError: [:e | g at: 'reply' put: 'ERR ' , e printString. nil ] ] "
  + "on: Exception do: [:e | g at: 'reply' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";

function startFrontDoor(port) {
  // NS_WEB_ROOT points both doors at an alternate copy of out/ - the way to try
  // a runtime change without writing into the tree a live session is served from.
  const args = [path.join(__dirname, '..', 'tool', 'cors-proxy.py'), String(port), '--bus'];
  if (process.env.NS_WEB_ROOT) args.push('--root', process.env.NS_WEB_ROOT);
  return spawn('python3', args, { stdio: 'ignore' });
}
async function tokenOf(origin) {
  for (let i = 0; i < 60; i++) {
    try { return JSON.parse(await get(origin, '/_ns/token')).token } catch (e) { await sleep(500) }
  }
  return undefined;
}

/* A front door already on the port would answer in place of the one this probe
   starts - serving a different tree, counting nobody's bus traffic - and every
   assertion below would then be about the wrong server. A crashed earlier run
   leaves exactly that behind, so refuse rather than measure the wrong thing. */
function portFree(port) {
  return new Promise(res => {
    const s = require('net').createServer();
    s.once('error', () => res(false));
    s.once('listening', () => s.close(() => res(true)));
    s.listen(port, '127.0.0.1');
  });
}

async function main() {
  for (const p of [A_PORT, B_PORT]) if (!await portFree(p)) {
    console.log('port ' + p + ' is already in use - a stale front door from an earlier run?');
    process.exitCode = 1; return;
  }
  const proxies = [startFrontDoor(A_PORT), startFrontDoor(B_PORT)];
  const tokenA = await tokenOf(A_ORIGIN), tokenB = await tokenOf(B_ORIGIN);
  if (!tokenA || !tokenB) {
    console.log('a front door never came up (A=' + !!tokenA + ' B=' + !!tokenB + ')');
    proxies.forEach(p => p.kill()); process.exitCode = 1; return;
  }
  console.log('front doors: A=' + A_ORIGIN + ' (agent here), B=' + B_ORIGIN + ' (no agent)');

  const onA = { n: 0, corr: [] }, onB = { n: 0, corr: [] };
  const agent = await watchBus(A_ORIGIN, tokenA, AGENT, onA, true);
  const spy = await watchBus(B_ORIGIN, tokenB, null, onB, false);   // unnamed: a listener, not an agent
  await sleep(1500);
  const listed = await agentsOn(A_ORIGIN, tokenA);
  const listedB = await agentsOn(B_ORIGIN, tokenB);
  check('the agent is listed on A and NOT on B', listed.includes(AGENT) && !listedB.includes(AGENT),
    'A=' + JSON.stringify(listed) + ' B=' + JSON.stringify(listedB));

  const clients = [];
  const A = await launchBrowser({ port: 9821, tag: 'loc-a', session: SESSION }); clients.push(A);
  if (!await bootIDE(A, ideUrl(A_ORIGIN))) { check('A boots', false, A.logs.slice(-4).join(' | ')); return done(clients, [agent, spy], proxies) }
  const B = await launchBrowser({ port: 9822, tag: 'loc-b', session: SESSION }); clients.push(B);
  if (!await bootIDE(B, ideUrl(B_ORIGIN))) { check('B boots', false, B.logs.slice(-4).join(' | ')); return done(clients, [agent, spy], proxies) }
  await sleep(5000);

  console.log('\n--- one bus completion; the agent is only reachable from A ---');
  /* Driven from B on purpose: the client that CANNOT reach the agent is the one
     the user typed into, so nothing about who asks first can carry the test. */
  const rb = await evalDoIt(B, DOIT, 'reply', 90);
  check('B (no agent here) still gets the reply', rb === REPLY, JSON.stringify(rb));
  let ra; for (let i = 0; i < 40; i++) { await sleep(1500); ra = await A.v('window.reply'); if (ra !== undefined) break }
  check('A gets the SAME reply', ra === REPLY, JSON.stringify(ra));
  check('the request went to the agent EXACTLY ONCE', onA.n === 1, 'A-bus=' + onA.n + ' corr=' + JSON.stringify(onA.corr));
  check('nothing was posted into the agent-less bus', onB.n === 0, 'B-bus=' + onB.n + ' corr=' + JSON.stringify(onB.corr));

  console.log('\n--- a late joiner, also without the agent ---');
  const C = await launchBrowser({ port: 9823, tag: 'loc-c', session: SESSION }); clients.push(C);
  if (!await bootIDE(C, ideUrl(B_ORIGIN))) check('C boots', false, C.logs.slice(-4).join(' | '));
  else {
    await sleep(10000);
    check('replay did NOT re-issue the request', onA.n === 1, 'A-bus=' + onA.n);
    check('replay posted nothing into the agent-less bus', onB.n === 0, 'B-bus=' + onB.n);
    const orph = C.logs.filter(l => l.includes('no subscriber'));
    check('joiner replay is orphan-free', orph.length === 0, orph.slice(0, 2).join(' | '));
  }

  const errs = [A, B].map(b => b.logs.filter(l => l.startsWith('[error]')));
  console.log('  console errors A/B:', errs.map(e => e.length).join('/'));
  errs.flat().slice(0, 4).forEach(l => console.log('    ' + l.slice(0, 240)));
  if (process.env.BUSLOC_TRACE) for (const [n, b] of [['A', A], ['B', B]]) {
    const d = await b.v("JSON.stringify({model: typeof theModel, awaitFn: typeof (theModel && theModel.coordinatedFetch_await), fetches: theModel && theModel.coordinatedFetches, subs: Array.from(newspeakSubscriptions.keys()).filter(k=>k.indexOf('nscoordfetch')===0), held: Array.from(nsPendingCoordAnswers.keys())})");
    console.log('  ' + n + ' state: ' + d);
  }
  if (process.env.BUSLOC_TRACE) [['A', A], ['B', B]].forEach(([n, b]) => {
    console.log('  --- ' + n + ' trace ---');
    b.logs.filter(l => /BUSLOC|nscoordfetch|no subscriber|holding|delivering/i.test(l))
      .slice(0, 60).forEach(l => console.log('    ' + n + ' ' + l.slice(0, 220)));
  });
  return done(clients, [agent, spy], proxies);
}
function done(bs, reqs, proxies) {
  bs.forEach(b => { try { b.proc.kill() } catch (e) {} });
  reqs.forEach(r => { try { r.destroy() } catch (e) {} });
  proxies.forEach(p => { try { p.kill() } catch (e) {} });
  summary();
}
main().catch(e => { console.error(e); process.exit(1) });
