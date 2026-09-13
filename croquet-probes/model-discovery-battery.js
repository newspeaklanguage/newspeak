/* Verification battery for AI model discovery through the host fetcher.
   Credential-free: OpenAICompatibleProvider against a local mock endpoint
   (out/mockai/v1/models) served by the front door, so no API key is involved
   and the payload is fixed.

     T1 PLAIN     regular platform discovers through Host>>fetchText:headers:
                  (the regression guard for the psoup/newspeak Host.ns split)
     T2 CROQUET   single client discovers through the coordinated path
     T3 ELECTION  two clients converge on the SAME list, and exactly ONE of
                  them performed the network fetch
     T4 JOINER    a late joiner reaches the same list from the recorded
                  result without fetching at all

   Run: node model-discovery-battery.js            (all)
        node model-discovery-battery.js plain      (T1 only)
*/
const { spawn } = require('child_process');
const { sleep, launchBrowser, click, waitFor, bootIDE, evalDoIt, makeChecker } = require('./harness');
const ORIGIN = 'http://localhost:8080/';
const SESSION = 'mdb' + Math.floor(Date.now()/1000);
const MOCK_BASE = 'http://localhost:8080/mockai/v1';
const WANT = 'mock-alpha,mock-beta,mock-gamma,';
const SUF = process.env.NS_SUFFIX || '';
const PLAIN_URL = ORIGIN + 'primordialsoup.html?snapshot=HopscotchWebIDE' + SUF + '.vfuel';
const CROQUET_URL = ORIGIN + 'croquetpsoup.html?snapshot=CroquetHopscotchWebIDE' + SUF + '.vfuel&sessionId='
  + SESSION + '&pwd=test&appId=org.newspeaklanguage.mdb&apiKey=none&reflector=ws://localhost:9090&files=/files';
const DOCNAME = 'ProbeDoc';
const COUNTER = "window.nsMockFetches=0;window.nsDocFetches=0;"
  + "(function(){var f=window.fetch;window.fetch=function(u){var s=String(u);"
  + "if(s.indexOf('mockai')>=0)window.nsMockFetches++;"
  + "if(s.indexOf('" + "ProbeDoc" + ".zip')>=0)window.nsDocFetches++;"
  + "return f.apply(this,arguments)}})();"
  + "(function(){var X=window.XMLHttpRequest;window.XMLHttpRequest=function(){var r=new X();var o=r.open;"
  + "r.open=function(m,u){if(String(u).indexOf('" + "ProbeDoc" + ".zip')>=0)window.nsDocFetches++;return o.apply(r,arguments)};return r}})();";
const { check, summary } = makeChecker();

/* Build a provider on the mock endpoint and refresh; report the resulting list. */
const REFRESH = (flag) => "[:g | [ | p | p:: platform aiAccess OpenAICompatibleProvider apiKey: '' model: 'mock-alpha' baseUrl: '" + MOCK_BASE + "'. "
  + "p refreshAvailableModelsThen: [ | s | s:: ''. p availableModels do: [:x | s:: s , x , ',' ]. g at: '" + flag + "' put: s ] "
  + "onError: [:m | g at: '" + flag + "' put: 'ERR ' , m printString ] ] on: Exception do: [:e | g at: '" + flag + "' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";

/* Read the list from cache only (no fetch) - for a client that must converge
   without running its own discovery. */
const READ = (flag) => "[:g | [ | p s | p:: platform aiAccess OpenAICompatibleProvider apiKey: '' model: 'mock-alpha' baseUrl: '" + MOCK_BASE + "'. "
  + "s:: ''. p availableModels do: [:x | s:: s , x , ',' ]. g at: '" + flag + "' put: s ] on: Exception do: [:e | g at: '" + flag + "' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";

/* A non-loopback address the browser can actually resolve: mDNS (.local) does
   not resolve inside headless Chrome, so use the first non-internal IPv4. */
function nonLoopbackHost(){
  const os = require('os'), ifs = os.networkInterfaces();
  for (const name of Object.keys(ifs))
    for (const a of ifs[name])
      if (a.family === 'IPv4' && !a.internal) return a.address;
  return null;   // offline: no non-loopback address to serve from
}

/* A dumb static server on its own port: no /_ns, no CORS headers, no
   Cache-Control - i.e. what a deployed Ampleforth site is served from. */
function bareServer(port){
  return spawn('python3', ['-m','http.server', String(port), '--bind', '0.0.0.0', '--directory', 'out'], {stdio:'ignore'});
}

async function main(){
  const only = process.argv[2];
  console.log('battery: mock endpoint ' + MOCK_BASE + '   expect: ' + WANT);

  if (!only || only === 'plain') {
    console.log('\n--- T1 PLAIN PLATFORM (regression guard for Host fetchText:headers:) ---');
    const P = await launchBrowser({port:9601,tag:'mdb-plain',session:SESSION,initScript:COUNTER});
    if (!await bootIDE(P, PLAIN_URL)) { check('plain IDE boots', false, P.logs.slice(-4).join(' | ')); }
    else {
      const got = await evalDoIt(P, REFRESH('t1'), 't1', 25);
      check('plain platform discovers through the host fetcher', got === WANT, JSON.stringify(got));
      check('plain platform actually hit the network', (await P.v('window.nsMockFetches')) >= 1, 'fetches=' + await P.v('window.nsMockFetches'));

      // T8: two overlapping loads of ONE document, on the platform with no
      // coordination at all. Nothing here ever deduplicated - the old plain
      // path ran the fetcher block immediately, with no key and no pending
      // list - so without the in-flight map this fetches and unzips twice.
      // Two lazy transclusions of the same document on one page do exactly this.
      const DOUBLE = "[:g | [ ide documents loadFromServerNamed: '" + DOCNAME + "' "
        + "ifSuccess: [:d | g at: 't8a' put: 'OK' ] ifFailure: [:m | g at: 't8a' put: 'FAILED ' , m printString ]. "
        + "ide documents loadFromServerNamed: '" + DOCNAME + "' "
        + "ifSuccess: [:d | g at: 't8b' put: 'OK' ] ifFailure: [:m | g at: 't8b' put: 'FAILED ' , m printString ] ] "
        + "on: Exception do: [:e | g at: 't8b' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";
      const second = await evalDoIt(P, DOUBLE, 't8b', 30);
      const first = await P.v('window.t8a');
      check('T8 both overlapping loads are answered', first === 'OK' && second === 'OK', JSON.stringify([first, second]));
      check('T8 the document was fetched ONCE, not twice', (await P.v('window.nsDocFetches')) === 1, 'fetches=' + await P.v('window.nsDocFetches'));
    }
    P.proc.kill();
  }
  if (only === 'plain') { summary(); return; }
  if (only === 'static') { await runStaticOriginTest(); summary(); return; }

  console.log('\n--- T2/T3 CROQUET: two clients, election ---');
  const A = await launchBrowser({port:9602,tag:'mdb-a',session:SESSION,initScript:COUNTER});
  if (!await bootIDE(A, CROQUET_URL)) { check('croquet client A boots', false, A.logs.slice(-4).join(' | ')); summary(); A.proc.kill(); return; }
  const B = await launchBrowser({port:9603,tag:'mdb-b',session:SESSION,initScript:COUNTER});
  if (!await bootIDE(B, CROQUET_URL)) { check('croquet client B boots', false, B.logs.slice(-4).join(' | ')); summary(); A.proc.kill(); B.proc.kill(); return; }
  await sleep(3000);

  const gotA = await evalDoIt(A, REFRESH('t2'), 't2', 30);
  check('T2 croquet discovers through the coordinated path', gotA === WANT, JSON.stringify(gotA));
  // B must converge without running its own refresh: read cache after A's recorded result lands.
  let gotB;
  for (let i=0;i<20;i++){ await sleep(1500); gotB = await evalDoIt(B, READ('t3b'+i), 't3b'+i, 3); if (gotB === WANT) break; }
  check('T3 client B converges on the same list', gotB === WANT, JSON.stringify(gotB));
  const fA = await A.v('window.nsMockFetches'), fB = await B.v('window.nsMockFetches');
  check('T3 exactly one client performed the fetch (election)', fA + fB === 1, 'A:'+fA+' B:'+fB);

  console.log('\n--- T4 LATE JOINER ---');
  const C = await launchBrowser({port:9604,tag:'mdb-c',session:SESSION,initScript:COUNTER});
  if (!await bootIDE(C, CROQUET_URL)) { check('late joiner boots', false, C.logs.slice(-4).join(' | ')); }
  else {
    let gotC;
    for (let i=0;i<20;i++){ await sleep(1500); gotC = await evalDoIt(C, READ('t4c'+i), 't4c'+i, 3); if (gotC === WANT) break; }
    check('T4 late joiner reaches the same list', gotC === WANT, JSON.stringify(gotC));
    check('T4 late joiner did not fetch', (await C.v('window.nsMockFetches')) === 0, 'fetches=' + await C.v('window.nsMockFetches'));
    const orphans = C.logs.filter(l=>l.includes('no subscriber'));
    check('T4 joiner replay is orphan-free', orphans.length === 0, orphans.slice(0,2).join(' | '));
  }
  console.log('\n--- T5 DOCUMENT LOAD through the host fetcher (no app-supplied key) ---');
  const LOAD = (flag) => "[:g | [ ide documents loadFromServerNamed: '" + DOCNAME + "' "
    + "ifSuccess: [:d | g at: '" + flag + "' put: 'LOADED ' , d name ] "
    + "ifFailure: [:m | g at: '" + flag + "' put: 'FAILED ' , m printString ] ] "
    + "on: Exception do: [:e | g at: '" + flag + "' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";
  const dA = await evalDoIt(A, LOAD('t5a'), 't5a', 30);
  check('T5 client A loads the document through the host fetcher', String(dA).indexOf('LOADED') === 0, JSON.stringify(dA));
  let dB;
  for (let i=0;i<20;i++){ await sleep(1500); dB = await evalDoIt(B, LOAD('t5b'+i), 't5b'+i, 6); if (String(dB).indexOf('LOADED') === 0) break; }
  check('T5 client B gets the same document', String(dB).indexOf('LOADED') === 0, JSON.stringify(dB));
  // C (the T4 joiner) is still live and replays A's doIt, so it is a candidate
  // initiator too: the election is across every live client, not just A and B.
  const dfA = await A.v('window.nsDocFetches'), dfB = await B.v('window.nsDocFetches'),
        dfC = await C.v('window.nsDocFetches');
  check('T5 exactly one client fetched the zip (election)', dfA + dfB + dfC === 1, 'A:'+dfA+' B:'+dfB+' C:'+dfC);

  console.log('\n--- T6 LATE JOINER, DOCUMENT ---');
  const PRESENT = (flag) => "[:g | [ g at: '" + flag + "' put: ((ide namespacing Root at: '" + DOCNAME + "' ifAbsent: [ nil ]) isNil "
    + "ifTrue: [ 'ABSENT' ] ifFalse: [ 'PRESENT' ]) ] on: Exception do: [:e | g at: '" + flag + "' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";
  const D = await launchBrowser({port:9605,tag:'mdb-d',session:SESSION,initScript:COUNTER});
  if (!await bootIDE(D, CROQUET_URL)) { check('T6 late joiner boots', false, D.logs.slice(-4).join(' | ')); }
  else {
    let present;
    for (let i=0;i<20;i++){ await sleep(1500); present = await evalDoIt(D, PRESENT('t6'+i), 't6'+i, 6); if (present === 'PRESENT') break; }
    check('T6 joiner has the document after replay', present === 'PRESENT', JSON.stringify(present));
    check('T6 joiner did NOT fetch the zip', (await D.v('window.nsDocFetches')) === 0, 'fetches=' + await D.v('window.nsDocFetches'));
    const orph = D.logs.filter(l=>l.includes('no subscriber'));
    check('T6 joiner replay is orphan-free', orph.length === 0, orph.slice(0,2).join(' | '));
    D.proc.kill();
  }

  const errs = [A,B,C].map(b=>b.logs.filter(l=>l.startsWith('[error]')).length);
  console.log('  console errors A/B/C: ' + errs.join('/'));
  A.proc.kill(); B.proc.kill(); C.proc.kill();
  await runStaticOriginTest();
  summary();
}
async function runStaticOriginTest(){
  console.log('\n--- T7 BARE, NON-LOOPBACK ORIGIN (no /_ns services; the deploy shape) ---');
  const PORT = 8099;
  const srv = bareServer(PORT);
  await sleep(2500);
  // Address the origin by a NON-loopback hostname, which is what a deployed
  // page is. No localStorage setting: the point is that the built-in
  // localhost:8080 fallback must not be offered to a page like this at all.
  const host = nonLoopbackHost();
  if (!host) { console.log('  SKIP  T7 needs a non-loopback address; this machine has none (offline?)'); srv.kill(); return; }
  const S = await launchBrowser({port:9606,tag:'mdb-static',session:SESSION,initScript:COUNTER});
  const staticUrl = 'http://' + host + ':' + PORT + '/primordialsoup.html?snapshot=HopscotchWebIDE' + SUF + '.vfuel';
  console.log('  origin: ' + staticUrl.split('/primordialsoup')[0]);
  if (!await bootIDE(S, staticUrl)) { check('T7 IDE boots from a bare static origin', false, S.logs.slice(-5).join(' | ')); }
  else {
    const LOAD = "[:g | [ ide documents loadFromServerNamed: '" + DOCNAME + "' "
      + "ifSuccess: [:d | g at: 't7' put: 'LOADED ' , d name ] "
      + "ifFailure: [:m | g at: 't7' put: 'FAILED ' , m printString ] ] "
      + "on: Exception do: [:e | g at: 't7' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";
    const got = await evalDoIt(S, LOAD, 't7', 30);
    check('T7 document loads with no host services present', String(got).indexOf('LOADED') === 0, JSON.stringify(got));
    // Host discovery probes the page origin and then falls back to a dev front
    // door (default http://localhost:8080), which on this machine is running -
    // so without disabling that fallback the probe succeeds and reports true.
    // A real visitor to a deployed site has no such server; 'off' models them.
    const avail = await evalDoIt(S, "[:g | [ g at: 't7b' put: platform host fetchAvailable printString ] "
      + "on: Exception do: [:e | g at: 't7b' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global", 't7b', 20);
    check('T7 dev fallback NOT offered to a non-loopback page (fetchAvailable false)', avail === 'false', JSON.stringify(avail));
  }
  S.proc.kill(); srv.kill();
}
main().catch(e=>{console.error(e);process.exit(1)});
