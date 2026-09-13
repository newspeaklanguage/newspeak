/* Exercise the host's tool-result sharing seam directly, one client, so a
 * silent fallback in the AI tool loop can be told apart from a broken seam.
 *
 *   NS_SUFFIX=-TEST NS_PAGE=croquetpsoup-test.html \
 *     ~/software/emsdk-main/node/22.16.0_64bit/bin/node croquet-probes/share-probe.js
 *
 * Three doIts: (1) platform host performer shareText:via: with a constant;
 * (2) the same through an AIAccess Session's shareToolText:forCall: (a fresh
 * session on the Anthropic provider needs no network for this); (3) what
 * `platform host` and its performer are. Each parks its outcome on a JS
 * global, RAISED/BROKEN/OK, so exceptions inside promise machinery surface.
 */
if (!process.env.NODE_PATH) {
  process.env.NODE_PATH = '/Users/gbracha/newspeak/dev/web/croquet/packages/reflector/node_modules';
  require('module').Module._initPaths();
}
const { sleep, launchBrowser, bootIDE, evalDoIt, makeChecker } = require('./harness');
const { check, summary } = makeChecker();
const SUFFIX = process.env.NS_SUFFIX || '';
const NS_PAGE_FILE = process.env.NS_PAGE || 'croquetpsoup.html';
const SESSION = 'shareprobe' + Math.floor(Date.now() / 1000);
const URL = 'http://localhost:8080/' + NS_PAGE_FILE + '?snapshot=CroquetHopscotchWebIDE' + SUFFIX +
  '.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.shareprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';

const HOST_DOIT = "[:g | [ | p | p:: platform host performer shareText: 'probe share' via: [:ok :fail | ok value: 'hello-shared'. nil ]. " +
  "platform actors Promise when: p fulfilled: [:t | g at: 'shareHost' put: 'OK ' , t printString. nil ] broken: [:r | g at: 'shareHost' put: 'BROKEN ' , r printString. nil ] ] " +
  "on: Exception do: [:e | g at: 'shareHost' put: 'RAISED ' , e printString ]. 'GO' ] value: platform js global";
const SESSION_DOIT = "[:g | [ | s p | s:: platform aiAccess Session provider: (platform aiAccess AnthropicProvider apiKey: 'none' model: 'x') tools: {}. " +
  "p:: s shareToolText: 'local-text' forCall: 'toolu_probe'. " +
  "p then: [:t | g at: 'shareSession' put: 'OK ' , t printString. nil ] onError: [:r | g at: 'shareSession' put: 'BROKEN ' , r printString. nil ] ] " +
  "on: Exception do: [:e | g at: 'shareSession' put: 'RAISED ' , e printString ]. 'GO' ] value: platform js global";
const WHO_DOIT = "[:g | [ g at: 'who' put: 'host=' , platform host printString , ' performer=' , platform host performer printString ] " +
  "on: Exception do: [:e | g at: 'who' put: 'RAISED ' , e printString ]. 'GO' ] value: platform js global";

async function main() {
  const A = await launchBrowser({ port: 9831, tag: 'share-a', session: SESSION });
  if (!await bootIDE(A, URL)) { check('A boots', false, A.logs.slice(-4).join(' | ')); return done([A]) }
  const who = await evalDoIt(A, WHO_DOIT, 'who', 30);
  console.log('who:', who);
  const h = await evalDoIt(A, HOST_DOIT, 'shareHost', 30);
  console.log('host seam:', h);
  check('host performer shareText:via: answers the text', typeof h === 'string' && h.startsWith('OK'), String(h));
  /* The Session-level seam (shareToolText:forCall:) is protected, so it is
     exercised only through a real tool round: setup-latejoin-probe.js. Its
     fallbacks now print a 'shareToolText:' console line, which that probe's
     A logs would show. */
  const errs = A.logs.filter(l => l.startsWith('[error]'));
  console.log('console errors:', errs.length); errs.slice(0, 6).forEach(l => console.log('    ' + l.slice(0, 300)));
  console.log('--- console tail ---'); console.log(A.logs.slice(-8).join('\n'));
  return done([A]);
}
function done(bs) { bs.forEach(b => { try { b.proc.kill() } catch (e) {} }); summary(); }
main().catch(e => { console.error(e); process.exit(1) });
