/* Label census: boot ONE client on the given build, open a workspace, and
 * print what the fragment registry holds for the divergence alarm's label
 * check (croquet-post.js nsFragmentLabels; HopscotchForCroquet croquetLabel):
 * per button/link subscription, its address and label. A diagnostic for the
 * PROVOKE mode of setup-latejoin-probe.js when it finds no labelled pair.
 *
 *   croquet-probes/run.sh NS_SUFFIX=-TEST NS_PAGE=croquetpsoup-test.html label-census-probe.js
 */
if (!process.env.NODE_PATH) {
  process.env.NODE_PATH = '/Users/gbracha/newspeak/dev/web/croquet/packages/reflector/node_modules';
  require('module').Module._initPaths();
}
const { launchBrowser, bootIDE } = require('./harness');
const ORIGIN = 'http://localhost:8080';
const SUFFIX = process.env.NS_SUFFIX || '';
const NS_PAGE_FILE = process.env.NS_PAGE || 'croquetpsoup.html';
const SESSION = 'labelcensus' + Math.floor(Date.now() / 1000);
const URL = ORIGIN + '/' + NS_PAGE_FILE + '?snapshot=CroquetHopscotchWebIDE' + SUFFIX +
  '.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.sljprobe&apiKey=none' +
  '&reflector=ws://localhost:9090&files=/files';

async function main() {
  const A = await launchBrowser({ port: 9831, tag: 'lc-a', session: SESSION });
  const booted = await bootIDE(A, URL);
  console.log('booted:', booted);
  console.log('alarm present:', await A.v("typeof nsCheckLabel + '/' + typeof nsFragmentLabels"));
  console.log('labels registered:', await A.v("typeof nsFragmentLabels === 'undefined' ? 'n/a' : nsFragmentLabels.size"));
  const rows = JSON.parse(await A.v("JSON.stringify(Array.from(newspeakSubscriptions.values()).map(function(v){return [v.scope, v.eventSpec, v.label === undefined ? '(undefined)' : v.label]}))"));
  console.log('subscriptions:', rows.length);
  rows.slice(0, 40).forEach(r => console.log('  ' + r.join('  ')));
  const errs = A.logs.filter(l => /error|DNU|doesNotUnderstand|croquetLabel/i.test(l));
  console.log('console lines of interest:', errs.length);
  errs.slice(0, 10).forEach(l => console.log('  ' + l.slice(0, 240)));
  try { A.proc.kill() } catch (e) {}
}
main().catch(e => { console.error(e); process.exit(1) });
