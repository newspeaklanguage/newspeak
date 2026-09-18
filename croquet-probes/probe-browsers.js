/* Housekeeping for the probes' headless Chromes. A probe that dies early (or is
   stopped) leaves its browsers behind, holding their debugging ports; the next
   run then talks to a stale browser or cannot start one.

     croquet-probes/run.sh probe-browsers.js          list them, and what each port answers
     croquet-probes/run.sh probe-browsers.js --kill   also terminate them

   Only processes whose command line names a probe profile directory
   (--user-data-dir=/tmp/cq-...) are touched; your own Chrome is not. */
const { execSync } = require('child_process');
const http = require('http');
const kill = process.argv.includes('--kill');
function getText(port, path) {
  return new Promise(res => {
    const rq = http.get({ host: '127.0.0.1', port, path, timeout: 3000 }, r => {
      let b = ''; r.on('data', c => b += c); r.on('end', () => res(b));
    });
    rq.on('timeout', () => { rq.destroy(); res('(timeout)'); });
    rq.on('error', e => res('(' + e.code + ')'));
  });
}
(async () => {
  let lines = [];
  try { lines = execSync("ps -axo pid=,command= | grep -- '--user-data-dir=/tmp/cq-' | grep -v grep", { encoding: 'utf8' }).split('\n').filter(Boolean); } catch (e) {}
  const mains = lines.filter(l => l.includes('--remote-debugging-port='));
  console.log(mains.length + ' probe browser(s), ' + lines.length + ' process(es) in all');
  for (const l of mains) {
    const pid = Number(l.trim().split(/\s+/)[0]);
    const port = Number((l.match(/--remote-debugging-port=(\d+)/) || [])[1]);
    const dir = (l.match(/--user-data-dir=(\S+)/) || [])[1];
    const version = await getText(port, '/json/version');
    const targets = await getText(port, '/json');
    let pages = '?';
    try { pages = JSON.parse(targets).filter(t => t.type === 'page').map(t => t.url).join(', ') || '(no page target)'; } catch (e) { pages = targets.slice(0, 80); }
    let browser = '?';
    try { browser = JSON.parse(version).Browser; } catch (e) { browser = version.slice(0, 60); }
    console.log('  pid ' + pid + '  port ' + port + '  ' + dir + '\n    browser: ' + browser + '\n    pages: ' + pages);
    if (kill) { try { process.kill(pid, 'SIGTERM'); console.log('    terminated'); } catch (e) { console.log('    could not terminate: ' + e.message); } }
  }
})();
