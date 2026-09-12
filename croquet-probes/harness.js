/* Shared CDP harness for the probe batteries.
 *
 * Three probes had grown near-identical copies of this: launching headless
 * Chrome, finding a page target, driving Runtime.evaluate over the DevTools
 * socket, booting the IDE, and evaluating a Newspeak doIt in a workspace.
 * A fourth copy was about to appear, so it lives here instead.
 *
 * Nothing here knows what is being tested; probes supply the URLs, the
 * assertions and the fixtures.
 */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');

const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const sleep = ms => new Promise(r => setTimeout(r, ms));

function getJson(port, path) {
  return new Promise((res, rej) => {
    http.get({ host: '127.0.0.1', port, path }, r => {
      let b = ''; r.on('data', c => b += c);
      r.on('end', () => { try { res(JSON.parse(b)) } catch (e) { rej(e) } });
    }).on('error', rej);
  });
}

/* Launch headless Chrome and attach to its page target.
 * Chrome needs a beat before /json answers, and on a loaded machine the first
 * page target can lag, so poll generously and fall back to minting one
 * (PUT /json/new) rather than failing what is really a slow start. */
async function launchBrowser({ port, tag, session, initScript }) {
  const proc = spawn(CHROME, [
    '--headless=new', '--remote-debugging-port=' + port, '--remote-allow-origins=*',
    '--user-data-dir=/tmp/cq-' + tag + '-' + session, '--no-first-run', '--disable-gpu',
    '--disable-background-timer-throttling', '--disable-renderer-backgrounding', 'about:blank'
  ], { stdio: 'ignore' });
  await sleep(1200);
  let page;
  for (let i = 0; i < 200; i++) {
    try { const t = await getJson(port, '/json'); page = t && t.find(x => x.type === 'page'); if (page) break } catch (e) {}
    if (i === 60) {
      try {
        await new Promise((res, rej) => {
          const rq = http.request({ host: '127.0.0.1', port, path: '/json/new?about:blank', method: 'PUT' },
            r => { r.resume(); r.on('end', res) });
          rq.on('error', rej); rq.end();
        });
      } catch (e) {}
    }
    await sleep(300);
  }
  if (!page) throw new Error('no CDP page target on port ' + port + ' after ~60s');

  const ws = new WebSocket(page.webSocketDebuggerUrl, { perMessageDeflate: false });
  await new Promise(r => ws.on('open', r));
  let id = 0; const pending = new Map(); const logs = [];
  ws.on('message', raw => {
    const m = JSON.parse(raw);
    if (m.id && pending.has(m.id)) { pending.get(m.id)(m.result); pending.delete(m.id); return }
    if (m.method === 'Runtime.consoleAPICalled')
      logs.push('[' + m.params.type + '] ' + m.params.args
        .map(x => x.value !== undefined ? String(x.value) : (x.description || '')).join(' '));
  });
  const send = (meth, par) => new Promise(res => {
    const i = ++id; pending.set(i, res);
    ws.send(JSON.stringify({ id: i, method: meth, params: par || {} }));
  });
  await send('Runtime.enable'); await send('Page.enable');
  if (initScript) await send('Page.addScriptToEvaluateOnNewDocument', { source: initScript });
  const v = async e => {
    const r = await send('Runtime.evaluate', { expression: e, returnByValue: true });
    return r && r.result ? r.result.value : undefined;
  };
  return { proc, v, logs, navigate: url => send('Page.navigate', { url }) };
}

/* Click the LAST element whose trimmed text is exactly `label`. Hopscotch
 * renders buttons as plain elements, so a real MouseEvent triple is what
 * reaches its handlers - CDP's dispatchMouseEvent does not. */
const click = label =>
  `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label'))` +
  `.filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];` +
  `if(!e)return 'NOBTN';['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(` +
  `new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'CLICKED'})()`;

async function waitFor(b, pred, ms) {
  const t0 = Date.now();
  while (Date.now() - t0 < ms) { if (await b.v(pred)) return true; await sleep(1000) }
  return false;
}

/* Boot the IDE and open a workspace, so doIts have somewhere to run. */
async function bootIDE(b, url, { bootMs = 240000, settleMs = 4000 } = {}) {
  await b.navigate(url);
  if (!await waitFor(b, "document.body && document.body.innerText.includes('Workspaces')", bootMs)) return false;
  await sleep(settleMs);
  await b.v(click('Workspaces'));
  await waitFor(b, "document.body.innerText.includes('Evaluate')", 30000);
  await sleep(2000);
  return true;
}

/* Evaluate a Newspeak doIt in the workspace and wait for it to park a result
 * on `window[flag]`. The re-select before clicking is deliberate: a render
 * between setValue and the click can collapse the selection, and Evaluate
 * Selection reads the selection at dispatch. */
async function evalDoIt(b, src, flag, secs) {
  await b.v(`(function(){var c=document.querySelectorAll('.CodeMirror');var cm=c[c.length-1].CodeMirror;` +
            `cm.focus();cm.setValue(${JSON.stringify(src)});cm.execCommand('selectAll');return 1})()`);
  await sleep(1500);
  await b.v("(function(){var c=document.querySelectorAll('.CodeMirror');var cm=c[c.length-1].CodeMirror;" +
            "cm.focus();cm.execCommand('selectAll');return 1})()");
  await b.v(click('Evaluate Selection'));
  for (let i = 0; i < (secs || 30); i++) {
    await sleep(1000);
    const r = await b.v(`window[${JSON.stringify(flag)}]`);
    if (r !== undefined) return r;
  }
  return undefined;
}

function makeChecker() {
  let pass = 0, fail = 0;
  return {
    check(label, ok, detail) {
      ok ? pass++ : fail++;
      console.log((ok ? '  PASS  ' : '  FAIL  ') + label + (detail ? '   ' + detail : ''));
    },
    summary() {
      console.log('\n==== ' + pass + ' passed, ' + fail + ' failed ====');
      process.exitCode = fail ? 1 : 0;
    },
    get failures() { return fail }
  };
}

module.exports = { CHROME, sleep, getJson, launchBrowser, click, waitFor, bootIDE, evalDoIt, makeChecker };
