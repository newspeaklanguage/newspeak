// Cross-origin persistence rebase probe.
// Phase A: client on the localhost origin creates a fresh CroquetCounterApp
//   session, clicks increment 3x, waits for persistence, leaves; island dies.
// Phase B: cold joiner on the macbook-pro-4 origin must (a) come up synced,
//   (b) show the persisted count, (c) have fetched the persisted blob from
//   ITS OWN origin (macbook-pro-4), proving the downloadEncrypted rebase.
const WebSocket = require('ws');
const { execSync, spawn } = require('child_process');
const http = require('http');

const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const PORT = 9333;
const SESSION = 'ns-rebase-probe-' + Date.now();
const QS = `snapshot=CroquetCounterApp.vfuel&sessionId=${SESSION}&apiKey=none&pwd=test&appId=org.newspeaklanguage.ide&files=/files`;
const URL_A = `http://localhost:8080/croquetpsoup.html?${QS}&reflector=ws://localhost:9090`;
const URL_B = `http://macbook-pro-4:8080/croquetpsoup.html?${QS}&reflector=ws://macbook-pro-4:9090`;

const sleep = ms => new Promise(r => setTimeout(r, ms));

function httpJson(method, path) {
    return new Promise((resolve, reject) => {
        const req = http.request({ host: '127.0.0.1', port: PORT, path, method }, res => {
            let body = '';
            res.on('data', c => body += c);
            res.on('end', () => { try { resolve(JSON.parse(body)); } catch (e) { resolve(body); } });
        });
        req.on('error', reject);
        req.end();
    });
}

class Tab {
    constructor(ws) { this.ws = ws; this.id = 0; this.pending = new Map(); this.events = []; }
    static async open(url) {
        const info = await httpJson('PUT', '/json/new?' + encodeURIComponent(url));
        const ws = new WebSocket(info.webSocketDebuggerUrl, { maxPayload: 256 * 1024 * 1024 });
        await new Promise((res, rej) => { ws.on('open', res); ws.on('error', rej); });
        const tab = new Tab(ws);
        tab.targetId = info.id;
        ws.on('message', data => {
            const msg = JSON.parse(data);
            if (msg.id && tab.pending.has(msg.id)) { tab.pending.get(msg.id)(msg); tab.pending.delete(msg.id); }
            else if (msg.method) tab.events.push(msg);
        });
        return tab;
    }
    send(method, params = {}) {
        const id = ++this.id;
        return new Promise(resolve => {
            this.pending.set(id, resolve);
            this.ws.send(JSON.stringify({ id, method, params }));
        });
    }
    async eval(expr) {
        const r = await this.send('Runtime.evaluate', { expression: expr, returnByValue: true, awaitPromise: true });
        if (r.result && r.result.exceptionDetails) throw new Error('eval failed: ' + JSON.stringify(r.result.exceptionDetails.exception));
        return r.result && r.result.result ? r.result.result.value : undefined;
    }
    async close() {
        try { await httpJson('GET', '/json/close/' + this.targetId); } catch (e) { /* ignore */ }
        this.ws.close();
    }
}

// The count label is the text right before the increment button in the row.
const READ_COUNT = `(() => {
    const t = document.body ? document.body.innerText : '';
    const m = t.match(/(-?\\d+)\\s*increment/);
    return m ? parseInt(m[1], 10) : null;
})()`;

async function clickButton(tab, label) {
    // These are real <button> elements with onclick handlers; JS click() works.
    const r = await tab.eval(`(() => {
        const el = [...document.querySelectorAll('button')].find(e => e.textContent.trim() === '${label}');
        if (!el) return null;
        el.click();
        return true;
    })()`);
    if (!r) throw new Error(`button '${label}' not found`);
}

async function waitFor(tab, desc, expr, timeoutMs) {
    const start = Date.now();
    while (Date.now() - start < timeoutMs) {
        const v = await tab.eval(expr);
        if (v !== null && v !== false && v !== undefined) return v;
        await sleep(1000);
    }
    throw new Error(`timeout waiting for ${desc}`);
}

(async () => {
    const chrome = spawn(CHROME, [
        '--headless=new', `--remote-debugging-port=${PORT}`,
        '--user-data-dir=/tmp/ns-rebase-probe-profile',
        '--disable-background-timer-throttling', '--mute-audio', '--no-first-run',
        'about:blank'
    ], { stdio: 'ignore' });
    process.on('exit', () => { try { chrome.kill(); } catch (e) {} });
    for (let i = 0; ; i++) {
        try { await httpJson('GET', '/json/version'); break; }
        catch (e) { if (i > 20) throw e; await sleep(500); }
    }

    console.log('SESSION', SESSION);

    // ---- Phase A ----
    console.log('phase A: creating session on localhost origin');
    const a = await Tab.open(URL_A);
    let count = await waitFor(a, 'counter UI (A)', READ_COUNT, 90000);
    console.log('A synced, count =', count);
    for (let i = 0; i < 3; i++) { await clickButton(a, 'increment'); await sleep(700); }
    count = await waitFor(a, 'count == 3', `(${READ_COUNT}) === 3 ? 3 : null`, 20000);
    console.log('A clicked to count =', count);

    console.log('waiting 30s for persistence (10s debounce + upload)...');
    await sleep(30000);
    const persisted = execSync(
        `grep '"persist-local"' /private/tmp/reflector.log | grep '${SESSION}' | tail -1 || true`
    ).toString().trim();
    if (!persisted) { console.log('FAIL: no persist-local record for', SESSION); process.exit(1); }
    console.log('persist-local recorded:', (persisted.match(/"data":"([^"]+)"/) || [])[1]);

    await a.close();
    console.log('A left; waiting 15s for island deletion...');
    await sleep(15000);

    // ---- Phase B ----
    console.log('phase B: cold join on macbook-pro-4 origin');
    const b = await Tab.open('about:blank');
    await b.send('Network.enable');
    await b.send('Page.navigate', { url: URL_B });
    const bCount = await waitFor(b, 'counter UI (B)', READ_COUNT, 90000);

    const fileFetches = b.events
        .filter(e => e.method === 'Network.requestWillBeSent')
        .map(e => e.params.request.url)
        .filter(u => u.includes('/files/apps/'));
    const saveFetches = fileFetches.filter(u => u.includes('/save/'));

    console.log('B synced, count =', bCount);
    console.log('B file-server fetches:', JSON.stringify(fileFetches, null, 2));

    const ok = bCount === 3
        && saveFetches.length > 0
        && saveFetches.every(u => u.startsWith('http://macbook-pro-4:8080/'));
    console.log(ok ? 'PASS: cold joiner restored count 3 via its own origin'
                   : `FAIL: count=${bCount}, saveFetches=${JSON.stringify(saveFetches)}`);

    await b.close();
    chrome.kill();
    process.exit(ok ? 0 : 1);
})().catch(e => { console.log('ERROR:', e && (e.stack || e.message || String(e))); process.exit(1); });
