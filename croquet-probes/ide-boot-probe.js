// Does the IDE actually START?
//
//   croquet-probes/run.sh ide-boot-probe.js
//   croquet-probes/run.sh NS_SNAPSHOT=HopscotchWebIDE-BOOTTEST.vfuel ide-boot-probe.js
//
// Compiling a vfuel proves nothing about whether it boots: Newspeak resolves
// sends at run time, so a method left in the wrong class compiles perfectly and
// dies as a doesNotUnderstand during startup -- which is exactly what shipped
// on 2026-09-20, from an edit that placed HopscotchWebIDE>>buildVersionOn: in a
// neighbouring class. This loads the snapshot in headless Chrome and asks two
// questions: did anything blow up, and did the IDE draw its home page.
//
// Needs the local server on :8080 serving out/ (the one already running -- this
// probe does not start one).
const WebSocket = require('ws');
const { spawn } = require('child_process');
const http = require('http');

const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const PORT = 9341;
const SNAPSHOT = process.env.NS_SNAPSHOT || 'HopscotchWebIDE.vfuel';
const URL = `http://localhost:8080/primordialsoup.html?snapshot=${SNAPSHOT}`;
const BOOT_MS = Number(process.env.BOOT_MS || 25000);

const sleep = ms => new Promise(r => setTimeout(r, ms));
function httpJson(method, path) {
    return new Promise((resolve, reject) => {
        const req = http.request({ host: '127.0.0.1', port: PORT, path, method }, res => {
            let body = ''; res.on('data', c => body += c);
            res.on('end', () => { try { resolve(JSON.parse(body)); } catch (e) { resolve(body); } });
        });
        req.on('error', reject); req.end();
    });
}

(async () => {
    const chrome = spawn(CHROME, ['--headless=new', `--remote-debugging-port=${PORT}`,
        '--user-data-dir=/tmp/ns-ide-boot-probe-profile', '--disable-background-timer-throttling',
        '--no-first-run', 'about:blank'], { stdio: 'ignore' });
    process.on('exit', () => { try { chrome.kill(); } catch (e) {} });
    for (let i = 0; ; i++) {
        try { await httpJson('GET', '/json/version'); break; }
        catch (e) { if (i > 20) throw e; await sleep(500); }
    }
    const info = await httpJson('PUT', '/json/new?' + encodeURIComponent(URL));
    const ws = new WebSocket(info.webSocketDebuggerUrl, { maxPayload: 256 * 1024 * 1024 });
    await new Promise((res, rej) => { ws.on('open', res); ws.on('error', rej); });

    let id = 0; const pending = new Map();
    const noise = [];
    ws.on('message', d => {
        const m = JSON.parse(d);
        if (m.id && pending.has(m.id)) { pending.get(m.id)(m); pending.delete(m.id); return; }
        // Everything the page says about itself, so a startup failure is caught
        // however it surfaces: a console message, a thrown exception, or a crash.
        if (m.method === 'Runtime.consoleAPICalled') {
            const t = (m.params.args || []).map(a => a.value !== undefined ? a.value : a.description).join(' ');
            noise.push([m.params.type, t]);
        } else if (m.method === 'Runtime.exceptionThrown') {
            const d2 = m.params.exceptionDetails || {};
            noise.push(['exception', d2.text + ' ' + ((d2.exception || {}).description || '')]);
        } else if (m.method === 'Inspector.targetCrashed') {
            noise.push(['crash', 'the renderer died']);
        }
    });
    const send = (method, params = {}) => new Promise(r => {
        pending.set(++id, r); ws.send(JSON.stringify({ id, method, params }));
    });
    const evl = async e => {
        const r = await send('Runtime.evaluate', { expression: e, returnByValue: true });
        return r.result && r.result.result ? r.result.result.value : undefined;
    };

    await send('Runtime.enable');
    await send('Inspector.enable');
    await send('Page.enable');

    console.log(`booting ${SNAPSHOT} …`);
    const deadline = Date.now() + BOOT_MS;
    let rendered = 0;
    while (Date.now() < deadline) {
        await sleep(500);
        // The IDE has started once it has painted something into the document.
        rendered = await evl('document.body ? document.body.innerText.length : 0') || 0;
        if (rendered > 40) break;
    }

    const bad = noise.filter(([kind, text]) =>
        kind === 'error' || kind === 'exception' || kind === 'crash' ||
        /doesNotUnderstand|DNU|does not understand/i.test(text));
    const version = await evl(
        "(document.body && document.body.innerText.match(/built [^\\n]*/) || [''])[0]") || '';

    console.log(`rendered ${rendered} chars of text`);
    if (version) console.log(`home page reports: ${version}`);
    if (bad.length) {
        console.log('\nFAIL: the page reported trouble while starting:');
        bad.slice(0, 10).forEach(([k, t]) => console.log(`  [${k}] ${String(t).slice(0, 300)}`));
        process.exit(1);
    }
    if (rendered <= 40) {
        console.log('\nFAIL: nothing was rendered within ' + BOOT_MS + 'ms; the IDE did not start.');
        noise.slice(-10).forEach(([k, t]) => console.log(`  [${k}] ${String(t).slice(0, 300)}`));
        process.exit(1);
    }
    console.log('\nPASS: the IDE started and drew its home page.');
    process.exit(0);
})().catch(e => { console.log('BAIL: ' + e.message); process.exit(2); });
