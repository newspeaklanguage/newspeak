const WebSocket = require('ws');
const { spawn } = require('child_process');
const http = require('http');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const PORT = 9333;
const SESSION = 'ns-dom-probe-' + Date.now();
const URL_A = `http://localhost:8080/croquetpsoup.html?snapshot=CroquetCounterApp.vfuel&sessionId=${SESSION}&apiKey=none&pwd=test&appId=org.newspeaklanguage.ide&files=/files&reflector=ws://localhost:9090`;
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
        '--user-data-dir=/tmp/ns-rebase-probe-profile', '--disable-background-timer-throttling',
        '--no-first-run', 'about:blank'], { stdio: 'ignore' });
    process.on('exit', () => { try { chrome.kill(); } catch (e) {} });
    for (let i = 0; ; i++) { try { await httpJson('GET', '/json/version'); break; } catch (e) { if (i > 20) throw e; await sleep(500); } }
    const info = await httpJson('PUT', '/json/new?' + encodeURIComponent(URL_A));
    const ws = new WebSocket(info.webSocketDebuggerUrl, { maxPayload: 256 * 1024 * 1024 });
    await new Promise((res, rej) => { ws.on('open', res); ws.on('error', rej); });
    let id = 0; const pending = new Map();
    ws.on('message', d => { const m = JSON.parse(d); if (m.id && pending.has(m.id)) { pending.get(m.id)(m); pending.delete(m.id); } });
    const send = (method, params = {}) => new Promise(r => { pending.set(++id, r); ws.send(JSON.stringify({ id, method, params })); });
    const evl = async e => { const r = await send('Runtime.evaluate', { expression: e, returnByValue: true }); return r.result.result ? r.result.result.value : r.result; };
    await sleep(25000);
    console.log(await evl(`(() => {
        const els = [...document.querySelectorAll('*')].filter(e => e.textContent.trim() === 'increment');
        return els.map(e => {
            const r = e.getBoundingClientRect();
            return e.tagName + ' cls=' + e.className + ' onclick=' + (e.onclick !== null) + ' rect=' + JSON.stringify(r);
        }).join('\\n');
    })()`));
    console.log('bodytext:', JSON.stringify(await evl('document.body.innerText.slice(0,200)')));
    // try plain JS click on the innermost match
    console.log('click result:', await evl(`(() => {
        const els = [...document.querySelectorAll('*')].filter(e => e.textContent.trim() === 'increment');
        const el = els[els.length - 1];
        if (!el) return 'no el';
        el.click();
        return 'clicked ' + el.tagName;
    })()`));
    await sleep(3000);
    console.log('bodytext after click:', JSON.stringify(await evl('document.body.innerText.slice(0,200)')));
    await httpJson('GET', '/json/close/' + info.id);
    chrome.kill(); process.exit(0);
})().catch(e => { console.log('ERROR:', e && (e.stack || String(e))); process.exit(1); });
