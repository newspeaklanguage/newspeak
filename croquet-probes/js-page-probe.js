// Load CroquetHopscotchWebIDE.html (NS2JS deploy) via the macbook-pro-4 origin
// and capture every console message + pageerror, to reproduce Gilad's
// "Invalid URL at connectToReflector".
const WebSocket = require('ws');
const { spawn } = require('child_process');
const http = require('http');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const PORT = 9333;
const SESSION = 'ns-jspage-probe-' + Date.now();
const URL_B = `http://macbook-pro-4:8080/CroquetHopscotchWebIDE.html?sessionId=${SESSION}&apiKey=none&pwd=test&appId=org.newspeaklanguage.ide&reflector=ws://macbook-pro-4:9090&files=/files`;
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
        '--user-data-dir=/tmp/ns-jspage-probe-profile', '--disable-background-timer-throttling',
        '--no-first-run', 'about:blank'], { stdio: 'ignore' });
    process.on('exit', () => { try { chrome.kill(); } catch (e) {} });
    for (let i = 0; ; i++) { try { await httpJson('GET', '/json/version'); break; } catch (e) { if (i > 20) throw e; await sleep(500); } }
    const info = await httpJson('PUT', '/json/new?about:blank');
    const ws = new WebSocket(info.webSocketDebuggerUrl, { maxPayload: 256 * 1024 * 1024 });
    await new Promise((res, rej) => { ws.on('open', res); ws.on('error', rej); });
    let id = 0; const pending = new Map(); const logs = [];
    ws.on('message', d => {
        const m = JSON.parse(d);
        if (m.id && pending.has(m.id)) { pending.get(m.id)(m); pending.delete(m.id); }
        else if (m.method === 'Runtime.consoleAPICalled') {
            logs.push(m.params.type + ': ' + m.params.args.map(a => a.value !== undefined ? a.value : (a.description || a.type)).join(' '));
        } else if (m.method === 'Runtime.exceptionThrown') {
            logs.push('EXCEPTION: ' + JSON.stringify(m.params.exceptionDetails.exception && m.params.exceptionDetails.exception.description));
        }
    });
    const send = (method, params = {}) => new Promise(r => { pending.set(++id, r); ws.send(JSON.stringify({ id, method, params })); });
    const evl = async e => { const r = await send('Runtime.evaluate', { expression: e, returnByValue: true }); return r.result.result ? r.result.result.value : r.result; };
    await send('Runtime.enable');
    await send('Page.navigate', { url: URL_B });
    await sleep(30000);
    console.log('--- console ---');
    logs.forEach(l => console.log(l.slice(0, 400)));
    console.log('--- state ---');
    console.log('theView defined:', await evl('typeof theView'));
    console.log('body text head:', JSON.stringify(await evl('document.body ? document.body.innerText.slice(0,120) : null')));
    await httpJson('GET', '/json/close/' + info.id);
    chrome.kill(); process.exit(0);
})().catch(e => { console.log('ERROR:', e && (e.stack || String(e))); process.exit(1); });
