/* What does a keystroke cost the TYPIST, with nobody else involved? The control
   for typing-latency-probe.js, whose calibrated runs (2026-09-19) showed the
   typist's main thread saturated at ~290ms per key on 1KB of text, in
   CodeMirror layout and native work. This probe types the same characters, the
   same way (real key events via CDP), into ONE client, and reports the cost per
   key, the event-loop lag and a CPU profile - for:

     croquet-probes/run.sh typing-cost-control.js             the PLAIN IDE (no Croquet at all)
     croquet-probes/run.sh CROQUET=1 typing-cost-control.js   the Croquet IDE, alone in its session
     croquet-probes/run.sh CROQUET=1 typing-cost-control.js js   ... as deployed to JS

   If the plain IDE costs about as much per key, Croquet is not the cause: the
   editor's own per-keystroke work (or the headless rig) is. If it is far
   cheaper, the echo handling is the cost.

   SIZE_KB (1)  N (40)  CADENCE_MS (100)  GPU=1 (no --disable-gpu)  BARE=1: also type into a
   bare CodeMirror created on the same page, outside Hopscotch - the floor for this rig. */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'keycost' + Math.floor(Date.now() / 1000);
const CROQUET = process.env.CROQUET === '1', JS = process.argv[2] === 'js';
const PAGE = !CROQUET ? 'primordialsoup.html?snapshot=HopscotchWebIDE-TEST.vfuel'
  : (JS ? 'CroquetJSIDE-TEST.html?sessionId=' : 'croquetpsoup-test.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=')
    + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const URL = 'http://localhost:8080/' + PAGE;
const SIZE_KB = Number(process.env.SIZE_KB || 1), N = Number(process.env.N || 40), CADENCE = Number(process.env.CADENCE_MS || 100);
const TYPED = 'the quick brown fox jumps over the lazy dog 0123456789 '.repeat(8).slice(0, N);
const sleep = ms => new Promise(r => setTimeout(r, ms));
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});if(!m.length)return 'absent';var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
const LAG_INSTALL = "(function(){if(window.__lag)return 'already';window.__lag=[];var last=Date.now();setInterval(function(){var now=Date.now();window.__lag.push([now,Math.max(0,now-last-50)]);if(window.__lag.length>4000)window.__lag.splice(0,2000);last=now},50);return 'installed'})()";
const lagSince = t => `(function(){var a=window.__lag.filter(function(x){return x[0]>=${t}}).map(function(x){return x[1]}).sort(function(p,q){return p-q});return a.length?JSON.stringify({n:a.length,median:a[Math.floor(a.length/2)],p90:a[Math.floor(a.length*0.9)],max:a[a.length-1]}):'null'})()`;
const pct = (a, p) => a.length ? a[Math.min(a.length - 1, Math.floor(p * a.length))] : null;
function summarize(profile, label) {
  const dt = profile.timeDeltas || [], byId = new Map();
  profile.nodes.forEach(n => byId.set(n.id, n));
  const self = new Map(); let total = 0;
  (profile.samples || []).forEach((id, i) => { const us = dt[i] || 0; total += us; self.set(id, (self.get(id) || 0) + us); });
  const bucket = n => { const f = n.callFrame, u = f.url || '';
    if (f.functionName === '(idle)') return 'idle';
    if (f.functionName === '(garbage collector)') return 'gc';
    if (u.startsWith('wasm:') || /wasm-function/.test(f.functionName)) return 'newspeak-vm(wasm)';
    if (/croquet\.min\.js/.test(u)) return 'croquet.min.js';
    if (/codemirror/i.test(u)) return 'codemirror';
    if (/croquetpsoup|primordialsoup|CroquetJSIDE/.test(u)) return 'glue/runtime js';
    if (f.functionName === '(program)') return '(program)';
    return u ? u.split('/').pop().slice(0, 30) : '(native/other)'; };
  const buckets = new Map(), fns = new Map();
  self.forEach((us, id) => { const n = byId.get(id); if (!n) return;
    buckets.set(bucket(n), (buckets.get(bucket(n)) || 0) + us);
    const f = n.callFrame, name = (f.functionName || '(anon)') + ' @' + (f.url || '').split('/').pop().slice(0, 28) + ':' + f.lineNumber;
    fns.set(name, (fns.get(name) || 0) + us); });
  const fmt = m => Array.from(m.entries()).sort((x, y) => y[1] - x[1]);
  console.log('  CPU ' + label + ', ' + Math.round(total / 1000) + 'ms: ' + fmt(buckets).map(([k, v]) => k + ' ' + Math.round(100 * v / total) + '%').join(', '));
  console.log('  hottest: ' + fmt(fns).slice(0, 7).map(([k, v]) => k + ' ' + Math.round(v / 1000) + 'ms').join(' | '));
}
async function main() {
  console.log((CROQUET ? 'CROQUET, one client' : 'PLAIN IDE') + '  SIZE_KB=' + SIZE_KB + ' N=' + N + ' CADENCE_MS=' + CADENCE + (process.env.GPU === '1' ? ' GPU' : ' software-rendering') + '  ' + PAGE.slice(0, 70));
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9495','--remote-allow-origins=*','--user-data-dir=/tmp/cq-keycost-'+SESSION,'--no-first-run','--window-size=1400,1000'].concat(process.env.GPU === '1' ? [] : ['--disable-gpu']).concat(['--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank']), {stdio:'ignore'});
  const done = code => { try { proc.kill(); } catch (e) {} process.exit(code); };
  setTimeout(() => { console.log('BAIL: deadline'); done(1); }, Number(process.env.DEADLINE_MS || 400000)).unref();
  let page; for (let i=0;i<300;i++){ try { const t=await getJson(9495,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await sleep(300); }
  if (!page) { console.log('BAIL: no page target'); done(1); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false, maxPayload: 64*1024*1024});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'&&m.params.type==='error')log.push(m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ').slice(0,200));
    if(m.method==='Runtime.exceptionThrown')log.push('THROWN '+((m.params.exceptionDetails.exception||{}).description||'').slice(0,200));}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); if (r&&r.exceptionDetails) return 'EVAL-THREW: '+((r.exceptionDetails.exception||{}).description||r.exceptionDetails.text); return r&&r.result&&r.result.value; };
  const waitFor = async (pred, ms) => { const t0=Date.now(); while (Date.now()-t0<ms){ if (await ev(pred)===true) return true; await sleep(500);} return false; };
  const waitIdle = async why => { const t0 = Date.now(); await ev(LAG_INSTALL);
    while (Date.now() - t0 < 120000) { await sleep(3000); const r = JSON.parse(await ev(lagSince(Date.now() - 3000)) || 'null'); if (r && r.max < 40) { console.log('idle ' + why + ' after ' + Math.round((Date.now()-t0)/1000) + 's'); return; } }
    console.log('NEVER idle ' + why + ': ' + await ev(lagSince(Date.now() - 3000))); };
  await send('Page.navigate',{url:URL});
  if (!await waitFor("!!(document.body && (document.body.innerText.includes('Workspaces') || document.body.innerText.includes('backup changes')))", 150000)) { console.log('BAIL: no home page'); done(1); }
  if (await ev("document.body.innerText.includes('backup changes')")) {
    await ev(`(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim().indexOf('Use current version')===0);if(m.length){var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})))}return m.length})()`);
    await waitFor("document.body.innerText.includes('Workspaces')", 60000);
  }
  await sleep(4000);
  await ev(click('Workspaces'));
  if (!await waitFor("document.body.innerText.includes('Evaluate')", 40000)) { console.log('BAIL: no workspace'); done(1); }
  await waitIdle('before the buffer');
  const size = await ev(`(function(){var cm=${CM};cm.focus();var line='(* '+'x'.repeat(76)+' *)\\n';var pad=line.repeat(Math.ceil(${SIZE_KB}*1024/line.length))+'##';cm.execCommand('selectAll');cm.replaceSelection(pad,null,'+input');cm.focus();return cm.getValue().length})()`);
  console.log('buffer: ' + size + ' chars');
  await sleep(2000); await waitIdle('before typing');

  async function typeRun(label, focusExpr) {
    const timed = (what, pr, ms) => Promise.race([pr, new Promise(r => setTimeout(() => r('__STALLED__'), ms))]).then(v => { if (v === '__STALLED__') { console.log('STALLED: ' + what + ' did not return within ' + ms + 'ms'); } return v; });
    console.log('  focus: ' + await timed('focus', ev(focusExpr), 15000));
    await timed('Profiler.enable', send('Profiler.enable'), 15000); await send('Profiler.setSamplingInterval', { interval: 1000 }); await send('Profiler.start');
    const t0 = Date.now(), cost = [];
    for (let i = 0; i < N; i++) {
      const c = TYPED[i], s0 = Date.now(), code = c === ' ' ? 'Space' : undefined;
      const kd = await timed('keyDown #' + i + ' ' + JSON.stringify(c), send('Input.dispatchKeyEvent', { type: 'keyDown', text: c, unmodifiedText: c, key: c, code }), 20000);
      if (kd === '__STALLED__') { console.log('  page text tail: ' + JSON.stringify(String(await timed('read', ev("document.body.innerText.slice(-200)"), 5000)))); break; }
      await timed('keyUp #' + i, send('Input.dispatchKeyEvent', { type: 'keyUp', key: c, code }), 20000);
      if (i % 10 === 9) console.log('  ' + (i + 1) + ' keys, ' + (Date.now() - t0) + 'ms');
      cost.push(Date.now() - s0);
      const rest = CADENCE - (Date.now() - s0); if (rest > 0) await sleep(rest);
    }
    const took = Date.now() - t0;
    await sleep(1500);
    const prof = await send('Profiler.stop');
    const k = cost.slice().sort((x, y) => x - y);
    console.log('--- ' + label + ': ' + N + ' keys in ' + took + 'ms (ideal ' + N * CADENCE + '); per key ms: median=' + pct(k, 0.5) + ' p90=' + pct(k, 0.9) + ' max=' + k[k.length - 1] + '; event-loop lag ' + await ev(lagSince(t0)));
    summarize(prof.profile, label);
  }
  await typeRun(CROQUET ? 'Croquet IDE workspace editor' : 'plain IDE workspace editor', `(function(){var cm=${CM};cm.focus();cm.setCursor(cm.lineCount(),0);return 1})()`);
  console.log('  editor now ends with: ' + JSON.stringify(String(await ev(`${CM}.getValue().slice(-46)`))));
  if (process.env.BARE === '1') {
    /* The floor: a CodeMirror with the same text, on the same page, that Hopscotch knows nothing about. */
    await ev(`(function(){var d=document.createElement('div');d.style.cssText='position:fixed;left:0;top:0;width:900px;height:500px;z-index:99999;background:white';document.body.appendChild(d);var line='(* '+'x'.repeat(76)+' *)\\n';window.__bare=CodeMirror(d,{value:line.repeat(Math.ceil(${SIZE_KB}*1024/line.length)),lineNumbers:false});return 1})()`);
    await sleep(1500);
    await typeRun('BARE CodeMirror, same page, outside Hopscotch', "(function(){window.__bare.focus();window.__bare.setCursor(window.__bare.lineCount(),0);return 1})()");
  }
  console.log('page errors: ' + log.length + (log.length ? '  first: ' + log[0] : ''));
  done(0);
}
main().catch(e => { console.error(e); process.exit(1); });
