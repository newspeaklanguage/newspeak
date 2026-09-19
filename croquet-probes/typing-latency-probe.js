/* How long does a typed character take to reach the other client, and what does
   typing cost in events - as a function of the SIZE of the text being edited?
   The requirement (Gilad, 2026-09-18): interactive at any size.

   Client A puts SIZE_KB of text into a workspace editor, then types N characters
   at the END of it with REAL key events (CDP Input.dispatchKeyEvent), so that
   CodeMirror's own '+input' path runs - selection moves included - which a
   scripted replaceSelection does not exercise. Client B is polled every 25ms;
   a character's latency is the time from its keyDown to the first poll in which
   B's editor holds it.

     croquet-probes/run.sh SIZE_KB=9   typing-latency-probe.js [js]
     croquet-probes/run.sh SIZE_KB=300 typing-latency-probe.js [js]

   SIZE_KB (9)  N (40 characters)  CADENCE_MS (100 = 10 chars/s)
   NS_PAGE (croquetpsoup-test.html: the TEST glue)  NS_SUFFIX (-TEST)
   BOUND_MS (1500): every character must arrive within this, at ANY size - FAIL otherwise.
   GPU=1: do not pass --disable-gpu (headless software rendering inflates layout cost).
   IDLE_WAIT_MS (120000): how long to wait for both clients' event loops to go quiet
   before measuring. 2026-09-19: the first baselines were taken with both browsers
   CPU-saturated (start-up git work, software layout), which is a fact about the rig.
   PROFILE=1: CPU-profile both clients while A types, and timestamp each change's journey:
   CodeMirror change on A -> nsPublish called -> handed to Croquet -> applied on B.

   Reports: latency first/median/p90/max; how long A's keyDown took to be
   processed (the typist's own responsiveness); the events the typing recorded,
   by kind, and how many of them took the Data-API detour (full text over 8KB). */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'latency' + Math.floor(Date.now() / 1000);
const JS = process.argv[2] === 'js';
const SUFFIX = process.env.NS_SUFFIX === undefined ? '-TEST' : process.env.NS_SUFFIX;
const NS_PAGE = process.env.NS_PAGE || 'croquetpsoup-test.html';
const PAGE = JS ? 'CroquetJSIDE-TEST.html?sessionId='
                : NS_PAGE + '?snapshot=CroquetHopscotchWebIDE' + SUFFIX + '.vfuel&sessionId=';
const URL = 'http://localhost:8080/' + PAGE + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
const SIZE_KB = Number(process.env.SIZE_KB || 9);
const N = Number(process.env.N || 40);
const CADENCE = Number(process.env.CADENCE_MS || 100);
const BOUND = Number(process.env.BOUND_MS || 1500);
const MARK = '§§';
const TYPED = 'the quick brown fox jumps over the lazy dog 0123456789 '.repeat(8).slice(0, N);
const sleep = ms => new Promise(r => setTimeout(r, ms));
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
const CM = "document.querySelectorAll('.CodeMirror')[document.querySelectorAll('.CodeMirror').length-1].CodeMirror";
const click = label => `(function(){var m=Array.from(document.querySelectorAll('a,button,span,div,label')).filter(e=>(e.innerText||'').trim()===${JSON.stringify(label)});var e=m[m.length-1];['mousedown','mouseup','click'].forEach(t=>e.dispatchEvent(new MouseEvent(t,{bubbles:true,cancelable:true,view:window})));return 'C'})()`;
const live = [];
function bail(why) {
  console.log('BAIL: ' + why);
  for (const b of live) { console.log('  ' + b.tag + ' console tail: ' + b.log.slice(-6).join(' || ')); try { b.proc.kill(); } catch (e) {} }
  process.exit(1);
}
setTimeout(() => bail('overall deadline passed'), Number(process.env.DEADLINE_MS || 420000)).unref();
async function browser(port, tag) {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port='+port,'--remote-allow-origins=*','--user-data-dir=/tmp/cq-lat-'+tag+'-'+SESSION,'--no-first-run','--window-size=1400,1000'].concat(process.env.GPU === '1' ? [] : ['--disable-gpu']).concat(['--disable-background-timer-throttling','--disable-renderer-backgrounding','about:blank']), {stdio:'ignore'});
  let page; for (let i=0;i<300;i++){ try { const t=await getJson(port,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await sleep(300); }
  if (!page) { try { proc.kill(); } catch (e) {} throw new Error('no page target on port ' + port + ' (run probe-browsers.js --kill)'); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false, maxPayload: 64*1024*1024});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){log.push('['+m.params.type+'] '+m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ').slice(0,200));}
    if(m.method==='Runtime.exceptionThrown'){const d=m.params.exceptionDetails;log.push('[THROWN] '+(d.exception&&d.exception.description||d.text||'').slice(0,300));}}catch(e){}});
  await send('Runtime.enable'); await send('Page.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); if (r&&r.exceptionDetails) return 'EVAL-THREW: '+(r.exceptionDetails.exception&&r.exceptionDetails.exception.description||r.exceptionDetails.text); return r&&r.result&&r.result.value; };
  const b = { proc, ev, send, log, tag, navigate: u => send('Page.navigate',{url:u}) };
  live.push(b);
  return b;
}
async function waitFor(b, pred, ms) { const t0=Date.now(); while (Date.now()-t0<ms){ if (await b.ev(pred)===true) return true; await sleep(500); } return false; }
async function boot(b) {
  const t0 = Date.now();
  await b.navigate(URL);
  if (!await waitFor(b, "!!(document.body && document.body.innerText.includes('Workspaces'))", 150000)) bail(b.tag + ' never showed the home page');
  console.log(b.tag + ' booted in ' + Math.round((Date.now()-t0)/1000) + 's');
  await sleep(4000);
}
/* Event-loop lag: a 50ms interval timer that records how late it fires. A page
   whose main thread is busy shows it here, whatever is keeping it busy. */
const LAG_INSTALL = "(function(){if(window.__lag)return 'already';window.__lag=[];var last=Date.now();setInterval(function(){var now=Date.now();window.__lag.push([now,Math.max(0,now-last-50)]);if(window.__lag.length>4000)window.__lag.splice(0,2000);last=now},50);return 'installed'})()";
const lagSince = t => `(function(){var a=window.__lag.filter(function(x){return x[0]>=${t}}).map(function(x){return x[1]}).sort(function(p,q){return p-q});return a.length?JSON.stringify({n:a.length,median:a[Math.floor(a.length/2)],p90:a[Math.floor(a.length*0.9)],max:a[a.length-1]}):'null'})()`;
async function waitIdle(b, why) {
  const t0 = Date.now(), limit = Number(process.env.IDLE_WAIT_MS || 120000);
  await b.ev(LAG_INSTALL);
  while (Date.now() - t0 < limit) {
    await sleep(3000);
    const r = JSON.parse(await b.ev(lagSince(Date.now() - 3000)) || 'null');
    if (r && r.max < 40) { console.log(b.tag + ' idle ' + why + ' after ' + Math.round((Date.now() - t0) / 1000) + 's (3s lag max ' + r.max + 'ms)'); return true; }
  }
  const r = await b.ev(lagSince(Date.now() - 3000));
  console.log(b.tag + ' NEVER went idle ' + why + ' within ' + limit + 'ms; last 3s lag ' + r);
  return false;
}
const PROFILE = process.env.PROFILE === '1';
/* Where a client's CPU went, from a CDP sampling profile: self time by bucket
   (the Newspeak VM is WebAssembly; the rest by script), and the hottest functions. */
function summarize(profile, label) {
  const dt = profile.timeDeltas || [], byId = new Map();
  profile.nodes.forEach(n => byId.set(n.id, n));
  const self = new Map(); let total = 0;
  (profile.samples || []).forEach((id, i) => { const us = dt[i] || 0; total += us; self.set(id, (self.get(id) || 0) + us); });
  const bucket = n => {
    const f = n.callFrame, u = f.url || '';
    if (f.functionName === '(idle)') return 'idle';
    if (f.functionName === '(garbage collector)') return 'gc';
    if (u.startsWith('wasm:') || /wasm-function/.test(f.functionName)) return 'newspeak-vm(wasm)';
    if (/croquet\.min\.js/.test(u)) return 'croquet.min.js';
    if (/codemirror/i.test(u)) return 'codemirror';
    if (/croquetpsoup|primordialsoup|CroquetJSIDE/.test(u)) return 'glue/runtime js';
    if (f.functionName === '(program)') return '(program)';
    return u ? u.split('/').pop().slice(0, 30) : '(native/other)';
  };
  const buckets = new Map(), fns = new Map();
  self.forEach((us, id) => { const n = byId.get(id); if (!n) return;
    const bk = bucket(n); buckets.set(bk, (buckets.get(bk) || 0) + us);
    const f = n.callFrame, name = (f.functionName || '(anon)') + ' @' + (f.url || '').split('/').pop().slice(0, 28) + ':' + f.lineNumber;
    fns.set(name, (fns.get(name) || 0) + us); });
  const fmt = m => Array.from(m.entries()).sort((x, y) => y[1] - x[1]);
  console.log('--- CPU profile ' + label + ': ' + Math.round(total / 1000) + 'ms sampled');
  console.log('  by bucket: ' + fmt(buckets).map(([k, v]) => k + ' ' + Math.round(100 * v / total) + '%').join(', '));
  console.log('  hottest:   ' + fmt(fns).slice(0, 8).map(([k, v]) => k + ' ' + Math.round(v / 1000) + 'ms').join(' | '));
}
const pct = (a, p) => a.length ? a[Math.min(a.length - 1, Math.floor(p * a.length))] : null;
async function main() {
  console.log('SIZE_KB=' + SIZE_KB + ' N=' + N + ' CADENCE_MS=' + CADENCE + ' BOUND_MS=' + BOUND + '  ' + PAGE);
  const A = await browser(9491, 'A'); await boot(A);
  await A.ev(click('Workspaces'));
  if (!await waitFor(A, "document.body.innerText.includes('Evaluate')", 40000)) bail('A never reached the workspace');
  const B = await browser(9492, 'B'); await boot(B);
  if (!await waitFor(B, "document.body.innerText.includes('Evaluate')", 60000)) bail('B never followed A to the workspace');
  await waitIdle(A, 'before the buffer'); await waitIdle(B, 'before the buffer');

  /* The buffer goes in as ONE user edit (like a paste), ending in the marker;
     the cursor is left at the end, after the marker, where the typing goes. */
  const set = await A.ev(`(function(){var cm=${CM};cm.focus();var line='(* '+'x'.repeat(76)+' *)\\n';var pad=line.repeat(Math.ceil(${SIZE_KB}*1024/line.length))+${JSON.stringify(MARK)};cm.execCommand('selectAll');cm.replaceSelection(pad,null,'+input');cm.focus();return cm.getValue().length})()`);
  console.log('A buffer: ' + set + ' chars');
  const tBuf = Date.now();
  if (!await waitFor(B, `${CM}.getValue().length >= ${set}`, 120000)) bail('B never received the buffer');
  console.log('B received the buffer after ' + (Date.now() - tBuf) + 'ms');
  await waitIdle(A, 'before typing'); await waitIdle(B, 'before typing');
  /* STYLE=count: count the editor's markText and refresh calls while typing. STYLE=off: also
     make them do nothing - what typing costs when the text is not styled at all. */
  const STYLE_COUNT = process.env.STYLE === 'count' || process.env.STYLE === 'off';
  if (STYLE_COUNT) for (const b of [A, B]) console.log(b.tag + ' style hooks: ' + await b.ev(`(function(){var cm=${CM};window.__st={markText:0,refresh:0,marks:cm.getAllMarks().length};var mt=cm.markText,rf=cm.refresh,off=${process.env.STYLE === 'off'};cm.markText=function(){window.__st.markText++;return off?{clear:function(){},find:function(){return null}}:mt.apply(this,arguments)};cm.refresh=function(){window.__st.refresh++;return off?undefined:rf.apply(this,arguments)};return 'installed, marks in the document: '+window.__st.marks})()`));
  if (PROFILE) {
    /* A: when CodeMirror announced a user change, when Newspeak called nsPublish, when it was handed to Croquet. */
    console.log('A journey hooks: ' + await A.ev(`(function(){var cm=${CM};window.__j={change:[],nsPublish:[],viewPublish:[]};cm.on('change',function(c,o){if(o.origin&&o.origin!=='setValue'&&o.origin!=='croquet')window.__j.change.push(Date.now())});var np=window.nsPublish;window.nsPublish=function(s,e,d){if(e==='codeMirror_change')window.__j.nsPublish.push(Date.now());return np.apply(this,arguments)};var vp=theView.publish;theView.publish=function(s,e,d){if(e==='codeMirror_change')window.__j.viewPublish.push(Date.now());return vp.apply(this,arguments)};return 'installed'})()`));
    /* B: when each echo changed its editor. */
    console.log('B journey hooks: ' + await B.ev(`(function(){var cm=${CM};window.__j={applied:[]};cm.on('change',function(c,o){window.__j.applied.push(Date.now())});return 'installed'})()`));
    for (const b of [A, B]) { await b.send('Profiler.enable'); await b.send('Profiler.setSamplingInterval', { interval: 1000 }); await b.send('Profiler.start'); }
  }
  const eventsBefore = await A.ev('theModel.newspeakEvents.length');

  /* Poll B for how much of the typed text it holds, stamping first sightings. */
  const seenAt = new Array(N).fill(null);
  let polling = true;
  const TAIL = `(function(){var v=${CM}.getValue();var i=v.lastIndexOf(${JSON.stringify(MARK)});return i<0?-1:v.length-i-${MARK.length}})()`;
  const poller = (async () => {
    while (polling) {
      const k = await B.ev(TAIL), now = Date.now();
      if (typeof k === 'number') for (let i = 0; i < Math.min(k, N); i++) if (seenAt[i] === null) seenAt[i] = now;
      await sleep(25);
    }
  })();

  const sentAt = [], keyCost = [];
  for (let i = 0; i < N; i++) {
    const c = TYPED[i], t0 = Date.now();
    sentAt.push(t0);
    const code = c === ' ' ? 'Space' : undefined;
    await A.send('Input.dispatchKeyEvent', { type: 'keyDown', text: c, unmodifiedText: c, key: c, code });
    await A.send('Input.dispatchKeyEvent', { type: 'keyUp', key: c, code });
    keyCost.push(Date.now() - t0);
    const rest = CADENCE - (Date.now() - t0);
    if (rest > 0) await sleep(rest);
  }
  const typedFor = Date.now() - sentAt[0];
  console.log('event-loop lag while typing, ms: A ' + await A.ev(lagSince(sentAt[0])) + '  B ' + await B.ev(lagSince(sentAt[0])));
  const tEnd = Date.now();
  while (seenAt[N - 1] === null && Date.now() - tEnd < 90000) await sleep(100);
  polling = false; await poller;
  if (PROFILE) {
    const pa = await A.send('Profiler.stop'), pb = await B.send('Profiler.stop');
    summarize(pa.profile, 'A (the typist)'); summarize(pb.profile, 'B');
    const ja = JSON.parse(await A.ev('JSON.stringify(window.__j)')), jb = JSON.parse(await B.ev('JSON.stringify(window.__j)'));
    const t0 = sentAt[0], rel = a => a.map(t => t - t0).join(',');
    console.log('--- journey, ms since the first keyDown');
    console.log('  A CodeMirror user changes (' + ja.change.length + '): ' + rel(ja.change).slice(0, 300));
    console.log('  A nsPublish called        (' + ja.nsPublish.length + '): ' + rel(ja.nsPublish));
    console.log('  A handed to Croquet       (' + ja.viewPublish.length + '): ' + rel(ja.viewPublish));
    console.log('  B editor changed by echo  (' + jb.applied.length + '): ' + rel(jb.applied));
  }

  const aTail = await A.ev(`(function(){var v=${CM}.getValue();var i=v.lastIndexOf(${JSON.stringify(MARK)});return v.slice(i+${MARK.length})})()`);
  const bTail = await B.ev(`(function(){var v=${CM}.getValue();var i=v.lastIndexOf(${JSON.stringify(MARK)});return v.slice(i+${MARK.length})})()`);
  const lat = seenAt.map((t, i) => t === null ? null : t - sentAt[i]);
  const arrived = lat.filter(x => x !== null).sort((x, y) => x - y);
  console.log('typed ' + N + ' chars in ' + typedFor + 'ms; A holds ' + JSON.stringify(aTail.slice(0, 50)) + (aTail === TYPED ? ' (all, in order)' : ' (NOT what was typed)'));
  console.log('B holds ' + bTail.length + ' of ' + N + (bTail === TYPED ? ' (all, in order)' : ' : ' + JSON.stringify(bTail.slice(0, 50))));
  console.log('latency to B, ms: first=' + lat[0] + ' median=' + pct(arrived, 0.5) + ' p90=' + pct(arrived, 0.9) + ' max=' + (arrived.length ? arrived[arrived.length - 1] : null) + ' last char=' + lat[N - 1] + '  (never arrived: ' + (N - arrived.length) + ')');
  const kc = keyCost.slice().sort((x, y) => x - y);
  console.log('A keyDown+keyUp processed in, ms: median=' + pct(kc, 0.5) + ' p90=' + pct(kc, 0.9) + ' max=' + kc[kc.length - 1]);
  await sleep(2000);
  const tally = await A.ev(`(function(){var ev=theModel.newspeakEvents.slice(${eventsBefore});var m={},det=0;ev.forEach(function(e){m[e.eventSpec]=(m[e.eventSpec]||0)+1;if(e.data&&e.data.__nsDetouredPayload)det++});return JSON.stringify({total:ev.length,detoured:det,byKind:m})})()`);
  console.log('events recorded by the typing: ' + tally);
  const t = JSON.parse(tally);
  console.log('events per typed character: ' + (t.total / N).toFixed(2));
  const ok = (l, c, d) => console.log(l + ': ' + (c ? 'PASS' : 'FAIL') + (d ? '  ' + d : ''));
  ok('EVERY CHARACTER REACHES B', arrived.length === N && bTail === TYPED);
  ok('WITHIN ' + BOUND + 'ms AT THIS SIZE', arrived.length === N && arrived[arrived.length - 1] <= BOUND, 'max ' + (arrived.length ? arrived[arrived.length - 1] : 'n/a') + 'ms');
  ok('NO TYPING EVENT TAKES THE DETOUR', t.detoured === 0, t.detoured + ' detoured');
  ok('A KEPT WHAT WAS TYPED', aTail === TYPED);
  const divs = [await A.ev('JSON.stringify((window.nsDivergences||[]).length)'), await B.ev('JSON.stringify((window.nsDivergences||[]).length)')];
  if (STYLE_COUNT) for (const x of [A, B]) console.log(x.tag + ' styling while typing: ' + await x.ev(`(function(){var cm=${CM};return JSON.stringify(window.__st)+' marks now: '+cm.getAllMarks().length})()`));
  ok('NO DIVERGENCE REPORTED', divs[0] === '0' && divs[1] === '0', 'A=' + divs[0] + ' B=' + divs[1]);
  console.log('errors A/B: ' + A.log.filter(l => /^\[(error|THROWN)\]/.test(l)).length + ' / ' + B.log.filter(l => /^\[(error|THROWN)\]/.test(l)).length);
  for (const b of live) { try { b.proc.kill(); } catch (e) {} }
  process.exit(0);
}
main().catch(e => { console.error(e); bail('exception'); });
