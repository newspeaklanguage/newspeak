/* Late join after the AI chat setup form was driven through the UI and a bus
 * chat exchanged messages.
 *
 * Reproduces the 2026-09-12 stall: Gilad opened the chat setup from the
 * toolbar, switched the provider to Bus Agent, typed the agent name, pressed
 * Start Chat and exchanged messages with the agent. A late joiner then stalled
 * with 'no subscriber for key "nscodemirror_/2..."' at event ~562 - a
 * setValue-shaped pair on the setup form's chat-name editor, published by the
 * ORIGINAL client long after Start Chat had retired that form - and later
 * orphaned keystrokes for an editor ordinal (/24) the joiner had not minted.
 * The bus-election probe never covered this: it builds the completion with a
 * doIt, not through the form, and a first version of this probe stopped at
 * Start Chat and converged cleanly. So the exchange is part of the recipe.
 *
 * Browser A drives the form and the chat; the probe itself is the bus agent
 * answering on /_ns/bus. Browser B cold-joins. We print the CodeMirror census
 * (which ordinals are live) after every step on A, the recorded storyline,
 * and B's census, page and orphan skips.
 *
 *   ~/software/emsdk-main/node/22.16.0_64bit/bin/node croquet-probes/setup-latejoin-probe.js
 *
 * Needs the front door on :8080 started with --bus, and the reflector on
 * :9090. NS_SUFFIX=-TEST runs against the -TEST vfuel; default is the live
 * one. TURNS (default 2) is how many messages A sends before B joins.
 */
if (!process.env.NODE_PATH) {
  process.env.NODE_PATH = '/Users/gbracha/newspeak/dev/web/croquet/packages/reflector/node_modules';
  require('module').Module._initPaths();
}
const http = require('http');
const { sleep, launchBrowser, click, waitFor, makeChecker } = require('./harness');
const { check, summary } = makeChecker();

const ORIGIN = 'http://localhost:8080';
const SUFFIX = process.env.NS_SUFFIX || '';
const SESSION = 'sljprobe' + Math.floor(Date.now() / 1000);
const AGENT = process.env.AGENT || 'probeagent';
const TURNS = Number(process.env.TURNS || 2);
const REPLY = 'BUS-REPLY-424242';
const URL = ORIGIN + '/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE' + SUFFIX +
  '.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.sljprobe&apiKey=none' +
  '&reflector=ws://localhost:9090&files=/files';
const JOIN_MS = Number(process.env.JOIN_MS || 240000);
/* How long the agent sits on each request before answering. Long enough for
   the chat's waiting state - the thinking indicator and its per-second
   re-renders - to happen on A, so the joiner has to reproduce them. 0 answers
   at once. */
const REPLY_DELAY_MS = Number(process.env.REPLY_DELAY_MS || 30000);
let requests = 0;

function get(path) { return new Promise((res, rej) => { http.get(ORIGIN + path, r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) }).on('error', rej) }) }
function post(path, obj, token) {
  return new Promise((res, rej) => {
    const d = JSON.stringify(obj);
    const rq = http.request(ORIGIN + path, { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-NS-Token': token, 'Content-Length': Buffer.byteLength(d) } },
      r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) });
    rq.on('error', rej); rq.end(d);
  });
}
/* The agent: hold the SSE open under our name, answer completion_request. */
function startAgent(token) {
  return new Promise(resolve => {
    const req = http.get(ORIGIN + '/_ns/bus?token=' + encodeURIComponent(token) + '&name=' + encodeURIComponent(AGENT), res => {
      let buf = '';
      res.on('data', chunk => {
        buf += chunk; let i;
        while ((i = buf.indexOf('\n\n')) >= 0) {
          const frame = buf.slice(0, i); buf = buf.slice(i + 2);
          const line = frame.split('\n').find(l => l.startsWith('data:'));
          if (!line) continue;
          let msg; try { msg = JSON.parse(line.slice(5).trim()) } catch (e) { continue }
          if (msg.kind === 'completion_request' && msg.to === AGENT) {
            requests++;
            const n = requests;
            console.log('  agent: request ' + n + ' received; answering in ' + REPLY_DELAY_MS + 'ms');
            setTimeout(() => {
              post('/_ns/bus', { to: msg.from, from: AGENT, kind: 'completion_response', corr_id: msg.corr_id,
                response: { id: 'msg_' + n, type: 'message', role: 'assistant',
                  content: [{ type: 'text', text: REPLY + '-' + n }], stop_reason: 'end_turn',
                  usage: { input_tokens: 1, output_tokens: 1 } } }, token).catch(() => {});
            }, REPLY_DELAY_MS);
          }
        }
      });
      resolve(req);
    });
  });
}

const CENSUS = `(function(){var s=new Set();Array.from(newspeakSubscriptions.keys()).forEach(function(k){` +
  `if(k.indexOf('nscodemirror_')===0)s.add(k.split('model_')[0].slice('nscodemirror_'.length))});` +
  `return JSON.stringify({processed:lastProcessedEvent,total:theModel.newspeakEvents.length,onScreen:document.querySelectorAll('.CodeMirror').length,cm:Array.from(s)})})()`;
const STORY = n => `(function(){var ev=theModel.newspeakEvents.slice(0,${n});var seen=[];` +
  `ev.forEach(function(e,i){var t=e.scope+e.fid+':'+String(e.eventSpec).replace('model_','');` +
  `if(seen.indexOf(t)<0)seen.push(i+' '+t)});return seen.join(' | ')})()`;
const PAGE = `(document.body.innerText||'').replace(/\\s+/g,' ').slice(0,300)`;
/* An ImageButtonFragment is a div (which carries the tooltip title) around an
   img that carries the onclick, so the click must land on the img. */
const clickTitle = t => `(function(){var e=document.querySelector('[title=' + ${JSON.stringify(JSON.stringify(t))} + ']');` +
  `if(!e)return 'NOEL';var tgt=e.querySelector('img')||e;` +
  `['mousedown','mouseup','click'].forEach(function(x){tgt.dispatchEvent(new MouseEvent(x,{bubbles:true,cancelable:true,view:window}))});return 'CLICKED'})()`;
/* The provider picker is the drop-down image button in the same row as the
   bold label showing the current provider name. */
const openPicker = name => `(function(){var want=${JSON.stringify(name)}.toLowerCase();` +
  `var lab=Array.from(document.querySelectorAll('span,div,label,b'))` +
  `.filter(function(e){return (e.innerText||'').trim().toLowerCase()===want&&e.children.length===0});` +
  `if(!lab.length)return 'NOLABEL';var l=lab[lab.length-1];var row=l.parentElement;var img=null;` +
  `for(var k=0;k<6&&row&&!img;k++){img=row.querySelector('img');if(!img)row=row.parentElement}` +
  `if(!img)return 'NOIMG';['mousedown','mouseup','click'].forEach(function(x){img.dispatchEvent(new MouseEvent(x,{bubbles:true,cancelable:true,view:window}))});return 'CLICKED'})()`;
/* Focus the CodeMirror in the 'Model: ' row; the text is then typed with real
   keystrokes (typeInto). A setValue would be a PROGRAMMATIC change, which
   the Croquet layer now handles locally and does not publish - a joiner
   replaying the form would never see the agent name, and Start Chat would
   fail validation there. A user's typing is tagged '+input' and published. */
const FOCUS_MODEL_CM = `(function(){var lab=Array.from(document.querySelectorAll('span,div,label,b'))` +
  `.filter(function(e){return (e.innerText||'').trim()==='Model:'&&e.children.length===0});` +
  `if(!lab.length)return 'NOLABEL';var row=lab[lab.length-1].parentElement;var cm=null;` +
  `for(var k=0;k<6&&row&&!cm;k++){cm=row.querySelector('.CodeMirror');if(!cm)row=row.parentElement}` +
  `if(!cm)return 'NOCM';cm.CodeMirror.focus();return 'FOCUSED'})()`;
async function typeInto(b, focusExpr, text) {
  const f = await b.v(focusExpr);
  if (f !== 'FOCUSED') return f;
  /* Two chunks: see sendChat. */
  await b.send('Input.insertText', { text: text.slice(0, -1) });
  await sleep(300);
  await b.send('Input.insertText', { text: text.slice(-1) });
  await sleep(600);
  return 'TYPED';
}
/* The chat input is the last CodeMirror on the chat page. Focus it, then type
   and accept through the DevTools Input domain: real keystrokes take
   CodeMirror's own input path (origin +input, which puts the fragment in edit
   state) and the accept is Ctrl+Enter in respondToKeyDown:. A synthetic
   setValue plus a dispatched keydown worked once but not on the re-rendered
   editor of a second turn. */
const FOCUS_LAST_CM = `(function(){var c=document.querySelectorAll('.CodeMirror');if(!c.length)return 'NOCM';` +
  `var cm=c[c.length-1].CodeMirror;cm.focus();cm.setCursor(cm.lineCount(),0);return 'FOCUSED:'+c.length})()`;
async function sendChat(b, text) {
  const f = await b.v(FOCUS_LAST_CM);
  if (f === 'NOCM') return f;
  /* Two chunks, deliberately: after a re-render the Croquet CodeMirror
     override leaves lastChangeWasSynthetic raised when the adopted text was
     unchanged (its updateEditedText: skips the setValue that would consume
     it), so the FIRST real change is swallowed as synthetic and the editor
     never enters edit state - Ctrl+Enter is then ignored. A second keystroke
     clears it, as a human's always does. */
  await b.send('Input.insertText', { text: text.slice(0, -1) });
  await sleep(300);
  await b.send('Input.insertText', { text: text.slice(-1) });
  await sleep(600);
  const key = type => b.send('Input.dispatchKeyEvent', { type, key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13, modifiers: 2 });
  await key('keyDown'); await key('keyUp');
  return 'SENT (' + f + ')';
}

async function step(b, label, expr) {
  const r = await b.v(expr);
  console.log('  ' + label + ': ' + r);
  return r;
}
let agentReq = null;
async function bail(A, msg) {
  console.log(msg);
  console.log('A page:', await A.v(PAGE));
  return done([A]);
}

async function main() {
  const cfg = JSON.parse(await get('/_ns/config'));
  if (!cfg.bus) { console.log('front door has no bus (start it with --bus)'); process.exitCode = 1; return }
  const token = JSON.parse(await get('/_ns/token')).token;
  agentReq = await startAgent(token);
  console.log('agent "' + AGENT + '" listening on the bus');
  await sleep(1500);

  const A = await launchBrowser({ port: 9821, tag: 'slj-a', session: SESSION });
  await A.navigate(URL);
  if (!await waitFor(A, "document.body && document.body.innerText.includes('Workspaces')", 240000)) {
    check('A boots', false, A.logs.slice(-4).join(' | ')); return done([A]);
  }
  await sleep(5000);
  console.log('A home census:', await A.v(CENSUS));

  await step(A, 'open AI Chat', clickTitle('AI Chat'));
  if (!await waitFor(A, "document.body.innerText.includes('AI Chat Setup')", 30000)) { check('setup page opens', false); return bail(A, 'setup page did not open') }
  await sleep(4000);
  console.log('A setup census:', await A.v(CENSUS));

  await step(A, 'open provider picker', openPicker('anthropic'));
  if (!await waitFor(A, "document.body.innerText.includes('Bus Agent (external)')", 15000)) { check('picker menu shows Bus Agent', false); return bail(A, 'no picker menu') }
  await step(A, 'pick Bus Agent', click('Bus Agent (external)'));
  if (!await waitFor(A, "document.body.innerText.includes('bus-agent')", 15000)) { check('provider switched', false); return bail(A, 'provider did not switch') }
  await sleep(4000);
  console.log('A after switch census:', await A.v(CENSUS));

  const typed = await typeInto(A, FOCUS_MODEL_CM, AGENT);
  console.log('  type agent name: ' + typed);
  if (typed !== 'TYPED') return bail(A, 'could not type the agent name');
  await sleep(3000);
  console.log('A after typing census:', await A.v(CENSUS));

  await step(A, 'Start Chat', click('Start Chat'));
  if (!await waitFor(A, "!document.body.innerText.includes('AI Chat Setup') && document.body.innerText.includes(" + JSON.stringify(AGENT) + ")", 30000)) { check('chat page opens', false); return bail(A, 'chat page did not open') }
  await sleep(6000);
  console.log('A after Start Chat census:', await A.v(CENSUS));

  for (let t = 1; t <= TURNS; t++) {
    console.log('  send message ' + t + ': ' + await sendChat(A, 'probe message number ' + t + ' for the late joiner test'));
    await sleep(Math.min(REPLY_DELAY_MS, 5000));
    console.log('  A while waiting:', await A.v(CENSUS), await A.v(PAGE));
    const got = await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(REPLY + '-' + t) + ")", 90000 + REPLY_DELAY_MS);
    check('A gets reply ' + t, got, 'requests=' + requests);
    if (!got) return bail(A, 'no reply to message ' + t);
    await sleep(6000);
    console.log('A after turn ' + t + ' census:', await A.v(CENSUS));
  }
  const aCensus = await A.v(CENSUS);
  console.log('A page:', await A.v(PAGE));
  const aTotal = await A.v('theModel.newspeakEvents.length');
  console.log('A storyline:', await A.v(STORY(aTotal)));

  console.log('\n--- late joiner B ---');
  const B = await launchBrowser({ port: 9822, tag: 'slj-b', session: SESSION });
  const t0 = Date.now();
  await B.navigate(URL);
  const caught = await waitFor(B, 'window.lastProcessedEvent >= ' + aTotal, JOIN_MS);
  const secs = Math.round((Date.now() - t0) / 1000);
  const bCensus = await B.v(CENSUS);
  console.log('B after ' + secs + 's:', bCensus);
  console.log('B page:', await B.v(PAGE));
  const orph = B.logs.filter(l => l.includes('no subscriber'));
  check('B caught up', caught, secs + 's');
  check('B replay is orphan-free', orph.length === 0, orph.length + ' skips');
  if (orph.length) console.log('B orphans:\n' + orph.map(l => '    ' + l.slice(0, 220)).join('\n'));
  check('the agent saw exactly ' + TURNS + ' requests (replay added none)', requests === TURNS, 'requests=' + requests);
  const ca = JSON.parse(aCensus).cm.sort().join(',');
  const cb = bCensus ? JSON.parse(bCensus).cm.sort().join(',') : '(no census: B did not boot)';
  check('B CodeMirror census matches A', ca === cb, 'A=' + ca + ' B=' + cb);
  check('B shows the last reply', await B.v("document.body.innerText.includes(" + JSON.stringify(REPLY + '-' + TURNS) + ")"));
  /* A replaying client must record nothing: the stream's length after B's
     catch-up should equal A's, read again now so A's own late events (the
     reply's re-render settling after the earlier read) are not mistaken for
     B's. */
  const aTotalNow = await A.v('theModel.newspeakEvents.length');
  const bTotalNow = await B.v('theModel.newspeakEvents.length');
  console.log('A final census:', await A.v(CENSUS));
  check('B recorded nothing of its own', aTotalNow === bTotalNow, 'A=' + aTotalNow + ' B=' + bTotalNow + ' (A before join: ' + aTotal + ')');
  const errs = B.logs.filter(l => l.startsWith('[error]'));
  console.log('B console errors:', errs.length); errs.slice(0, 4).forEach(l => console.log('    ' + l.slice(0, 240)));
  console.log('--- B console tail ---'); console.log(B.logs.slice(-6).join('\n'));
  return done([A, B]);
}
function done(bs) { bs.forEach(b => { try { b.proc.kill() } catch (e) {} }); if (agentReq) { try { agentReq.destroy() } catch (e) {} } summary(); }
main().catch(e => { console.error(e); process.exit(1) });
