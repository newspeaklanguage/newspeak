/* Late join after the AI chat setup form was driven through the UI and a bus
 * chat exchanged messages - by default from a CLASS PRESENTER's brain button,
 * with a tool-call round in every turn.
 *
 * Reproduces the 2026-09-12 stall: Gilad opened the chat setup from the
 * toolbar, switched the provider to Bus Agent, typed the agent name, pressed
 * Start Chat and exchanged messages with the agent. A late joiner then stalled
 * with 'no subscriber for key "nscodemirror_/2..."' at event ~562 - a
 * setValue-shaped pair on the setup form's chat-name editor, published by the
 * ORIGINAL client long after Start Chat had retired that form - and later
 * orphaned keystrokes for an editor ordinal (/24) the joiner had not minted.
 * Root cause and fix: CROQUET_REPLAY_CONTAMINATION_2026-09-12.md.
 *
 * The 2026-09-13 session (fix in place) misbehaved again with a different
 * shape: the joiner logged 'holding early answer' for a completion, then
 * orphaned keystrokes for nscodemirror_/21. Its recipe had two ingredients the
 * first probe lacked - the chat opened from a class presenter's brain button
 * (an embedded chat region, focus set) and tool calls from it - and keystrokes
 * while a reply was pending. All three are in here now.
 *
 * Browser A drives the form and the chat; the probe itself is the bus agent
 * answering on /_ns/bus, with a tool_use round first when TOOL_TURNS=1.
 * Browser B cold-joins. We print the full fragment registry census after every
 * step on A, the recorded storyline, and B's census, page, held answers and
 * orphan skips.
 *
 *   ~/software/emsdk-main/node/22.16.0_64bit/bin/node croquet-probes/setup-latejoin-probe.js
 *
 * Needs the front door on :8080 started with --bus, and the reflector on
 * :9090. Environment:
 *   NS_SUFFIX=-TEST            run the -TEST vfuel (default: live)
 *   NS_PAGE=croquetpsoup-test.html   run the TEST runtime glue (default: live)
 *   TURNS=2                    messages A sends before B joins
 *   REPLY_DELAY_MS=30000       how long the agent sits on a request (0 = at once)
 *   FROM_CLASS=1               open the chat from a class presenter's brain (0: chat page)
 *   TOOL_TURNS=1               agent answers each message with a tool_use first (0: text only)
 *   JOIN_MS=240000             how long to give B to catch up
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
const NS_PAGE_FILE = process.env.NS_PAGE || 'croquetpsoup.html';
const SESSION = 'sljprobe' + Math.floor(Date.now() / 1000);
const AGENT = process.env.AGENT || 'probeagent';
const TURNS = Number(process.env.TURNS || 2);
const FROM_CLASS = process.env.FROM_CLASS !== '0';
const TOOL_TURNS = process.env.TOOL_TURNS !== '0';
const CLASS_NAME = process.env.CLASS_NAME || 'Minitest';
/* Which tool the agent asks for in a tool round. 'evaluate' (default) reads
   the synchronization machinery's own event count - a value that is client-
   local by construction (a replaying joiner's model already holds the whole
   history) and so the sharpest test that tool RESULTS are shared rather than
   computed per client. 'current_focus' is replica-deterministic. */
const TOOL = process.env.TOOL || 'evaluate';
const TOOL_USE = TOOL === 'evaluate'
  ? { name: 'evaluate', input: { expression: "'events so far: ' , (((platform js global at: 'theModel') at: 'newspeakEvents') at: 'length') printString", in_id: 'workspace' } }
  : { name: 'current_focus', input: {} };
const REPLY = 'BUS-REPLY-424242';
const URL = ORIGIN + '/' + NS_PAGE_FILE + '?snapshot=CroquetHopscotchWebIDE' + SUFFIX +
  '.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.sljprobe&apiKey=none' +
  '&reflector=ws://localhost:9090&files=/files';
const JOIN_MS = Number(process.env.JOIN_MS || 240000);
const REPLY_DELAY_MS = Number(process.env.REPLY_DELAY_MS || 30000);
let requests = 0, toolRequests = 0, textReplies = 0;

function get(path) { return new Promise((res, rej) => { http.get(ORIGIN + path, r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) }).on('error', rej) }) }
function post(path, obj, token) {
  return new Promise((res, rej) => {
    const d = JSON.stringify(obj);
    const rq = http.request(ORIGIN + path, { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-NS-Token': token, 'Content-Length': Buffer.byteLength(d) } },
      r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) });
    rq.on('error', rej); rq.end(d);
  });
}
/* Every request body the agent receives, kept for diffing: two clients agree
   on a completion's coordination key only if their request BODIES agree (the
   key is a digest of URL + body), so when a joiner mints a key the original
   never had, the bodies differ somewhere - and the diff names where. Written
   to scratch/bus-requests/<n>.json as well. */
const fs = require('fs');
const REQ_DIR = require('path').join(__dirname, '..', 'scratch', 'bus-requests');
const recorded = {};
function recordRequest(n, msg) {
  recorded[n] = msg.request || msg;
  try { fs.mkdirSync(REQ_DIR, { recursive: true }); fs.writeFileSync(require('path').join(REQ_DIR, n + '.json'), JSON.stringify(recorded[n], null, 1)) } catch (e) {}
}
/* First difference between two request bodies, field by field, message by
   message, block by block. */
function diffRequests(a, b) {
  const s = x => JSON.stringify(x);
  if (!a || !b) return 'one side missing';
  for (const k of ['model', 'system', 'tools', 'max_tokens']) if (s(a[k]) !== s(b[k])) return k + ' differs:\n      A: ' + String(s(a[k])).slice(0, 300) + '\n      B: ' + String(s(b[k])).slice(0, 300);
  const ma = a.messages || [], mb = b.messages || [];
  for (let i = 0; i < Math.max(ma.length, mb.length); i++) {
    if (s(ma[i]) === s(mb[i])) continue;
    const ca = ma[i] && ma[i].content, cb = mb[i] && mb[i].content;
    if (Array.isArray(ca) && Array.isArray(cb)) {
      for (let j = 0; j < Math.max(ca.length, cb.length); j++) if (s(ca[j]) !== s(cb[j]))
        return 'messages[' + i + '].content[' + j + '] differs:\n      A: ' + String(s(ca[j])).slice(0, 400) + '\n      B: ' + String(s(cb[j])).slice(0, 400);
    }
    return 'messages[' + i + '] differs:\n      A: ' + String(s(ma[i])).slice(0, 400) + '\n      B: ' + String(s(mb[i])).slice(0, 400);
  }
  const ka = Object.keys(a).sort().join(','), kb = Object.keys(b).sort().join(',');
  return ka === kb ? 'no difference found in the compared fields' : 'top-level keys differ: A=' + ka + ' B=' + kb;
}
/* The text of the last tool_result in a request, or null. */
function toolResultTextOf(msg) {
  try {
    const msgs = (msg.request && msg.request.messages) || msg.messages || [];
    const last = msgs[msgs.length - 1];
    const blk = last && Array.isArray(last.content) && last.content.find(b => b && b.type === 'tool_result');
    if (!blk) return null;
    if (typeof blk.content === 'string') return blk.content;
    const t = Array.isArray(blk.content) && blk.content.find(c => c && c.type === 'text');
    return t ? t.text : JSON.stringify(blk.content);
  } catch (e) { return null }
}
/* Does this request carry a tool_result (the IDE answering our tool_use)? */
function carriesToolResult(msg) {
  try {
    const msgs = (msg.request && msg.request.messages) || msg.messages || [];
    const last = msgs[msgs.length - 1];
    return !!(last && Array.isArray(last.content) && last.content.some(b => b && b.type === 'tool_result'));
  } catch (e) { return false }
}
/* The agent: hold the SSE open under our name, answer completion_request.
   With TOOL_TURNS, a user message is first answered with a tool_use
   (current_focus - real, harmless, and exactly what the 2026-09-13 session
   did); the IDE runs it and comes back with the tool_result, which gets the
   text reply. */
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
            recordRequest(n, msg);
            const useTool = TOOL_TURNS && !carriesToolResult(msg);
            let content, stop;
            if (useTool) {
              toolRequests++;
              content = [{ type: 'tool_use', id: 'toolu_' + n, name: TOOL_USE.name, input: TOOL_USE.input }];
              stop = 'tool_use';
            } else {
              textReplies++;
              content = [{ type: 'text', text: REPLY + '-' + textReplies }];
              stop = 'end_turn';
            }
            if (!useTool) console.log('  agent: tool result in request ' + n + ': ' + JSON.stringify(toolResultTextOf(msg)).slice(0, 160));
            console.log('  agent: request ' + n + ' received (' + (useTool ? 'answering with tool_use ' + TOOL_USE.name : 'answering text ' + textReplies) + ') in ' + REPLY_DELAY_MS + 'ms');
            setTimeout(() => {
              post('/_ns/bus', { to: msg.from, from: AGENT, kind: 'completion_response', corr_id: msg.corr_id,
                response: { id: 'msg_' + n, type: 'message', role: 'assistant', content, stop_reason: stop,
                  usage: { input_tokens: 1, output_tokens: 1 } } }, token).catch(() => {});
            }, REPLY_DELAY_MS);
          }
        }
      });
      resolve(req);
    });
  });
}

/* Live registry census: every subscribed fragment, by kind. A subscription
   key is scope + fid + eventSpec, and every eventSpec starts with 'model_',
   so the part before 'model_' names the fragment ('nsbutton_/3'). `cm` keeps
   the CodeMirror ordinals as a readable list; `all` is the complete set, kind
   by kind, so ordinal drift in buttons, image buttons, toggles or links shows
   up too - the button-numbering discrepancies seen in earlier sessions would
   otherwise pass unnoticed behind a matching CodeMirror census. */
const CENSUS = `(function(){var cm=new Set(),all={};Array.from(newspeakSubscriptions.keys()).forEach(function(k){` +
  `var f=k.split('model_')[0];var i=f.indexOf('_');var kind=f.slice(0,i),fid=f.slice(i+1);` +
  `(all[kind]=all[kind]||new Set()).add(fid);if(kind==='nscodemirror')cm.add(fid)});` +
  `var out={};Object.keys(all).sort().forEach(function(k){out[k]=Array.from(all[k]).sort()});` +
  `return JSON.stringify({processed:lastProcessedEvent,total:theModel.newspeakEvents.length,onScreen:document.querySelectorAll('.CodeMirror').length,cm:Array.from(cm),all:out})})()`;
const STORY = n => `(function(){var ev=theModel.newspeakEvents.slice(0,${n});var seen=[];` +
  `ev.forEach(function(e,i){var t=e.scope+e.fid+':'+String(e.eventSpec).replace('model_','');` +
  `if(seen.indexOf(t)<0)seen.push(i+' '+t)});return seen.join(' | ')})()`;
const PAGE = `(document.body.innerText||'').replace(/\\s+/g,' ').slice(0,300)`;
const MOUSE = `['mousedown','mouseup','click'].forEach(function(x){T.dispatchEvent(new MouseEvent(x,{bubbles:true,cancelable:true,view:window}))})`;
/* Like the harness's click, but over EVERY element and by textContent, taking
   the deepest match: the home page's namespace and class entries carry an
   icon and are not among the tag names the harness inspects. */
const clickText = label => `(function(){var want=${JSON.stringify(label)};var m=Array.from(document.querySelectorAll('*'))` +
  `.filter(function(e){return (e.textContent||'').trim()===want&&!Array.from(e.children).some(function(c){return (c.textContent||'').trim()===want})});` +
  `if(!m.length)return 'NOEL';var T=m[m.length-1];${MOUSE};return 'CLICKED('+m.length+' '+T.tagName+')'})()`;
/* An ImageButtonFragment is a div (which carries the tooltip title) around an
   img that carries the onclick, so the click must land on the img. */
const clickTitle = t => `(function(){var e=document.querySelector('[title=' + ${JSON.stringify(JSON.stringify(t))} + ']');` +
  `if(!e)return 'NOEL';var T=e.querySelector('img')||e;${MOUSE};return 'CLICKED'})()`;
/* A presenter's brain button has no tooltip; it is an image button showing the
   same brain image as the toolbar's (which does carry title 'AI Chat'). Click
   the LAST brain img that is not the toolbar's. */
const CLICK_PRESENTER_BRAIN = `(function(){var tb=document.querySelector('[title="AI Chat"]');var src=tb&&tb.querySelector('img')?tb.querySelector('img').src:null;` +
  `var all=Array.from(document.querySelectorAll('img')).filter(function(i){return (src?i.src===src:/brain/i.test(i.src))&&!(tb&&tb.contains(i))});` +
  `if(!all.length)return 'NOBRAIN';var T=all[all.length-1];${MOUSE};return 'CLICKED('+all.length+')'})()`;
/* The provider picker is the drop-down image button in the same row as the
   bold label showing the current provider name. */
const openPicker = name => `(function(){var want=${JSON.stringify(name)}.toLowerCase();` +
  `var lab=Array.from(document.querySelectorAll('span,div,label,b'))` +
  `.filter(function(e){return (e.innerText||'').trim().toLowerCase()===want&&e.children.length===0});` +
  `if(!lab.length)return 'NOLABEL';var l=lab[lab.length-1];var row=l.parentElement;var img=null;` +
  `for(var k=0;k<6&&row&&!img;k++){img=row.querySelector('img');if(!img)row=row.parentElement}` +
  `if(!img)return 'NOIMG';var T=img;${MOUSE};return 'CLICKED'})()`;
/* Focus the CodeMirror in the 'Model: ' row; the text is then typed with real
   keystrokes (typeInto). A setValue would be a PROGRAMMATIC change, which
   the Croquet layer handles locally and does not publish - a joiner replaying
   the form would never see the agent name, and Start Chat would fail
   validation there. A user's typing is tagged '+input' and published. */
const FOCUS_MODEL_CM = `(function(){var lab=Array.from(document.querySelectorAll('span,div,label,b'))` +
  `.filter(function(e){return (e.innerText||'').trim()==='Model:'&&e.children.length===0});` +
  `if(!lab.length)return 'NOLABEL';var row=lab[lab.length-1].parentElement;var cm=null;` +
  `for(var k=0;k<6&&row&&!cm;k++){cm=row.querySelector('.CodeMirror');if(!cm)row=row.parentElement}` +
  `if(!cm)return 'NOCM';cm.CodeMirror.focus();return 'FOCUSED'})()`;
/* The chat input: on the chat page it is the last CodeMirror; in a presenter's
   embedded chat region it is the first CodeMirror AFTER the region's 'AI Chat'
   heading in document order. */
const FOCUS_LAST_CM = `(function(){var c=document.querySelectorAll('.CodeMirror');if(!c.length)return 'NOCM';` +
  `var cm=c[c.length-1].CodeMirror;cm.focus();cm.setCursor(cm.lineCount(),0);return 'FOCUSED:'+c.length})()`;
const FOCUS_REGION_CM = `(function(){var labs=Array.from(document.querySelectorAll('span,div,label,b'))` +
  `.filter(function(e){return (e.innerText||'').trim()==='AI Chat'&&e.children.length===0});` +
  `if(!labs.length)return 'NOREGION';var lab=labs[labs.length-1];` +
  `var cms=Array.from(document.querySelectorAll('.CodeMirror')).filter(function(c){return lab.compareDocumentPosition(c)&Node.DOCUMENT_POSITION_FOLLOWING});` +
  `if(!cms.length)return 'NOCM';var cm=cms[0].CodeMirror;cm.focus();cm.setCursor(cm.lineCount(),0);return 'FOCUSED:'+cms.length})()`;

async function typeInto(b, focusExpr, text) {
  const f = await b.v(focusExpr);
  if (!String(f).startsWith('FOCUSED')) return f;
  /* Two chunks, deliberately: the first real change after a re-render used to
     be swallowed as synthetic (see updateEditedText:), and a human's second
     keystroke is what cleared it. Fixed, but cheap to keep. */
  await b.send('Input.insertText', { text: text.slice(0, -1) });
  await sleep(300);
  await b.send('Input.insertText', { text: text.slice(-1) });
  await sleep(600);
  return 'TYPED (' + f + ')';
}
/* Type into the chat input and accept with Ctrl+Enter (respondToKeyDown:),
   through the DevTools Input domain: real keystrokes take CodeMirror's own
   input path. */
async function sendChat(b, focusExpr, text) {
  const t = await typeInto(b, focusExpr, text);
  if (!t.startsWith('TYPED')) return t;
  const key = type => b.send('Input.dispatchKeyEvent', { type, key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13, modifiers: 2 });
  await key('keyDown'); await key('keyUp');
  return 'SENT ' + t.slice(6);
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
  console.log('agent "' + AGENT + '" listening on the bus; page=' + NS_PAGE_FILE + ' vfuel suffix="' + SUFFIX + '" fromClass=' + FROM_CLASS + ' toolTurns=' + TOOL_TURNS);
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
  if (!typed.startsWith('TYPED')) return bail(A, 'could not type the agent name');
  await sleep(3000);
  console.log('A after typing census:', await A.v(CENSUS));

  await step(A, 'Start Chat', click('Start Chat'));
  if (!await waitFor(A, "!document.body.innerText.includes('AI Chat Setup') && document.body.innerText.includes(" + JSON.stringify(AGENT) + ")", 30000)) { check('chat page opens', false); return bail(A, 'chat page did not open') }
  await sleep(6000);
  console.log('A after Start Chat census:', await A.v(CENSUS));

  let focusInput = FOCUS_LAST_CM;
  if (FROM_CLASS) {
    /* Now that a chat exists, go to a class presenter and open the chat from
       ITS brain button: the chat is installed as an embedded region on that
       page and the focus is captured into it - the 2026-09-13 recipe. */
    /* The chat page has no namespace links; go home first via the toolbar's
       home button (an image button with a tooltip, like the brain). */
    await step(A, 'return to home screen', clickTitle('Return to home screen'));
    if (!await waitFor(A, "document.body.innerText.includes('Workspaces')", 30000)) { check('home page reopens', false); return bail(A, 'home page did not reopen') }
    await sleep(3000);
    await step(A, 'go to Newspeak Source', clickText('Newspeak Source'));
    if (!await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(CLASS_NAME) + ")", 30000)) { check('namespace lists ' + CLASS_NAME, false); return bail(A, 'namespace page did not list the class') }
    await sleep(2000);
    await step(A, 'open class ' + CLASS_NAME, clickText(CLASS_NAME));
    await sleep(5000);
    console.log('A class page:', await A.v(PAGE));
    await step(A, 'click the class presenter brain', CLICK_PRESENTER_BRAIN);
    if (!await waitFor(A, "document.body.innerText.includes('AI Chat') && document.body.innerText.includes(" + JSON.stringify(AGENT) + ")", 30000)) { check('chat region opens on the class page', false); return bail(A, 'chat region did not open') }
    await sleep(6000);
    console.log('A after region chat census:', await A.v(CENSUS));
    console.log('A page:', await A.v(PAGE));
    focusInput = FOCUS_REGION_CM;
  }

  for (let t = 1; t <= TURNS; t++) {
    console.log('  send message ' + t + ': ' + await sendChat(A, focusInput, 'probe message number ' + t + ' for the late joiner test'));
    await sleep(Math.min(REPLY_DELAY_MS, 5000));
    console.log('  A while waiting:', await A.v(CENSUS), await A.v(PAGE));
    /* Keystrokes recorded between the request and its answer, and more right
       after the answer (the next sendChat types into the same draft): the
       2026-09-13 session orphaned exactly such keystrokes on a joiner whose
       request had gone out AFTER the recorded answer. */
    if (REPLY_DELAY_MS > 5000) console.log('  draft typed while waiting: ' + await typeInto(A, focusInput, 'draft '));
    const got = await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(REPLY + '-' + t) + ")", 90000 + 2 * REPLY_DELAY_MS);
    check('A gets reply ' + t, got, 'requests=' + requests + ' toolRequests=' + toolRequests);
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
  const held = B.logs.filter(l => l.includes('holding early answer') || l.includes('delivering held answer'));
  check('B caught up', caught, secs + 's');
  check('B replay is orphan-free', orph.length === 0, orph.length + ' skips');
  if (orph.length) console.log('B orphans:\n' + orph.map(l => '    ' + l.slice(0, 220)).join('\n'));
  console.log('B held answers: ' + held.length + (held.length ? '\n' + held.map(l => '    ' + l.slice(0, 220)).join('\n') : ''));
  const expectedRequests = TURNS * (TOOL_TURNS ? 2 : 1);
  check('the agent saw exactly ' + expectedRequests + ' requests (replay added none)', requests === expectedRequests, 'requests=' + requests + ' toolRequests=' + toolRequests);
  /* A request beyond the expected count came from the joiner. Its body should
     equal the original's request at the same position in the conversation
     (same message count); the first difference is the divergence. */
  for (let n = expectedRequests + 1; n <= requests; n++) {
    const rb = recorded[n]; if (!rb) continue;
    const len = (rb.messages || []).length;
    const twin = Object.keys(recorded).map(Number).filter(k => k <= expectedRequests && ((recorded[k].messages || []).length === len));
    console.log('joiner request ' + n + ' (' + len + ' messages) vs original request ' + (twin.length ? twin[0] : '(none with that length)') + ':\n    ' +
      (twin.length ? diffRequests(recorded[twin[0]], rb) : 'A never sent a request with ' + len + ' messages'));
  }
  console.log('request bodies saved under ' + REQ_DIR);
  const ca = JSON.parse(aCensus).cm.sort().join(',');
  const cb = bCensus ? JSON.parse(bCensus).cm.sort().join(',') : '(no census: B did not boot)';
  check('B CodeMirror census matches A', ca === cb, 'A=' + ca + ' B=' + cb);
  /* The full registry, kind by kind. Reported per kind so a drift in one
     family (buttons, say) is named rather than buried in one big diff. */
  const allA = JSON.parse(aCensus).all, allB = bCensus ? JSON.parse(bCensus).all : {};
  const kinds = Array.from(new Set(Object.keys(allA).concat(Object.keys(allB)))).sort();
  const drift = kinds.filter(k => (allA[k] || []).join(',') !== (allB[k] || []).join(','));
  check('B full fragment registry matches A (' + kinds.length + ' kinds)', drift.length === 0,
    drift.map(k => k + ': A=' + (allA[k] || []).join(',') + ' B=' + (allB[k] || []).join(',')).join(' | ') || kinds.join(','));
  check('B shows the last reply', await B.v("document.body.innerText.includes(" + JSON.stringify(REPLY + '-' + TURNS) + ")"));
  /* The tool result the ORIGINAL sent the agent (request 2's tool_result) is
     the text the session agreed on; the joiner's transcript must show that
     text, not a value it computed for itself. */
  if (TOOL_TURNS && recorded[2]) {
    const shared = toolResultTextOf(recorded[2]);
    const probe = "document.body.innerText.includes(" + JSON.stringify(shared) + ")";
    const onA = shared ? await A.v(probe) : false, onB = shared ? await B.v(probe) : false;
    /* The DOM is a weak observable here: CodeMirror renders only visible
       lines and tool results live in collapsed amplets, so the text may be
       on neither page. The strong evidence is the registry check above: the
       next completion's key digests the whole request body, tool result
       included, so equal keys mean equal histories. This check only fails if
       the original shows the text and the joiner does not. */
    check('B renders the SHARED tool result as A does (' + JSON.stringify(shared).slice(0, 50) + ')', !!onB || !onA,
      'onA=' + onA + ' onB=' + onB + (onA || onB ? '' : ' (not in either DOM: collapsed/virtualized; keys prove the history)'));
  }
  /* A replaying client must record nothing: the stream's length after B's
     catch-up should equal A's, read again now so A's own late events are not
     mistaken for B's. */
  const aTotalNow = await A.v('theModel.newspeakEvents.length');
  const bTotalNow = await B.v('theModel.newspeakEvents.length');
  console.log('A final census:', await A.v(CENSUS));
  check('B recorded nothing of its own', aTotalNow === bTotalNow, 'A=' + aTotalNow + ' B=' + bTotalNow + ' (A before join: ' + aTotal + ')');
  /* The Session's sharing seam prints a 'shareToolText:' line whenever it
     falls back to the local text; on either client that line names why. */
  const shareA = A.logs.filter(l => l.includes('shareToolText')), shareB = B.logs.filter(l => l.includes('shareToolText'));
  console.log('A sharing fallbacks: ' + shareA.length + (shareA.length ? '\n' + shareA.map(l => '    ' + l.slice(0, 240)).join('\n') : ''));
  console.log('B sharing fallbacks: ' + shareB.length + (shareB.length ? '\n' + shareB.map(l => '    ' + l.slice(0, 240)).join('\n') : ''));
  const errs = B.logs.filter(l => l.startsWith('[error]'));
  console.log('B console errors:', errs.length); errs.slice(0, 4).forEach(l => console.log('    ' + l.slice(0, 240)));
  console.log('--- B console tail ---'); console.log(B.logs.slice(-6).join('\n'));
  return done([A, B]);
}
function done(bs) { bs.forEach(b => { try { b.proc.kill() } catch (e) {} }); if (agentReq) { try { agentReq.destroy() } catch (e) {} } summary(); }
main().catch(e => { console.error(e); process.exit(1) });
