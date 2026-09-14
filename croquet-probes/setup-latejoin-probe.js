/* Late join after the AI chat setup form was driven through the UI and a chat
 * exchanged messages - by default from a CLASS PRESENTER's brain button, with
 * a tool-call round in every turn - against either a BUS agent or a REMOTE
 * (HTTP, OpenAI-compatible) provider, both played by this probe.
 *
 * History. The 2026-09-12 stall: a late joiner orphaned keystrokes for editor
 * ordinals it had numbered differently, because programmatic editor changes
 * were published and a replaying joiner re-published its own
 * (CROQUET_REPLAY_CONTAMINATION_2026-09-12.md). The 2026-09-13 sessions, with
 * that fixed: the joiner logged 'holding early answer' then orphaned
 * keystrokes (replay ran ahead of the tool round's asynchronous continuation -
 * fixed in the glue), and then minted a coordination key the original never
 * had (a TOOL RESULT computed per client - fixed by sharing tool results
 * through the host). All of those ingredients are in here now, and the
 * request bodies the provider receives are recorded and diffed, so a
 * divergence names its first differing message.
 *
 * Browser A drives the form and the chat; browser B cold-joins. We print the
 * full fragment registry census after every step on A, the recorded
 * storyline, and B's census, page, held answers, sharing fallbacks and orphan
 * skips.
 *
 *   ~/software/emsdk-main/node/22.16.0_64bit/bin/node croquet-probes/setup-latejoin-probe.js
 *
 * Needs the front door on :8080 (started with --bus for PROVIDER=bus) and the
 * reflector on :9090. Environment:
 *   PROVIDER=bus | openai-compat   who answers completions (default bus)
 *   NS_SUFFIX=-TEST                run the -TEST vfuel (default: live)
 *   NS_PAGE=croquetpsoup-test.html run the TEST runtime glue (default: live)
 *   TURNS=2                        messages A sends before B joins
 *   REPLY_DELAY_MS=30000           how long the provider sits on a request (0 = at once)
 *   FROM_CLASS=1                   open the chat from a class presenter's brain (0: chat page)
 *   TOOL_TURNS=1                   each message is first answered with a tool call (0: text only)
 *   TOOL=evaluate | current_focus  the tool asked for (evaluate reads a client-local value)
 *   NOTICE=1                       turn 1's tool call is propose_changes; A clicks the
 *                                  proposal's Apply button, so turn 2's request carries the
 *                                  IDE notices (codebase changed + changeset applied) in its
 *                                  system prompt - the joiner must queue the same notices
 *                                  from the replayed click, or its key for turn 2 diverges
 *   FAIL_TURN=1                    the provider answers that turn's text request with HTTP
 *                                  500 once; A sees the failed turn and clicks Retry. The
 *                                  failure is unrecorded and clears the model's entry, so
 *                                  a joiner replaying the Send finds no answer for that key
 *                                  (remote provider only)
 *   JOIN_MS=240000                 how long to give B to catch up
 */
if (!process.env.NODE_PATH) {
  process.env.NODE_PATH = '/Users/gbracha/newspeak/dev/web/croquet/packages/reflector/node_modules';
  require('module').Module._initPaths();
}
const http = require('http');
const fs = require('fs');
const path = require('path');
const { sleep, launchBrowser, click, waitFor, makeChecker } = require('./harness');
const { check, summary } = makeChecker();

const ORIGIN = 'http://localhost:8080';
const PROVIDER = process.env.PROVIDER || 'bus';
const REMOTE = PROVIDER === 'openai-compat';
const SUFFIX = process.env.NS_SUFFIX || '';
const NS_PAGE_FILE = process.env.NS_PAGE || 'croquetpsoup.html';
const SESSION = 'sljprobe' + Math.floor(Date.now() / 1000);
const AGENT = process.env.AGENT || 'probeagent';
const TURNS = Number(process.env.TURNS || 2);
const FROM_CLASS = process.env.FROM_CLASS !== '0';
const TOOL_TURNS = process.env.TOOL_TURNS !== '0';
const CLASS_NAME = process.env.CLASS_NAME || 'Minitest';
const MOCK_PORT = 8098, MOCK_BASE = 'http://localhost:' + MOCK_PORT + '/v1', MOCK_MODEL = 'mock-alpha';
const REPLY = 'PROBE-REPLY-424242';
const URL = ORIGIN + '/' + NS_PAGE_FILE + '?snapshot=CroquetHopscotchWebIDE' + SUFFIX +
  '.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.sljprobe&apiKey=none' +
  '&reflector=ws://localhost:9090&files=/files&mintLedger=on';
/* mintLedger=on: every fragment id minted is recorded with the context it was
   minted in (HopscotchForCroquet newIdFor:, glue nsRecordMint), so a registry
   drift between A and B can be traced to the FIRST differing mint instead of
   its consequences. Cheap enough to leave on. */
const JOIN_MS = Number(process.env.JOIN_MS || 240000);
const REPLY_DELAY_MS = Number(process.env.REPLY_DELAY_MS || 30000);
/* Which tool the provider asks for in a tool round. 'evaluate' (default)
   reads the synchronization machinery's own event count - a value that is
   client-local by construction (a replaying joiner's model already holds the
   whole history) and so the sharpest test that tool RESULTS are shared rather
   than computed per client. 'current_focus' is replica-deterministic. */
const TOOL = process.env.TOOL || 'evaluate';
const TOOL_USE = TOOL === 'evaluate'
  ? { name: 'evaluate', input: { expression: "'events so far: ' , (((platform js global at: 'theModel') at: 'newspeakEvents') at: 'length') printString", in_id: 'workspace' } }
  : { name: 'current_focus', input: {} };
/* NOTICE: the first tool round proposes a changeset instead - a harmless new
   top-level class, so nothing on screen is touched - and A applies it from the
   inline Apply button between the turns. Two notices then ride turn 2's system
   prompt: the install choke point's 'codebase just changed' and the Apply
   handler's 'user applied your proposed changeset'. */
const NOTICE = process.env.NOTICE === '1';
const PROPOSE_USE = { name: 'propose_changes', input: { changes: [{ kind: 'add_top_level_class', class_name: 'ProbeMarker',
  source: "class ProbeMarker = () (\n\tpublic marker = (\n\t\t^42\n\t)\n) : ()" }] } };
/* FAIL_TURN: the text request of that turn (the one carrying the tool result)
   is answered with HTTP 500, once. */
const FAIL_TURN = Number(process.env.FAIL_TURN || 0);
/* The transcript's record of an applied proposal, by presenter (see the
   Apply step). */
const APPLIED_TEXT = FROM_CLASS ? 'is no longer pending' : 'Applied changeset';
let requests = 0, toolRequests = 0, textReplies = 0, failedOnce = false;

/* ---- the provider, either dialect -------------------------------------- */

function get(p) { return new Promise((res, rej) => { http.get(ORIGIN + p, r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) }).on('error', rej) }) }
function post(p, obj, token) {
  return new Promise((res, rej) => {
    const d = JSON.stringify(obj);
    const rq = http.request(ORIGIN + p, { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-NS-Token': token, 'Content-Length': Buffer.byteLength(d) } },
      r => { let b = ''; r.on('data', c => b += c); r.on('end', () => res(b)) });
    rq.on('error', rej); rq.end(d);
  });
}
/* Every request body the provider receives, kept for diffing: two clients
   agree on a completion's coordination key only if their request BODIES
   agree (the key is a digest of URL + body), so when a joiner mints a key the
   original never had, the bodies differ somewhere - and the diff names
   where. Written to scratch/bus-requests/<n>.json as well. */
const REQ_DIR = path.join(__dirname, '..', 'scratch', 'bus-requests');
const recorded = {};
function recordRequest(n, body) {
  recorded[n] = body;
  try { fs.mkdirSync(REQ_DIR, { recursive: true }); fs.writeFileSync(path.join(REQ_DIR, n + '.json'), JSON.stringify(body, null, 1)) } catch (e) {}
}
/* The last tool result in a request body, or null. Anthropic dialect: a
   tool_result block in the last user message; OpenAI dialect: a role:'tool'
   message. */
function toolResultTextOf(body) {
  try {
    const msgs = body.messages || [];
    const last = msgs[msgs.length - 1];
    if (!last) return null;
    if (last.role === 'tool') return typeof last.content === 'string' ? last.content : JSON.stringify(last.content);
    const blk = Array.isArray(last.content) && last.content.find(b => b && b.type === 'tool_result');
    if (!blk) return null;
    if (typeof blk.content === 'string') return blk.content;
    const t = Array.isArray(blk.content) && blk.content.find(c => c && c.type === 'text');
    return t ? t.text : JSON.stringify(blk.content);
  } catch (e) { return null }
}
function carriesToolResult(body) { return toolResultTextOf(body) !== null }
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
/* Decide the answer to a request: with TOOL_TURNS, a user message is first
   answered with a tool call (the IDE runs it and comes back with the result),
   and the result gets the text reply. Returns {useTool, n}. */
function classify(body) {
  requests++;
  const n = requests;
  recordRequest(n, body);
  const useTool = TOOL_TURNS && !carriesToolResult(body);
  if (useTool) toolRequests++; else textReplies++;
  const tool = useTool ? (NOTICE && toolRequests === 1 ? PROPOSE_USE : TOOL_USE) : null;
  /* The failing answer: turn FAIL_TURN's text request, the first time it
     comes. The Retry re-sends the same body and gets that turn's reply. */
  const fail = !useTool && FAIL_TURN > 0 && textReplies === FAIL_TURN && !failedOnce;
  if (fail) { failedOnce = true; textReplies-- }
  if (!useTool) console.log('  provider: tool result in request ' + n + ': ' + JSON.stringify(toolResultTextOf(body)).slice(0, 160));
  console.log('  provider: request ' + n + ' received (' + (fail ? 'answering HTTP 500' : useTool ? 'answering with tool call ' + tool.name : 'answering text ' + textReplies) + ') in ' + REPLY_DELAY_MS + 'ms');
  return { useTool, tool, fail, n, text: REPLY + '-' + textReplies };
}
/* The system prompt of a request body, whichever dialect: OpenAI puts it in
   messages[0] as role 'system'; Anthropic (the bus) in `system`, a string or
   an array of text blocks. Notices are folded into it. */
function systemTextOf(body) {
  try {
    const m0 = (body.messages || [])[0];
    if (m0 && m0.role === 'system') return typeof m0.content === 'string' ? m0.content : JSON.stringify(m0.content);
    const s = body.system;
    if (typeof s === 'string') return s;
    if (Array.isArray(s)) return s.map(b => b && b.text || '').join('\n');
  } catch (e) {}
  return '';
}
/* Bus agent: hold the SSE open under our name, answer completion_request in
   the Anthropic dialect. */
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
            const { useTool, tool, n, text } = classify(msg.request || msg);
            const content = useTool
              ? [{ type: 'tool_use', id: 'toolu_' + n, name: tool.name, input: tool.input }]
              : [{ type: 'text', text }];
            setTimeout(() => {
              post('/_ns/bus', { to: msg.from, from: AGENT, kind: 'completion_response', corr_id: msg.corr_id,
                response: { id: 'msg_' + n, type: 'message', role: 'assistant', content, stop_reason: useTool ? 'tool_use' : 'end_turn',
                  usage: { input_tokens: 1, output_tokens: 1 } } }, token).catch(() => {});
            }, REPLY_DELAY_MS);
          }
        }
      });
      resolve(req);
    });
  });
}
/* Remote provider: an OpenAI-compatible endpoint. Under Croquet the
   completion is a POST through the coordinated fetcher, so only the elected
   client reaches here - and the count is the measurement. */
function mockServer() {
  const cors = res => { res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET,POST,OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type,Authorization'); };
  return http.createServer((req, res) => {
    cors(res);
    console.log('  provider: ' + req.method + ' ' + req.url);
    if (req.method === 'OPTIONS') { res.writeHead(204); return res.end() }
    if (req.url.endsWith('/models')) {
      res.writeHead(200, { 'Content-Type': 'application/json' });
      return res.end(JSON.stringify({ object: 'list', data: [{ id: MOCK_MODEL, display_name: 'Mock Alpha' }] }));
    }
    if (req.url.endsWith('/chat/completions') && req.method === 'POST') {
      let b = ''; req.on('data', c => b += c);
      return req.on('end', () => {
        let body = {}; try { body = JSON.parse(b) } catch (e) {}
        const { useTool, tool, fail, n, text } = classify(body);
        const message = useTool
          ? { role: 'assistant', content: null, tool_calls: [{ id: 'call_' + n, type: 'function', function: { name: tool.name, arguments: JSON.stringify(tool.input) } }] }
          : { role: 'assistant', content: text };
        setTimeout(() => {
          if (fail) {
            res.writeHead(500, { 'Content-Type': 'application/json' });
            return res.end(JSON.stringify({ error: { message: 'probe-induced failure of request ' + n } }));
          }
          res.writeHead(200, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ id: 'cmpl-' + n, object: 'chat.completion', model: MOCK_MODEL,
            choices: [{ index: 0, message, finish_reason: useTool ? 'tool_calls' : 'stop' }],
            usage: { prompt_tokens: 1, completion_tokens: 1 } }));
        }, REPLY_DELAY_MS);
      });
    }
    res.writeHead(404); res.end('no');
  }).listen(MOCK_PORT);
}

/* ---- page-side expressions --------------------------------------------- */

/* Live registry census: every subscribed fragment, by kind. A subscription
   key is scope + fid + eventSpec, and every eventSpec starts with 'model_',
   so the part before 'model_' names the fragment ('nsbutton_/3'). `cm` keeps
   the CodeMirror ordinals as a readable list; `all` is the complete set, kind
   by kind, so ordinal drift in buttons, image buttons, toggles or links shows
   up too. */
const CENSUS = `(function(){var cm=new Set(),all={};Array.from(newspeakSubscriptions.keys()).forEach(function(k){` +
  `var f=k.split('model_')[0];var i=f.indexOf('_');var kind=f.slice(0,i),fid=f.slice(i+1);` +
  `(all[kind]=all[kind]||new Set()).add(fid);if(kind==='nscodemirror')cm.add(fid)});` +
  `var out={};Object.keys(all).sort().forEach(function(k){out[k]=Array.from(all[k]).sort()});` +
  `return JSON.stringify({processed:lastProcessedEvent,total:theModel.newspeakEvents.length,onScreen:document.querySelectorAll('.CodeMirror').length,cm:Array.from(cm),all:out})})()`;
const STORY = n => `(function(){var ev=theModel.newspeakEvents.slice(0,${n});var seen=[];` +
  `ev.forEach(function(e,i){var t=e.scope+e.fid+':'+String(e.eventSpec).replace('model_','');` +
  `if(seen.indexOf(t)<0)seen.push(i+' '+t)});return seen.join(' | ')})()`;
const PAGE = `(document.body.innerText||'').replace(/\\s+/g,' ').slice(0,300)`;
/* Is a real <button> with exactly this label on the page? The changeset
   presenter shows the same word as an italic LABEL until its diff has been
   computed and only then as a button; matching any element found the label,
   and the click went to it (2026-09-13). */
const HAS_BUTTON = label => `Array.from(document.querySelectorAll('button')).some(function(e){return (e.innerText||'').trim()===${JSON.stringify(label)}})`;
/* The keys of the recorded coordinated answers in the history, in order (a
   key repeats when the model answers a late requester again - by design, so
   the per-client processed-event counting stays exact). */
const LOADED_KEYS = `JSON.stringify(theModel.newspeakEvents.filter(function(e){return String(e.eventSpec).indexOf('coordinatedFetch_loaded')>=0}).map(function(e){return String(e.fid)}))`;
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
/* The row of the setup form whose bold label is `label` ('Model:', 'Base
   URL:', 'API Key:', or the provider name for the picker row): walk up from
   the label until an ancestor holds what we want. */
const rowOf = label => `var lab=Array.from(document.querySelectorAll('span,div,label,b'))` +
  `.filter(function(e){return (e.innerText||'').trim().toLowerCase()===${JSON.stringify(label)}.toLowerCase()&&e.children.length===0});` +
  `if(!lab.length)return 'NOLABEL';var row=lab[lab.length-1].parentElement;`;
/* Click the drop-down image button in `label`'s row. */
const openPickerIn = label => `(function(){${rowOf(label)}var img=null;` +
  `for(var k=0;k<6&&row&&!img;k++){img=row.querySelector('img');if(!img)row=row.parentElement}` +
  `if(!img)return 'NOIMG';var T=img;${MOUSE};return 'CLICKED'})()`;
/* Focus the CodeMirror in `label`'s row; the text is then typed with real
   keystrokes (typeInto). A setValue would be a PROGRAMMATIC change, which the
   Croquet layer handles locally and does not publish - a joiner replaying the
   form would never see the text. A user's typing is tagged '+input' and
   published. Answers 'NOCM' when the row has no editor (a model field that
   rendered as a dropdown, say). */
const focusRowCM = label => `(function(){${rowOf(label)}var cm=null;` +
  `for(var k=0;k<6&&row&&!cm;k++){cm=row.querySelector('.CodeMirror');if(!cm)row=row.parentElement}` +
  `if(!cm)return 'NOCM';cm.CodeMirror.focus();cm.CodeMirror.execCommand('selectAll');return 'FOCUSED'})()`;
/* Form fields are selected whole before typing, so the text REPLACES what the
   form pre-filled (the base URL defaults to Ollama's http://localhost:11434/v1;
   appending the mock's URL to it sent the completion to port 11434, and the
   mock counted nothing). The chat input keeps its append-at-end focus. */
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
let agentReq = null, mock = null;
async function bail(A, msg) {
  console.log(msg);
  console.log('A page:', await A.v(PAGE));
  /* The console lines that explain a missing reply: the fetch, the election,
     the provider label, anything the session or watchdog complained about. */
  const rel = A.logs.filter(l => /fetch|coord|OpenAI|error|Error|fail|unavailable|held|elect|watchdog/i.test(l));
  console.log('A console (relevant, ' + rel.length + ' of ' + A.logs.length + '):');
  rel.slice(-25).forEach(l => console.log('    ' + l.slice(0, 300)));
  console.log('A console tail:'); A.logs.slice(-8).forEach(l => console.log('    ' + l.slice(0, 300)));
  /* The chat's own text (the page excerpt above is the class page's head). */
  console.log('A chat text:', await A.v(`(function(){var t=(document.body.innerText||'').replace(/\\s+/g,' ');var i=t.lastIndexOf('AI Chat');return i<0?'(no chat region)':t.slice(i,i+900)})()`));
  try { const n = await A.v('theModel.newspeakEvents.length'); console.log('A storyline:', await A.v(STORY(n))) } catch (e) {}
  return done([A]);
}

async function main() {
  const cfg = JSON.parse(await get('/_ns/config'));
  if (REMOTE) {
    mock = mockServer(); await sleep(500);
    console.log('mock OpenAI-compatible provider on ' + MOCK_BASE);
  } else {
    if (!cfg.bus) { console.log('front door has no bus (start it with --bus)'); process.exitCode = 1; return }
    const token = JSON.parse(await get('/_ns/token')).token;
    agentReq = await startAgent(token);
    console.log('agent "' + AGENT + '" listening on the bus');
  }
  if (FAIL_TURN && !REMOTE) { console.log('FAIL_TURN needs PROVIDER=openai-compat (the bus has no HTTP status to fail with)'); process.exitCode = 1; return done([]) }
  if (FAIL_TURN && !TOOL_TURNS) { console.log('FAIL_TURN fails the text request that carries a tool result; it needs TOOL_TURNS=1'); process.exitCode = 1; return done([]) }
  if (NOTICE && (!TOOL_TURNS || TURNS < 2)) { console.log('NOTICE needs TOOL_TURNS=1 and TURNS>=2 (the notices ride the turn after the Apply)'); process.exitCode = 1; return done([]) }
  console.log('provider=' + PROVIDER + ' page=' + NS_PAGE_FILE + ' vfuel suffix="' + SUFFIX + '" fromClass=' + FROM_CLASS + ' toolTurns=' + TOOL_TURNS + ' tool=' + TOOL_USE.name +
    ' notice=' + NOTICE + ' failTurn=' + FAIL_TURN);
  await sleep(1000);

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

  const menuLabel = REMOTE ? 'Local (OpenAI-compatible)' : 'Bus Agent (external)';
  const providerName = REMOTE ? 'openai-compat' : 'bus-agent';
  await step(A, 'open provider picker', openPickerIn('anthropic'));
  if (!await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(menuLabel) + ")", 15000)) { check('picker menu shows ' + menuLabel, false); return bail(A, 'no picker menu') }
  await step(A, 'pick ' + menuLabel, click(menuLabel));
  if (!await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(providerName) + ")", 15000)) { check('provider switched', false); return bail(A, 'provider did not switch') }
  await sleep(4000);
  console.log('A after switch census:', await A.v(CENSUS));

  let modelName = AGENT;
  if (REMOTE) {
    /* Base URL and API key are typed like a user would; typing the base URL
       re-arms model discovery, which the mock answers, so the Model field may
       have promoted to a dropdown by the time we get to it. */
    console.log('  type base URL: ' + await typeInto(A, focusRowCM('Base URL:'), MOCK_BASE));
    console.log('  type API key: ' + await typeInto(A, focusRowCM('API Key:'), 'none'));
    await sleep(5000);
    modelName = MOCK_MODEL;
    const typed = await typeInto(A, focusRowCM('Model:'), MOCK_MODEL);
    if (typed.startsWith('TYPED')) console.log('  type model: ' + typed);
    else {
      await step(A, 'open model dropdown', openPickerIn('Model:'));
      const shown = await waitFor(A, "document.body.innerText.includes('Mock Alpha') || document.body.innerText.includes(" + JSON.stringify(MOCK_MODEL) + ")", 15000);
      if (!shown) { check('model dropdown lists the mock model', false); return bail(A, 'no model dropdown') }
      let r = await A.v(click('Mock Alpha')); if (r === 'NOBTN') r = await A.v(click(MOCK_MODEL));
      console.log('  pick model: ' + r);
    }
  } else {
    const typed = await typeInto(A, focusRowCM('Model:'), AGENT);
    console.log('  type agent name: ' + typed);
    if (!typed.startsWith('TYPED')) return bail(A, 'could not type the agent name');
  }
  await sleep(3000);
  console.log('A after typing census:', await A.v(CENSUS));

  /* The chat shows its model by id or, once discovery has named it, by
     display name ('Mock Alpha'); accept either. */
  const modelShown = "(document.body.innerText.includes(" + JSON.stringify(modelName) + ")" + (REMOTE ? " || document.body.innerText.includes('Mock Alpha')" : '') + ")";
  await step(A, 'Start Chat', click('Start Chat'));
  if (!await waitFor(A, "!document.body.innerText.includes('AI Chat Setup') && " + modelShown, 30000)) { check('chat page opens', false); return bail(A, 'chat page did not open') }
  await sleep(6000);
  console.log('A after Start Chat census:', await A.v(CENSUS));

  let focusInput = FOCUS_LAST_CM;
  if (FROM_CLASS) {
    /* Now that a chat exists, go to a class presenter and open the chat from
       ITS brain button: the chat is installed as an embedded region on that
       page and the focus is captured into it. */
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
    if (!await waitFor(A, "document.body.innerText.includes('AI Chat') && " + modelShown, 30000)) { check('chat region opens on the class page', false); return bail(A, 'chat region did not open') }
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
       after the answer (the next sendChat types into the same draft). */
    if (REPLY_DELAY_MS > 5000) console.log('  draft typed while waiting: ' + await typeInto(A, focusInput, 'draft '));
    const budget = 90000 + 2 * REPLY_DELAY_MS;
    if (FAIL_TURN === t) {
      /* The 500 fails the coordinated fetch on the elected client; the
         failure broadcast (unrecorded) puts the session in its error state,
         and the status view offers Retry - a plain button, so the click is a
         recorded user event the joiner will replay. */
      const failed = await waitFor(A, "document.body.innerText.includes('did not finish')", budget);
      check('A sees turn ' + t + ' fail', failed, 'requests=' + requests);
      if (!failed) return bail(A, 'turn ' + t + ' did not fail visibly');
      console.log('  A after failure:', await A.v(CENSUS), await A.v(PAGE));
      await sleep(3000);
      await step(A, 'click Retry', click('Retry'));
    }
    const got = await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(REPLY + '-' + t) + ")", budget);
    check('A gets reply ' + t + (FAIL_TURN === t ? ' after Retry' : ''), got, 'requests=' + requests + ' toolRequests=' + toolRequests);
    if (!got) return bail(A, 'no reply to message ' + t);
    await sleep(6000);
    if (NOTICE && t === 1) {
      /* The proposal was rendered inline at markComplete, with the install
         strategy's Apply button. Applying installs the class on every client
         (the click is recorded) and queues the two notices for turn 2. */
      const shown = await waitFor(A, HAS_BUTTON('Apply'), 30000);
      check('A shows the proposed changeset with an Apply button', shown);
      if (!shown) return bail(A, 'no Apply button after the proposal');
      await step(A, 'click Apply', click('Apply'));
      /* What the transcript shows once applied differs by presenter: the
         document-backed chat page appends an IDE line 'Applied changeset
         csN'; the inline presenter of a class presenter's region replaces
         the proposal with a 'no longer pending' banner (2026-09-13). */
      const applied = await waitFor(A, "document.body.innerText.includes(" + JSON.stringify(APPLIED_TEXT) + ")", 30000);
      check('A applies the changeset', applied);
      if (!applied) return bail(A, 'the changeset did not apply');
      await sleep(4000);
    }
    console.log('A after turn ' + t + ' census:', await A.v(CENSUS));
  }
  if (NOTICE) {
    /* Both notices must be in the system prompt of turn 2's FIRST request,
       and in no earlier one. */
    const order = Object.keys(recorded).map(Number).sort((a, b) => a - b);
    const firstOfTurn2 = 3 + (FAIL_TURN === 1 ? 1 : 0);
    /* The install choke point's notice: queued on every client by the
       replayed Apply click, so it must be in turn 2's first request. */
    const withCodebase = order.filter(k => /codebase just changed/.test(systemTextOf(recorded[k])));
    check('the codebase-changed notice rides turn 2\'s first request', withCodebase.length > 0 && withCodebase[0] === firstOfTurn2,
      'requests carrying it: ' + withCodebase.join(',') + '; expected first: ' + firstOfTurn2);
    /* The Apply handler's own notice. The inline (region) chat's hook did not
       queue it before 2026-09-13 (AI_IDE_Support IDEChatSubject>>
       changesetSubjectFor:); a vfuel built before that fix fails this one
       check and nothing else. The tools payload quotes the same sentence, so
       only the system prompt is searched. */
    const withApply = order.filter(k => /applied your proposed changeset/.test(systemTextOf(recorded[k])));
    check('the Apply notice rides turn 2\'s first request (needs a build with the inline-hook fix)', withApply.length > 0 && withApply[0] === firstOfTurn2,
      'requests carrying it: ' + withApply.join(',') + '; expected first: ' + firstOfTurn2);
  }
  /* The recorded answers so far. A asks for nothing more, so whatever is
     recorded after B joins is on B's account. */
  const loadedBefore = JSON.parse(await A.v(LOADED_KEYS));
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
  const expectedRequests = TURNS * (TOOL_TURNS ? 2 : 1) + (FAIL_TURN ? 1 : 0);
  check('the provider saw exactly ' + expectedRequests + ' requests (replay added none)', requests === expectedRequests, 'requests=' + requests + ' toolRequests=' + toolRequests);
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
  /* On a drift, the ledgers name the first mint the two clients disagree on,
     with the context label of what was being built - the registry only shows
     the consequences. Block hashes first (cheap), then the entries around the
     first differing block. */
  if (drift.length && await A.v('typeof nsLedgerBlockHashes') === 'function') {
    const ha = JSON.parse(await A.v('JSON.stringify(nsLedgerBlockHashes(50))') || '[]');
    const hb = JSON.parse(await B.v('JSON.stringify(nsLedgerBlockHashes(50))') || '[]');
    let block = null;
    /* Entries are {i, h} with h a RUNNING hash, so the first block whose hash
       differs holds the first differing mint. */
    for (let i = 0; i < Math.max(ha.length, hb.length); i++) if (!ha[i] || !hb[i] || ha[i].h !== hb[i].h) { block = i; break }
    console.log('ledger: A mints=' + await A.v('nsLedgerCount()') + ' B mints=' + await B.v('nsLedgerCount()') +
      (block === null ? ' (block hashes agree - the drift is in what was RETIRED, not minted)' : ' first differing block ' + block + ' (50 mints per block)'));
    if (block !== null) {
      const from = block * 50;
      const sa = JSON.parse(await A.v(`JSON.stringify(nsLedgerSlice(${from}, ${from + 50}))`) || '[]');
      const sb = JSON.parse(await B.v(`JSON.stringify(nsLedgerSlice(${from}, ${from + 50}))`) || '[]');
      let i = 0; while (i < Math.min(sa.length, sb.length) && JSON.stringify(sa[i]) === JSON.stringify(sb[i])) i++;
      console.log('ledger: first differing mint at index ' + (from + i) + '; A then B, from 3 before:');
      console.log('    A ' + JSON.stringify(sa.slice(Math.max(0, i - 3), i + 4)));
      console.log('    B ' + JSON.stringify(sb.slice(Math.max(0, i - 3), i + 4)));
    }
  }
  check('B shows the last reply', await B.v("document.body.innerText.includes(" + JSON.stringify(REPLY + '-' + TURNS) + ")"));
  /* Two transcript lines only a faithful replay reproduces. The failed
     attempt's error section exists on A because A's fetch failed; the model
     never recorded that failure, so a joiner can only show it by having its
     replayed Send fail the same way (or by having no answer for that key at
     all - see the request count and held answers above). The Applied line
     comes from the replayed Apply click installing the class on B. */
  const same = async (label, text) => {
    const probe = "document.body.innerText.includes(" + JSON.stringify(text) + ")";
    const onA = await A.v(probe), onB = await B.v(probe);
    check(label, !!onB || !onA, 'onA=' + onA + ' onB=' + onB);
  };
  if (FAIL_TURN) await same('B shows the failed attempt\'s error section as A does', 'HTTP 500');
  if (NOTICE) await same('B shows the applied proposal as A does (' + APPLIED_TEXT + ')', APPLIED_TEXT);
  /* Answers recorded since B joined are repeat answers to B's late requests
     - keys the history already held - unless B got itself ELECTED for a key
     nobody had answered (a replaying client fetching afresh: the failed-then-
     retried key, 2026-09-13). Those show up as NEW keys. (The plain event
     count below cannot tell, since B's recordings land on A too.) */
  const loadedAfter = JSON.parse(await A.v(LOADED_KEYS));
  const fresh = loadedAfter.slice(loadedBefore.length).filter(k => !loadedBefore.includes(k));
  check('B fetched nothing afresh (every answer recorded since it joined repeats a known key)', fresh.length === 0,
    'recorded answers before join=' + loadedBefore.length + ' after=' + loadedAfter.length + (fresh.length ? ' NEW keys: ' + fresh.join(',') : ''));
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
function done(bs) {
  bs.forEach(b => { try { b.proc.kill() } catch (e) {} });
  if (agentReq) { try { agentReq.destroy() } catch (e) {} }
  if (mock) { try { mock.close() } catch (e) {} }
  summary();
}
main().catch(e => { console.error(e); process.exit(1) });
