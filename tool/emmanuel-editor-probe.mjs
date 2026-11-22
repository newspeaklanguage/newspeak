// Types into EmmanuelLiveEditor in a headless Chrome over the DevTools
// protocol and checks the sources it edits:
// node emmanuel-editor-probe.mjs <debugging port> <page url>
// Run by emmanuel-editor-probe.py, which starts Chrome and builds the snapshot.
const [port, url] = process.argv.slice(2);
// Any further arguments are source files to time keystrokes in, and to
// check the caret and every key at many places in.
// PROBE_DUMP=<part of a scenario name> prints that scenario's DOM, and the
// selection the browser reports at each beforeinput.

const targets = await (await fetch(`http://localhost:${port}/json/list`)).json();
const page = targets.find((t) => t.type === "page");
const ws = new WebSocket(page.webSocketDebuggerUrl);
await new Promise((resolve) => ws.addEventListener("open", resolve));

let nextId = 1;
const pending = new Map();
const consoleLines = [];
ws.addEventListener("message", (event) => {
  const message = JSON.parse(event.data);
  if (message.id && pending.has(message.id)) {
    pending.get(message.id)(message);
    pending.delete(message.id);
  } else if (message.method === "Runtime.consoleAPICalled") {
    consoleLines.push(message.params.args.map((a) => a.value ?? a.description).join(" "));
  } else if (message.method === "Runtime.exceptionThrown") {
    consoleLines.push("EXCEPTION " + JSON.stringify(message.params.exceptionDetails).slice(0, 1000));
  }
});
function send(method, params = {}) {
  const id = nextId++;
  ws.send(JSON.stringify({ id, method, params }));
  return new Promise((resolve) => pending.set(id, resolve));
}
async function js(expression) {
  const reply = await send("Runtime.evaluate", { expression, returnByValue: true });
  if (reply.result?.exceptionDetails) throw new Error(JSON.stringify(reply.result.exceptionDetails));
  return reply.result?.result?.value;
}
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

await send("Runtime.enable");
await send("Page.enable");
await send("Page.navigate", { url });
for (let i = 0; i < 600 && !consoleLines.includes("emmanuel-editor-ready"); i++) await sleep(100);
if (!consoleLines.includes("emmanuel-editor-ready")) {
  console.error("the app did not start:\n" + consoleLines.join("\n"));
  process.exit(1);
}

// Page-side helpers: put the caret at, or select, an occurrence of a text.
await js(`
  window.findText = (text) => {
    const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
    for (let n = walker.nextNode(); n; n = walker.nextNode()) {
      if (n.parentNode.tagName === 'STYLE') continue;
      const i = n.data.indexOf(text);
      if (i >= 0) return [n, i];
    }
    throw new Error("no text " + text);
  };
  window.caretAt = (text, k) => {
    const [n, i] = findText(text);
    document.body.firstChild.focus();
    const r = document.createRange();
    r.setStart(n, i + k); r.collapse(true);
    const s = getSelection(); s.removeAllRanges(); s.addRange(r);
  };
  window.caretInElement = (steps, k) => {
    const e = document.querySelector('[data-steps="' + steps + '"]');
    document.body.firstChild.focus();
    const r = document.createRange();
    r.setStart(e, k); r.collapse(true);
    const s = getSelection(); s.removeAllRanges(); s.addRange(r);
  };
  window.caretInRun = (steps, item, k) => {
    const e = [...document.querySelector('[data-steps="' + steps + '"]').childNodes].find((c) => c.getAttribute && c.getAttribute('data-item') === String(item));
    document.body.firstChild.focus();
    const r = document.createRange();
    r.setStart(e.firstChild, k); r.collapse(true);
    const s = getSelection(); s.removeAllRanges(); s.addRange(r);
  };
  window.selectText = (text) => {
    const [n, i] = findText(text);
    document.body.firstChild.focus();
    const r = document.createRange();
    r.setStart(n, i); r.setEnd(n, i + text.length);
    const s = getSelection(); s.removeAllRanges(); s.addRange(r);
  };
  true`);

const keys = {
  Backspace: { key: "Backspace", code: "Backspace", windowsVirtualKeyCode: 8 },
  Delete: { key: "Delete", code: "Delete", windowsVirtualKeyCode: 46 },
  Enter: { key: "Enter", code: "Enter", windowsVirtualKeyCode: 13, text: "\r" },
  CmdB: { key: "b", code: "KeyB", windowsVirtualKeyCode: 66, modifiers: 4 },
  CmdX: { key: "x", code: "KeyX", windowsVirtualKeyCode: 88, modifiers: 4, commands: ["cut"] },
  CmdC: { key: "c", code: "KeyC", windowsVirtualKeyCode: 67, modifiers: 4, commands: ["copy"] },
  CmdV: { key: "v", code: "KeyV", windowsVirtualKeyCode: 86, modifiers: 4, commands: ["paste"] },
  AltBackspace: { key: "Backspace", code: "Backspace", windowsVirtualKeyCode: 8, modifiers: 1, commands: ["deleteWordBackward"] },
  CmdU: { key: "u", code: "KeyU", windowsVirtualKeyCode: 85, modifiers: 4 },
  CmdShiftX: { key: "X", code: "KeyX", windowsVirtualKeyCode: 88, modifiers: 12 },
  CmdComma: { key: ",", code: "Comma", windowsVirtualKeyCode: 188, modifiers: 4 },
  CmdPeriod: { key: ".", code: "Period", windowsVirtualKeyCode: 190, modifiers: 4 },
};
async function key(name) {
  await send("Input.dispatchKeyEvent", { type: "keyDown", ...keys[name] });
  await send("Input.dispatchKeyEvent", { type: "keyUp", ...keys[name] });
}
async function type(text) {
  for (const ch of text) await send("Input.insertText", { text: ch });
}
async function source() {
  await js("emmanuelRead(0)");
  return await js("emmanuelSource");
}

const DOC = "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]";
const LIST = "[\\list. item. paragraph\\]One[\\endParagraph. endItem. item. paragraph\\]Two[\\endParagraph. endItem. endList\\]";
const STRONG_LIST = "[\\list. item. paragraph\\]One [\\strong\\]Bold[\\endStrong. endParagraph. endItem. item. paragraph\\]Two[\\endParagraph. endItem. endList\\]";
const LINK_LIST = "[\\list. item. paragraph. link: 'x.html'\\]Link[\\endLink. endParagraph. endItem. item. paragraph\\]Two[\\endParagraph. endItem. endList\\]";
const CONVERTED_LIST = "[\\paragraph\\]Before[\\endParagraph\\]\n[\\numberedList. item. paragraph\\]alpha[\\endParagraph. endItem. item. paragraph\\]beta[\\endParagraph. endItem. endNumberedList\\]\n[\\paragraph\\]After[\\endParagraph\\]";
const NEWLINES = "[\\paragraph\\]a [\\newline\\] [\\newline\\] b[\\endParagraph\\]";
const AMPLET_BETWEEN = "[\\paragraph\\]a[\\endParagraph\\][\\amplet: [x]\\][\\paragraph\\]b[\\endParagraph\\]";
const EMPTY_PARAGRAPH = "[\\paragraph\\]a[\\endParagraph\\][\\paragraph\\][\\endParagraph\\][\\paragraph\\]b[\\endParagraph\\]";
const scenarios = [
  ["type in a run", async () => { await js("caretAt('Hello', 3)"); await type("XY"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]HelXYlo world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["backspace in a run", async () => { await js("caretAt('Hello', 5)"); await key("Backspace"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hell world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["delete forward", async () => { await js("caretAt('Hello', 0)"); await key("Delete"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]ello world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["enter splits the paragraph", async () => { await js("caretAt('Hello', 5)"); await key("Enter"); },
    null],
  ["backspace at the start joins", async () => { await js("caretAt('Second', 0)"); await key("Backspace"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello worldSecond[\\endParagraph\\]"],
  ["bold a selection", async () => { await js("selectText('world')"); await key("CmdB"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello [\\strong\\]world[\\endStrong\\][\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ...[["CmdU", "underline", "endUnderline"], ["CmdShiftX", "strikethrough", "endStrikethrough"],
      ["CmdComma", "subscript", "endSubscript"], ["CmdPeriod", "superscript", "endSuperscript"]].map(([k, open, close]) =>
    [`${open} a selection (${k})`, async () => { await js("selectText('world')"); await key(k); },
      `[\\title: [\\Doc\\]\\][\\paragraph\\]Hello [\\${open}\\]world[\\${close}\\][\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]`]),
  ["a space at the end, then a letter", async () => { await js("caretAt('Second', 6)"); await type(" Z"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello world[\\endParagraph\\][\\paragraph\\]Second Z[\\endParagraph\\]"],
  ["type in the title", async () => { await js("caretAt('Doc', 3)"); await type("s"); },
    "[\\title: [\\Docs\\]\\][\\paragraph\\]Hello world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["two keystrokes keep the caret", async () => { await js("caretAt('world', 5)"); await type("!"); await key("Backspace"); await type("?"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello world?[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["two spaces are kept", async () => { await js("caretAt('Hello', 5)"); await type("  X"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello\u00a0\u00a0X world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["a space before a space is kept", async () => { await js("caretAt('Hello', 5)"); await type(" "); await type("X"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello\u00a0X world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["enter at the end of the last item", async () => { await js("caretAt('Two', 3)"); await key("Enter"); await type("Z"); },
    LIST.replace("Two[", "Two[\\endParagraph. endItem. item. paragraph\\]Z["), LIST],
  ["enter at the end of an item", async () => { await js("caretAt('One', 3)"); await key("Enter"); await type("Z"); },
    LIST.replace("One[", "One[\\endParagraph. endItem. item. paragraph\\]Z["), LIST],
  ["enter after a strong run ending an item", async () => { await js("caretAt('Bold', 4)"); await key("Enter"); await type("Z"); },
    null, STRONG_LIST],
  ["enter after a link ending an item", async () => { await js("caretAt('Link', 4)"); await key("Enter"); await type("Z"); },
    null, LINK_LIST],
  ["enter in a converted list", async () => { await js("caretAt('alpha', 5)"); await key("Enter"); await type("Z"); },
    null, CONVERTED_LIST],
  ["the raw view makes the source unparsable, then fixes it", async () => {
      await js(`emmanuelSetSource(${JSON.stringify(DOC.replace("Hello", "Hel[\\lo"))})`);
      await js(`emmanuelSetSource(${JSON.stringify(DOC.replace("Hello", "Hello!"))})`);
      await js("caretAt('Hello!', 6)"); await type("?"); },
    DOC.replace("Hello", "Hello!?")],
  ["an editor on an unparsable source", async () => { await js("emmanuelLoad('[\\\\paragraph')"); await js("document.body.firstChild.focus()"); await type("x"); },
    "[\\paragraph"],
  ["type into a space between newlines", async () => { await js("caretInRun('i0', 2, 0)"); await type("Q"); },
    "[\\paragraph\\]a [\\newline\\]Q [\\newline\\] b[\\endParagraph\\]", NEWLINES],
  ["backspace after an amplet deletes it", async () => { await js("caretInElement('', 2)"); await key("Backspace"); },
    AMPLET_BETWEEN.replace("[\\amplet: [x]\\]", ""), AMPLET_BETWEEN],
  ["backspace at the start of the block after an amplet deletes it", async () => { await js("caretAt('b', 0)"); await key("Backspace"); },
    AMPLET_BETWEEN.replace("[\\amplet: [x]\\]", ""), AMPLET_BETWEEN],
  ["delete before an amplet deletes it", async () => { await js("caretInElement('', 1)"); await key("Delete"); },
    AMPLET_BETWEEN.replace("[\\amplet: [x]\\]", ""), AMPLET_BETWEEN],
  ["delete at the end of the block before an amplet deletes it", async () => { await js("caretAt('a', 1)"); await key("Delete"); },
    AMPLET_BETWEEN.replace("[\\amplet: [x]\\]", ""), AMPLET_BETWEEN],
  ["backspace after a newline deletes it", async () => { await js("caretInRun('i0', 2, 0)"); await key("Backspace"); },
    "[\\paragraph\\]a  [\\newline\\] b[\\endParagraph\\]", NEWLINES],
  ["backspace after an empty paragraph", async () => { await js("caretInElement('', 2)"); await key("Backspace"); },
    null, EMPTY_PARAGRAPH],
];

let failures = 0;
for (const [name, act, expected, doc = DOC] of scenarios) {
  await js(`emmanuelLoad(${JSON.stringify(doc)})`);
  const before = consoleLines.length;
  if (process.env.PROBE_DUMP && name.includes(process.env.PROBE_DUMP)) {
    console.log("DOM " + await js("document.body.innerHTML"));
    await js(`document.addEventListener('beforeinput', (e) => { const r = getSelection().getRangeAt(0);
      const d = (n) => n.nodeType === 3 ? JSON.stringify(n.data) : n.tagName + '[' + (n.getAttribute('data-steps') ?? '') + ']';
      console.log('SEL ' + e.inputType + ' ' + d(r.startContainer) + '@' + r.startOffset + ' .. ' + d(r.endContainer) + '@' + r.endOffset); }, true); true`);
  }
  try {
    await act();
    const got = await source();
    const agrees = await js("emmanuelAgrees");
    const stuck = (await js("emmanuelFailed")) && !name.includes("unparsable");
    const ok = (expected === null ? got !== doc : got === expected) && agrees && !stuck;
    if (!agrees) console.log("     the incremental parse disagrees with the whole parse");
    if (stuck) console.log("     the source no longer interprets: the editor is dimmed and stuck");
    if (!ok) failures++;
    console.log(`${ok ? "PASS" : "FAIL"} ${name}\n     ${JSON.stringify(got)}${ok || expected === null ? "" : "\n want " + JSON.stringify(expected)}`);
  } catch (e) {
    failures++;
    console.log(`FAIL ${name}: ${e.message.slice(0, 300)}`);
  }
  for (const line of consoleLines.slice(before)) console.log("     console: " + line);
}
// Amplets run once: typing elsewhere does not run them again.
{
  const doc = "[\\paragraph\\]Hi [\\amplet: [self clock]\\] there[\\endParagraph\\]";
  await js(`emmanuelLoad(${JSON.stringify(doc)})`);
  await js("caretAt('there', 5)");
  await type("!!");
  const got = await source();
  const runs = await js("emmanuelRuns");
  const shown = await js("document.body.innerText.includes('ran [self clock]')");
  const ok = runs === 1 && shown && got === "[\\paragraph\\]Hi [\\amplet: [self clock]\\] there!![\\endParagraph\\]";
  if (!ok) failures++;
  console.log(`${ok ? "PASS" : "FAIL"} amplets run once\n     ${got}; runs ${runs}; shown ${shown}`);
  scenarios.push(null);
}
// An amplet's own editor gets what is typed into it: a method presenter's
// code editor in an amplet, say. The live editor used to take the input as
// an edit of the document, at its own caret.
{
  const doc = "[\\paragraph\\]a [\\amplet: [codeEditor]\\] b[\\endParagraph\\]";
  await js(`emmanuelLoad(${JSON.stringify(doc)})`);
  await sleep(300);
  await js("(() => { const cm = document.querySelector('.CodeMirror').CodeMirror; cm.focus(); cm.setCursor(0, 3); })()");
  await sleep(200);
  await type("Q");
  await key("Backspace");
  await type("RS");
  await sleep(200);
  const got = await source();
  const text = await js("document.querySelector('.CodeMirror').CodeMirror.getValue()");
  const ok = got === doc && text === "abcRS";
  if (!ok) failures++;
  console.log(`${ok ? "PASS" : "FAIL"} typing in an amplet's code editor\n     ${got}; the code editor holds ${JSON.stringify(text)}`);
  scenarios.push(null);
}
console.log(`${scenarios.length - failures}/${scenarios.length} scenarios passed`);

// Timing: with source files given, the time of a keystroke in each, typed
// at the start of its first paragraph's text.
// The raw view: a live-view edit is written into the code editor as the
// range that differs. Its offsets must be the code editor's (UTF-16), not
// psoup's (UTF-8 bytes), and the range whole characters, or the raw view
// garbles the source and hands the garbled text back as the user's edit.
{
  const nb = "\u00a0", cases = [
    ["a" + nb + "b [x] c", "a" + nb + "b [x] cQ"],
    ["a" + nb + "b [x] c", "a" + nb + "bQ [x] c"],
    ["x" + nb + "y", "x\u00a9y"],
    ["caf\u00e9 \u2014 na\u00efve", "caf\u00e9 \u2014 na\u00efveté"],
    ["\u{1F600} smile \u{1F600}", "\u{1F600} smiles \u{1F600}"],
    ["\u2018quoted\u2019 text", "\u2018quote\u2019 text"],
  ];
  let bad = 0;
  for (const [old, now] of cases) {
    await js(`emmanuelCodeMirrorWrite(${JSON.stringify(old)}, ${JSON.stringify(now)})`);
    const got = await js("emmanuelCodeMirrorText");
    if (got !== now) { bad++; console.log(`     raw view: wrote ${JSON.stringify(now)} over ${JSON.stringify(old)}, holds ${JSON.stringify(got)}`); }
  }
  if (bad) failures++;
  console.log(`raw view: ${cases.length - bad}/${cases.length} writes from the live view kept exactly`);
}

// The viewer: a transclusion embeds a document's read-only viewer, which
// must render an Emmanuel document, not show its source. The control renders
// the source as HTML, as the viewer did, and must be caught.
{
  const src = "[\\section: 'Heading'\\][\\paragraph\\]Hello [\\emphasis\\]world[\\endEmphasis\\] [\\amplet: [x]\\][\\endParagraph. endSection\\]";
  const check = async (asHTML) => {
    await js(`emmanuelView(${JSON.stringify(src)}, ${asHTML})`);
    const text = await js("emmanuelViewText");
    const editable = await js("document.body.querySelectorAll('[contenteditable=true]').length");
    const ok = !text.includes("[\\") && text.includes("Heading") && text.includes("Hello world") && editable === 0;
    return [ok, text];
  };
  const [ok, text] = await check(false);
  const [controlOk, controlText] = await check(true);
  if (!ok) { failures++; console.log(`     viewer: shows ${JSON.stringify(text)}`); }
  if (controlOk) { failures++; console.log(`     viewer control was not caught: ${JSON.stringify(controlText)}`); }
  console.log(`viewer: renders the document ${ok ? "yes" : "NO"}; control (source as HTML) caught ${controlOk ? "NO" : "yes"}`);
}

// Templates and pages. A paper (the core stylesheet) has no underline:
// Cmd-U does nothing there, while Cmd-B still works. The page limits the
// frame (the live view's border), and setting it rewrites the one page:
// statement; the width the reader gives the frame is the session's.
{
  await js(`emmanuelLoadPaper(${JSON.stringify(DOC)})`);
  await js("selectText('world')");
  await key("CmdU");
  const paperU = await source();
  await js("selectText('world')");
  await key("CmdB");
  const paperB = await source();
  const paperOk = paperU === DOC && paperB === DOC.replace("world", "[\\strong\\]world[\\endStrong\\]");
  await js(`emmanuelLoad(${JSON.stringify(DOC)})`);
  const before = await js("document.body.firstChild.style.maxWidth");
  await js("emmanuelSetPage('letter')");
  const letter = await source();
  const frame = await js("document.body.firstChild.style.maxWidth");
  const sheet = await js("getComputedStyle(document.body.querySelector('article')).maxWidth");
  await js("emmanuelSetPage('a4')");
  const a4 = await source();
  const pageOk = before === "100%" && letter === "[\\page: 'letter'\\]" + DOC && frame.includes("828px")
    && sheet === "816px" && a4 === "[\\page: 'a4'\\]" + DOC;
  const resize = await js("getComputedStyle(document.body.firstChild).resize");
  await js("(() => { const r = document.body.firstChild; r.style.width = '300px'; r.style.height = '400px'; r.dispatchEvent(new MouseEvent('mouseup', { bubbles: true })); })()");
  await js("caretAt('Second', 6)");
  await type("Z");
  await js("emmanuelFrameWidth(0)");
  const kept = await js("emmanuelFrame");
  const keptHigh = await js("emmanuelFrameHeight");
  const widthOk = resize === "both" && kept === "300px" && (await js("document.body.firstChild.style.width")) === "300px"
    && keptHigh === "400px" && (await js("document.body.firstChild.style.height")) === "400px";
  // A slide in the editor: zoomed to the frame, never past its 1080 pixels;
  // a long one grows past its 675.
  await js(`emmanuelLoad(${JSON.stringify("[\\page: 'slide'\\]" + "[\\paragraph\\]Line[\\endParagraph\\]".repeat(30))})`);
  await sleep(1500);
  const slide = await js("(() => { const a = document.body.querySelector('article'); return a.dataset.scale + ' ' + a.clientHeight + ' ' + document.body.firstChild.style.maxWidth; })()");
  const [zoom, high, slideMax] = slide.split(" ");
  const slideOk = Number(zoom) > 0 && Number(zoom) <= 1 && Number(high) > 675 && slide.includes("calc(1092px)");
  if (!paperOk || !pageOk || !widthOk || !slideOk) failures++;
  console.log(`paper has no underline ${paperOk ? "yes" : "NO"}; page ${pageOk ? "yes" : "NO"}; frame size kept ${widthOk ? "yes" : "NO"}; slide zoomed, never past 1, and long ${slideOk ? "yes" : "NO"}\n     paper ${JSON.stringify(paperU)} ${JSON.stringify(paperB)}\n     page: before ${before}, frame ${frame}, sheet ${sheet}\n     ${JSON.stringify(letter)}\n     ${JSON.stringify(a4)}\n     frame resize ${resize}, size ${kept} x ${keptHigh}\n     slide zoom, height, frame max: ${slide}`);
}

// Cut, copy, and paste, through the browser's own clipboard commands (as
// Cmd-X, Cmd-C, Cmd-V do): what is cut leaves the source, and what is
// pasted enters it.
{
  await send("Browser.grantPermissions", { permissions: ["clipboardReadWrite", "clipboardSanitizedWrite"] });
  await js(`window.inputLog = []; document.addEventListener('beforeinput', (e) => inputLog.push(e.inputType + '@' + (e.target.tagName || e.target.nodeName) + (e.target.getAttribute && e.target.getAttribute('data-steps') !== null ? '[' + e.target.getAttribute('data-steps') + ']' : '')), true); true`);
  await js(`emmanuelLoad(${JSON.stringify(DOC)})`);
  await js("selectText('world')");
  await key("CmdX");
  await sleep(300);
  const afterCut = await source();
  await js("caretAt('Second', 6)");
  await key("CmdV");
  await sleep(300);
  const afterPaste = await source();
  const log = await js("inputLog.join(', ')");
  const cutOk = afterCut === DOC.replace("Hello world", "Hello ");
  const pasteOk = afterPaste === DOC.replace("Hello world", "Hello ").replace("Second", "Secondworld");
  if (!cutOk || !pasteOk) failures++;
  console.log(`cut ${cutOk ? "yes" : "NO"}, paste ${pasteOk ? "yes" : "NO"}\n     after cut ${JSON.stringify(afterCut)}\n     after paste ${JSON.stringify(afterPaste)}\n     input events: ${log}`);
}

// Edits whose range the browser gives, not the selection: deleting a word
// (Option-Backspace), and a spelling correction, whose word replaces the
// misspelled one, wherever the caret is (synthetic, as headless Chrome has no
// spelling service).
{
  await js(`emmanuelLoad(${JSON.stringify(DOC)})`);
  await js("caretAt('world', 5)");
  await key("AltBackspace");
  await sleep(300);
  const afterWord = await source();
  await js(`emmanuelLoad(${JSON.stringify(DOC.replace("world", "wrold"))})`);
  await js("caretAt('Second', 6)");
  await js(`(() => { const [n, i] = findText('wrold');
    const range = new StaticRange({ startContainer: n, startOffset: i, endContainer: n, endOffset: i + 5 });
    const dt = new DataTransfer(); dt.setData('text/plain', 'world');
    n.parentNode.dispatchEvent(new InputEvent('beforeinput', { inputType: 'insertReplacementText', dataTransfer: dt,
      targetRanges: [range], bubbles: true, cancelable: true })); })()`);
  await sleep(300);
  const afterSpell = await source();
  const wordOk = afterWord === DOC.replace("Hello world", "Hello ");
  const spellOk = afterSpell === DOC;
  if (!wordOk || !spellOk) failures++;
  console.log(`delete a word ${wordOk ? "yes" : "NO"}, spelling correction ${spellOk ? "yes" : "NO"}\n     after word ${JSON.stringify(afterWord)}\n     after correction ${JSON.stringify(afterSpell)}`);
}

// A source that does not lex shows, above the dimmed view, what is wrong and
// where, with the line it is on; one that interprets again shows nothing.
{
  const problem = `(() => { const box = [...document.body.firstChild.children].find((e) => e.tagName === 'DIV' && e.getAttribute('contenteditable') === 'false');
    return box && box.style.display !== 'none' ? box.textContent : ''; })()`;
  const shown = async (src) => { await js(`emmanuelSetSource(${JSON.stringify(src)})`); return await js(problem); };
  await js(`emmanuelLoad(${JSON.stringify(DOC)})`);
  const stray = await shown("[\\paragraph\\]a\\]b[\\endParagraph\\]");
  const literal = await shown("[\\paragraph\\]a[\\amplet: [ 'x ]\\]b[\\endParagraph\\]");
  const bracket = await shown("[\\paragraph\\]a\n[\\emphasis");
  const fine = await shown(DOC);
  const ok = stray.startsWith("Lexical error at line 1, column 15: this \\] closes no bracket.")
    && literal.includes("a string or comment begins here and is never closed")
    && bracket.startsWith("Lexical error at line 2, column 1: this [\\ is never closed.") && fine === "";
  if (!ok) failures++;
  console.log(`lexical errors described ${ok ? "yes" : "NO"}\n     ${JSON.stringify(stray)}\n     ${JSON.stringify(literal)}\n     ${JSON.stringify(bracket)}\n     after a fix: ${JSON.stringify(fine)}`);
}

// The new styles render as their HTML elements, and a background as the
// document's background image, in the viewer and in the editor. The control
// renders the source as HTML and must be caught.
{
  const src = "[\\background: 'eye.png'\\][\\paragraph\\]a[\\underline\\]u[\\endUnderline. strikethrough\\]s[\\endStrikethrough\\]H[\\subscript\\]2[\\endSubscript\\]x[\\superscript\\]2[\\endSuperscript. endParagraph\\]";
  const looks = `(() => { const tags = ['u', 's', 'sub', 'sup'].every((t) => document.body.querySelector(t + '[data-steps]'));
    const art = document.body.querySelector('article'); const bg = art ? getComputedStyle(art).backgroundImage : 'none';
    return [tags, bg]; })()`;
  const check = async (asHTML) => {
    await js(`emmanuelView(${JSON.stringify(src)}, ${asHTML})`);
    const [tags, bg] = await js(looks);
    return [tags && bg.includes("eye.png"), `tags ${tags}, background ${bg}`];
  };
  const [ok, what] = await check(false);
  const [controlOk, controlWhat] = await check(true);
  await js(`emmanuelLoad(${JSON.stringify(src)})`);
  const [etags, ebg] = await js(looks);
  const editorOk = etags && ebg.includes("eye.png");
  if (!ok || !editorOk) { failures++; console.log(`     styles: viewer ${what}; editor tags ${etags}, background ${ebg}`); }
  if (controlOk) { failures++; console.log(`     styles control was not caught: ${controlWhat}`); }
  console.log(`styles and background: viewer ${ok ? "yes" : "NO"}, editor ${editorOk ? "yes" : "NO"}; control caught ${controlOk ? "NO" : "yes"}`);
}

// Links: every place a click can put the caret in a document with links,
// and every key there. No edit may leave the source uninterpretable (the
// editor would dim and refuse all further edits), raise, or disagree.
await js(`
  window.places = () => {
    const root = document.body.firstChild; const out = [];
    const walk = (node) => {
      if (node.nodeType === 1 && node.getAttribute('contenteditable') === 'false') return;
      if (node.nodeType === 1 && node.tagName === 'STYLE') return;
      const size = node.nodeType === 3 ? node.length : node.childNodes.length;
      for (let k = 0; k <= size; k++) out.push([node, k]);
      if (node.nodeType === 1) for (const c of node.childNodes) walk(c);
    };
    walk(root); return out;
  };
  window.placeCaret = (i) => {
    const [node, k] = places()[i];
    document.body.firstChild.focus(); const r = document.createRange(); r.setStart(node, k); r.collapse(true);
    getSelection().removeAllRanges(); getSelection().addRange(r);
    return node.nodeType === 3 ? JSON.stringify(node.data) + '@' + k
      : '<' + node.tagName + ' ' + (node.getAttribute('data-steps') || '') + '>@' + k;
  };
  true`);
const LINK_DOCS = [
  LINK_LIST,
  "[\\paragraph\\]See [\\link: 'x.html'\\]the link[\\endLink\\] here.[\\endParagraph\\]",
  "[\\paragraph. link: 'x.html'\\]whole[\\endLink. endParagraph\\][\\paragraph\\]next[\\endParagraph\\]",
  "[\\paragraph\\]a [\\link: 'x.html'\\]b [\\strong\\]c[\\endStrong\\] d[\\endLink\\] e[\\endParagraph\\]",
];
{
  const actions = [["Q", () => type("Q")], ["Enter", () => key("Enter")], ["Backspace", () => key("Backspace")],
                   ["Delete", () => key("Delete")], ["space", () => type(" ")], ["QQ", () => type("QQ")],
                   ["Backspace x2", async () => { await key("Backspace"); await key("Backspace"); }]];
  const errors = [];
  let tried = 0;
  for (const doc of LINK_DOCS) {
    await js(`emmanuelLoad(${JSON.stringify(doc)})`);
    const count = await js("places().length");
    for (let i = 0; i < count; i++) {
      for (const [label, act] of actions) {
        await js(`emmanuelLoad(${JSON.stringify(doc)})`);
        const where = await js(`placeCaret(${i})`);
        const before = consoleLines.length;
        await act();
        tried++;
        const got = await source();
        const agrees = await js("emmanuelAgrees");
        const stuck = await js("emmanuelFailed");
        const said = consoleLines.slice(before).filter((l) => l.includes("Emmanuel editor") || l.includes("Exception"));
        if (said.length || !agrees || stuck)
          errors.push(`${label} at ${where} in ${JSON.stringify(doc)}: ${agrees ? "" : "DISAGREES "}${stuck ? "STUCK " + JSON.stringify(got) + " " : ""}${said.join(" | ").slice(0, 300)}`);
      }
    }
  }
  // Selections: from one place to a later one, then a key.
  const selActions = [["Q", () => type("Q")], ["Backspace", () => key("Backspace")], ["Enter", () => key("Enter")]];
  for (const doc of LINK_DOCS) {
    await js(`emmanuelLoad(${JSON.stringify(doc)})`);
    const count = await js("places().length");
    for (let i = 0; i < count; i += 2) {
      for (let j = i + 1; j < count; j += 3) {
        const [label, act] = selActions[(i + j) % selActions.length];
        await js(`emmanuelLoad(${JSON.stringify(doc)})`);
        const where = await js(`(() => { const ps = places(); const [a, ka] = ps[${i}]; const [b, kb] = ps[${j}];
          const r = document.createRange(); r.setStart(a, ka); r.setEnd(b, kb);
          if (r.collapsed) return null;
          document.body.firstChild.focus(); getSelection().removeAllRanges(); getSelection().addRange(r);
          return JSON.stringify(getSelection().toString()); })()`);
        if (where === null) continue;
        const before = consoleLines.length;
        await act();
        tried++;
        const got = await source();
        const agrees = await js("emmanuelAgrees");
        const stuck = await js("emmanuelFailed");
        const said = consoleLines.slice(before).filter((l) => l.includes("Emmanuel editor") || l.includes("Exception"));
        if (said.length || !agrees || stuck)
          errors.push(`${label} over ${where} (places ${i}..${j}) in ${JSON.stringify(doc)}: ${agrees ? "" : "DISAGREES "}${stuck ? "STUCK " + JSON.stringify(got) + " " : ""}${said.join(" | ").slice(0, 300)}`);
      }
    }
  }
  if (errors.length) failures++;
  console.log(`links: ${tried - errors.length}/${tried} edits without error`);
  for (const m of errors.slice(0, 40)) console.log("       " + m);
}

for (const path of process.argv.slice(4)) {
  const fs = await import("node:fs");
  const text = fs.readFileSync(path, "utf8");
  await js(`emmanuelLoad(${JSON.stringify(text)})`);
  const placed = await js(`(() => { const s = document.querySelector('[data-item] '); if (!s) return false;
    const n = [...document.querySelectorAll('span[data-item]')].find(e => !e.hasAttribute('contenteditable') && e.firstChild);
    if (!n) return false; document.body.firstChild.focus(); const r = document.createRange();
    r.setStart(n.firstChild, 0); r.collapse(true); getSelection().removeAllRanges(); getSelection().addRange(r); return true; })()`);
  if (!placed) { console.log(`timing ${path}: no text to type into`); continue; }
  const times = [];
  for (const ch of "abcde") {
    const t0 = Date.now();
    await send("Input.insertText", { text: ch });
    await js("0");
    times.push(Date.now() - t0);
  }
  console.log(`timing ${path.split("/").pop()} (${text.length} chars): ${times.join(", ")} ms per keystroke`);
  await js("emmanuelRead(0)");
  console.log(`       last keystroke: ${await js("emmanuelTimings")}; agrees with the whole parse: ${await js("emmanuelAgrees")}`);
  for (let i = 0; i < 3; i++) {
    await js(`emmanuelProfile(${JSON.stringify(text)})`);
    console.log(`       full pass: ${await js("emmanuelProfileResult")}`);
  }
  // The caret: a character typed at a place in a run's text appears there.
  const misplaced = [];
  let tried = 0;
  for (let n = 0; n < 40; n++) {
    await js(`emmanuelLoad(${JSON.stringify(text)})`);
    const where = await js(`(() => {
      const runs = [...document.querySelectorAll('span[data-item]')].filter(e => !e.hasAttribute('contenteditable')
        && e.childNodes.length === 1 && e.firstChild.nodeType === 3 && e.firstChild.length > 0
        && !e.closest('[contenteditable=false]'));
      if (!runs.length) return null;
      const e = runs[(${n} * 7919) % runs.length]; const k = (${n} * 31) % (e.firstChild.length + 1);
      e.setAttribute('id', 'probe-run');
      document.body.firstChild.focus(); const r = document.createRange();
      r.setStart(e.firstChild, k); r.collapse(true); getSelection().removeAllRanges(); getSelection().addRange(r);
      return [e.firstChild.data, k, e.getAttribute('data-item'), e.parentNode.getAttribute('data-steps')]; })()`);
    if (!where) break;
    tried++;
    await send("Input.insertText", { text: "Q" });
    const [data, k, item, steps] = where;
    const want = data.slice(0, k) + "Q" + data.slice(k);
    const got = await js(`(() => { const p = document.querySelector('[data-steps="${steps}"]');
      const e = p && [...p.childNodes].find(c => c.getAttribute && c.getAttribute('data-item') === '${item}');
      return e ? e.textContent : null; })()`);
    if (got !== want) misplaced.push(`${JSON.stringify(want.slice(Math.max(0, k - 20), k + 21))} got ${JSON.stringify(got && got.slice(Math.max(0, k - 20), k + 21))}`);
  }
  if (misplaced.length) failures++;
  console.log(`caret ${path.split("/").pop()}: ${tried - misplaced.length}/${tried} typed where the caret was`);
  for (const m of misplaced.slice(0, 10)) console.log("       want " + m);
  // Any place a click can put the caret (in text, or between elements),
  // and any key: the editor raises no error, and stays in agreement.
  const errors = [];
  const actions = [["Q", () => type("Q")], ["Enter", () => key("Enter")], ["Backspace", () => key("Backspace")],
                   ["Delete", () => key("Delete")], ["two spaces", () => type("  ")]];
  let actsTried = 0;
  for (let n = 0; n < 80; n++) {
    await js(`emmanuelLoad(${JSON.stringify(text)})`);
    const where = await js(`(() => {
      const root = document.body.firstChild; const places = [];
      const walk = (node) => {
        if (node.nodeType === 1 && node.getAttribute('contenteditable') === 'false') return;
        if (node.nodeType === 1 && node.tagName === 'STYLE') return;
        const size = node.nodeType === 3 ? node.length : node.childNodes.length;
        for (let k = 0; k <= size; k++) places.push([node, k]);
        if (node.nodeType === 1) for (const c of node.childNodes) walk(c);
      };
      walk(root);
      const [node, k] = places[(${n} * 7919 + 13) % places.length];
      root.focus(); const r = document.createRange(); r.setStart(node, k); r.collapse(true);
      getSelection().removeAllRanges(); getSelection().addRange(r);
      const d = node.nodeType === 3 ? JSON.stringify(node.data.slice(Math.max(0, k - 12), k + 12)) + '@' + k
        : '<' + node.tagName + ' ' + (node.getAttribute('data-steps') || '') + '>@' + k;
      return d; })()`);
    const [label, act] = actions[n % actions.length];
    const before = consoleLines.length;
    await act();
    actsTried++;
    await js("emmanuelRead(0)");
    const agrees = await js("emmanuelAgrees");
    const stuck = await js("emmanuelFailed");
    const said = consoleLines.slice(before).filter((l) => l.includes("Emmanuel editor") || l.includes("Exception"));
    if (said.length || !agrees || stuck) errors.push(`${label} at ${where}: ${agrees ? "" : "DISAGREES "}${stuck ? "STUCK " + JSON.stringify((await source()).slice(0, 200)) + " " : ""}${said.join(" | ").slice(0, 300)}`);
  }
  if (errors.length) failures++;
  console.log(`keys ${path.split("/").pop()}: ${actsTried - errors.length}/${actsTried} without error`);
  for (const m of errors.slice(0, 15)) console.log("       " + m);
}
ws.close();
process.exit(failures ? 1 : 0);
