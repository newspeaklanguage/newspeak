// Types into EmmanuelLiveEditor in a headless Chrome over the DevTools
// protocol and checks the sources it edits:
// node emmanuel-editor-probe.mjs <debugging port> <page url>
// Run by emmanuel-editor-probe.py, which starts Chrome and builds the snapshot.
const [port, url] = process.argv.slice(2);
// Any further arguments are source files to time keystrokes in.

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
  ["a space at the end, then a letter", async () => { await js("caretAt('Second', 6)"); await type(" Z"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello world[\\endParagraph\\][\\paragraph\\]Second Z[\\endParagraph\\]"],
  ["type in the title", async () => { await js("caretAt('Doc', 3)"); await type("s"); },
    "[\\title: [\\Docs\\]\\][\\paragraph\\]Hello world[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
  ["two keystrokes keep the caret", async () => { await js("caretAt('world', 5)"); await type("!"); await key("Backspace"); await type("?"); },
    "[\\title: [\\Doc\\]\\][\\paragraph\\]Hello world?[\\endParagraph\\][\\paragraph\\]Second[\\endParagraph\\]"],
];

let failures = 0;
for (const [name, act, expected] of scenarios) {
  await js(`emmanuelLoad(${JSON.stringify(DOC)})`);
  const before = consoleLines.length;
  try {
    await act();
    const got = await source();
    const agrees = await js("emmanuelAgrees");
    const ok = (expected === null ? got !== DOC : got === expected) && agrees;
    if (!agrees) console.log("     the incremental parse disagrees with the whole parse");
    if (!ok) failures++;
    console.log(`${ok ? "PASS" : "FAIL"} ${name}\n     ${got}${ok || expected === null ? "" : "\n want " + expected}`);
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
console.log(`${scenarios.length - failures}/${scenarios.length} scenarios passed`);

// Timing: with source files given, the time of a keystroke in each, typed
// at the start of its first paragraph's text.
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
}
ws.close();
process.exit(failures ? 1 : 0);
