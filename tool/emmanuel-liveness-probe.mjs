// Times keystrokes in an Emmanuel document's editor in the IDE, in headless
// Chrome over the DevTools protocol, while viewers of the document (which
// refresh when it changes) are or are not alive:
// node emmanuel-liveness-probe.mjs <debugging port> <page url> <zip> <name> <outer zip> <scenario>
// Run by emmanuel-liveness-probe.py. The scenarios:
//   editor  - the document's editor only;
//   viewer  - a viewer of the document was shown (Outer transcludes it),
//             then the editor: the viewer is not on the page any more;
//   viewers - as viewer, with Outer shown and left five times.
// Prints OUTLETS (the document's contentsChanged outlets before typing),
// then KEYS: per keystroke, the time until the keystroke returns and the time
// until the page has settled (two timer turns later), in ms.
import { readFileSync } from "node:fs";

const [port, url, zip, name, outerZip, scenario] = process.argv.slice(2);
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
  const reply = await send("Runtime.evaluate", { expression, returnByValue: true, awaitPromise: true });
  if (reply.result?.exceptionDetails) throw new Error(JSON.stringify(reply.result.exceptionDetails));
  return reply.result?.result?.value;
}
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

await send("Runtime.enable");
await send("Page.enable");
await send("Page.navigate", { url });
for (let i = 0; i < 1200 && !consoleLines.includes("deck-probe-ready"); i++) await sleep(100);
if (!consoleLines.includes("deck-probe-ready")) {
  console.error("the IDE did not start:\n" + consoleLines.join("\n"));
  process.exit(1);
}

async function load(path, docName) {
  const b64 = readFileSync(path).toString("base64");
  await js(`window.deckResult = null; JSZip.loadAsync(Uint8Array.from(atob(${JSON.stringify(b64)}), c => c.charCodeAt(0))).then(z => deckLoad(z, ${JSON.stringify(docName)})), true`);
  for (let i = 0; i < 600 && !(await js("window.deckResult")); i++) await sleep(100);
  const loaded = await js("window.deckResult");
  console.log("LOAD " + loaded);
  if (loaded !== "loaded " + docName) process.exit(1);
}
await load(zip, name);
if (scenario !== "editor") {
  await load(outerZip, "Outer");
  const times = scenario === "viewers" ? 5 : 1;
  for (let k = 0; k < times; k++) {
    await js(`deckView("Outer")`);
    await sleep(3000);
    await js(`deckHome(0)`);
    await sleep(1000);
  }
}
await js(`deckOpen(${JSON.stringify(name)})`);
await sleep(4000);
await js(`window.deckResult = null; deckOutlets(${JSON.stringify(name)})`);
console.log("OUTLETS " + (await js("window.deckResult")));

// The caret at the start of the first text of the live view outside an amplet.
const placed = await js(`(() => {
  const n = [...document.querySelectorAll('span[data-item]')].find((e) => !e.closest('[data-amplet]')
    && e.closest('[contenteditable="true"]') && e.firstChild && e.firstChild.nodeType === 3 && e.firstChild.data.trim());
  if (!n) return false;
  n.closest('[contenteditable="true"]').focus();
  const r = document.createRange(); r.setStart(n.firstChild, 1); r.collapse(true);
  getSelection().removeAllRanges(); getSelection().addRange(r); return true; })()`);
if (!placed) { console.log("no text to type into"); process.exit(1); }

const settle = "new Promise((r) => setTimeout(() => setTimeout(r, 0), 0))";
const sync = [], settled = [];
for (const ch of "abcdefghijklmnopqrst") {
  const t0 = Date.now();
  await send("Input.insertText", { text: ch });
  await js("0");
  const t1 = Date.now();
  await js(settle);
  sync.push(t1 - t0);
  settled.push(Date.now() - t0);
}
console.log("KEYS sync " + sync.join(" ") + " | settled " + settled.join(" "));
await js(`window.deckResult = null; deckSource(${JSON.stringify(name)})`);
const src = await js("window.deckResult");
console.log("TYPED " + (src && src.includes("abcdefghijklmnopqrst")));
const errors = consoleLines.filter((l) => l.startsWith("EXCEPTION"));
if (errors.length) console.log(errors.join("\n"));
process.exit(0);
