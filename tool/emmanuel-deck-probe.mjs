// Loads a document zip into the IDE (EmmanuelDeckProbeApp) in a headless
// Chrome over the DevTools protocol, opens it, optionally expands a toggle,
// and clicks a presentation's Next button, printing the slide shown each time:
// node emmanuel-deck-probe.mjs <port> <page url> <zip> <name> [toggle label]
// Run by emmanuel-deck-probe.py, which starts Chrome, builds the snapshot and
// checks the output.
import { readFileSync } from "node:fs";
const [port, url, zip, name, toggle] = process.argv.slice(2);

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
const text = async () => (await js("document.body.innerText")).replace(/\s+/g, " ");
const slide = async () => { const m = (await text()).match(/Slide (\d+)/); return m ? Number(m[1]) : null; };

await send("Runtime.enable");
await send("Page.enable");
await send("Page.navigate", { url });
for (let i = 0; i < 1200 && !consoleLines.includes("deck-probe-ready"); i++) await sleep(100);
if (!consoleLines.includes("deck-probe-ready")) {
  console.error("the IDE did not start:\n" + consoleLines.join("\n"));
  process.exit(1);
}

const b64 = readFileSync(zip).toString("base64");
await js(`window.deckResult = null; JSZip.loadAsync(Uint8Array.from(atob(${JSON.stringify(b64)}), c => c.charCodeAt(0))).then(z => deckLoad(z, ${JSON.stringify(name)}))`);
for (let i = 0; i < 600 && !(await js("window.deckResult")); i++) await sleep(100);
const loaded = await js("window.deckResult");
console.log("LOAD " + loaded);
if (loaded !== "loaded " + name) process.exit(1);

await js(`deckOpen(${JSON.stringify(name)})`);
await sleep(4000);
if (toggle) {
  // The disclosure image nearest the toggle's label.
  const r = await js(`(() => {
    const els = [...document.querySelectorAll('*')].filter(e => e.innerText && e.innerText.trim() === ${JSON.stringify(toggle)});
    const e = els[els.length - 1]; if (!e) return 'no label';
    for (let up = e; up; up = up.parentElement) {
      const img = up.querySelector('img');
      if (img) { for (const t of ['mousedown', 'mouseup', 'click']) img.dispatchEvent(new MouseEvent(t, { bubbles: true })); return 'expanded'; }
    }
    return 'no disclosure image'; })()`);
  await sleep(3000);
  console.log("TOGGLE " + r);
}
if (process.env.SURVEY) {
  // Every slide in turn: whether its content is taller than the canvas
  // (the slide grows past it) or wider (what is cut off).
  const fit = `(() => { const a = [...document.querySelectorAll('article')].find((e) => e.dataset.scale);
    return a ? a.scrollHeight + 'x' + a.scrollWidth + ' of ' + parseInt(getComputedStyle(a).minHeight) + 'x' + a.clientWidth + ' box ' + a.clientHeight : 'no slide'; })()`;
  let last = null;
  for (let k = 0; k < 400; k++) {
    const n = await slide();
    if (n === last) break;
    last = n;
    console.log("FIT " + n + " " + await js(fit));
    await js(`(() => { const bs = [...document.querySelectorAll('button, a, div, span')].filter(e => e.innerText && e.innerText.trim() === 'Next');
      const b = bs[bs.length - 1]; if (b) for (const t of ['mousedown', 'mouseup', 'click']) b.dispatchEvent(new MouseEvent(t, { bubbles: true })); })()`);
    await sleep(1500);
  }
  process.exit(0);
}
if (process.env.NEWSLIDE) {
  // Add a slide (the presenter's new-slide button, the first button after
  // its "Slide n" label): it is made from the presentation's master slide.
  console.log("SLIDE " + await slide());
  const r = await js(`(() => { const label = [...document.querySelectorAll('*')].find((e) => e.children.length === 0 && /^Slide \\d+$/.test(e.textContent.trim()));
    if (!label) return 'no label';
    const all = [...document.querySelectorAll('img, button')];
    const b = all.find((e) => label.compareDocumentPosition(e) & Node.DOCUMENT_POSITION_FOLLOWING);
    if (!b) return 'no button';
    for (const t of ['mousedown', 'mouseup', 'click']) b.dispatchEvent(new MouseEvent(t, { bubbles: true }));
    return 'clicked'; })()`);
  await sleep(4000);
  console.log("NEW " + r);
  console.log("SLIDE " + await slide());
  console.log("BACKGROUND " + await js(`[...document.querySelectorAll('article')].map((a) => getComputedStyle(a).backgroundImage).filter((b) => b !== 'none').join(' ') || 'none'`));
  console.log("SHOWN " + JSON.stringify(await js(`(() => { const a = [...document.querySelectorAll('article')].find((e) => e.dataset.scale); return a ? a.innerText.trim() + ' / ' + getComputedStyle(a).fontSize : 'no slide; articles ' + document.querySelectorAll('article').length + '; page ' + document.body.innerText.replace(/\s+/g, ' ').slice(-400); })()`)));
  const errors = consoleLines.filter((l) => l.startsWith("EXCEPTION"));
  if (errors.length) console.log(errors.join("\n"));
  process.exit(0);
}
console.log("SLIDE " + await slide());
for (let k = 0; k < 3; k++) {
  await js(`(() => { const bs = [...document.querySelectorAll('button, a, div, span')].filter(e => e.innerText && e.innerText.trim() === 'Next');
    const b = bs[bs.length - 1]; if (b) for (const t of ['mousedown', 'mouseup', 'click']) b.dispatchEvent(new MouseEvent(t, { bubbles: true })); })()`);
  await sleep(2500);
  console.log("SLIDE " + await slide());
}
// The slide shown is on its background image, if it has one.
console.log("BACKGROUND " + await js(`[...document.querySelectorAll('article')].map((a) => getComputedStyle(a).backgroundImage).filter((b) => b !== 'none').join(' ') || 'none'`));
// The slide shown: its size, its text's size, and whether its content
// overflows it (how much is cut off).
console.log("MEASURE " + await js(`[...document.querySelectorAll('article')].filter((a) => getComputedStyle(a).backgroundImage !== 'none' || a.style.aspectRatio || getComputedStyle(a).aspectRatio !== 'auto').map((a) => {
  const r = a.getBoundingClientRect(); const p = a.querySelector('p'); const h = a.querySelector('h1, h2, header');
  return 'box ' + Math.round(r.width) + 'x' + Math.round(r.height) + ' content ' + a.scrollHeight + ' scale ' + (a.dataset.scale || '1') + ' text ' + (p ? getComputedStyle(p).fontSize : '-') + ' title ' + (h ? getComputedStyle(h).fontSize : '-') + ' window ' + innerWidth + 'x' + innerHeight;
}).join(' | ') || 'none'`));
const errors = consoleLines.filter((l) => l.startsWith("EXCEPTION"));
if (errors.length) console.log(errors.join("\n"));
process.exit(0);
