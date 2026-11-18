// Drives EmmanuelCorpusApp in a headless Chrome over the DevTools protocol:
// node emmanuel-corpus.mjs <debugging port> <page url> <documents.json> <results.json>
// documents.json is [{name, html}]; results.json gets [{name, result}], where
// result is the app's JSON report, or {failure} when the call itself failed.
// Run by emmanuel-corpus.py, which starts Chrome and builds the snapshot.
import fs from "node:fs";

const [port, url, docsPath, outPath] = process.argv.slice(2);
const docs = JSON.parse(fs.readFileSync(docsPath, "utf8"));

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
    consoleLines.push("EXCEPTION " + JSON.stringify(message.params.exceptionDetails).slice(0, 2000));
  }
});
function send(method, params = {}) {
  const id = nextId++;
  ws.send(JSON.stringify({ id, method, params }));
  return new Promise((resolve) => pending.set(id, resolve));
}
async function waitFor(predicate, ms) {
  const end = Date.now() + ms;
  while (Date.now() < end) {
    if (predicate()) return true;
    await new Promise((r) => setTimeout(r, 100));
  }
  return false;
}

await send("Runtime.enable");
await send("Page.enable");
await send("Page.navigate", { url });
if (!(await waitFor(() => consoleLines.includes("emmanuel-corpus-ready"), 120000))) {
  console.error("the app did not start:\n" + consoleLines.join("\n"));
  process.exit(1);
}

const results = [];
for (const doc of docs) {
  const reply = await send("Runtime.evaluate", {
    expression: `emmanuelConvert(${JSON.stringify(doc.html)}); emmanuelResult`,
    returnByValue: true,
    timeout: 120000,
  });
  let result;
  if (reply.result?.exceptionDetails || typeof reply.result?.result?.value !== "string") {
    result = { failure: JSON.stringify(reply.result?.exceptionDetails ?? reply.error ?? reply.result).slice(0, 2000) };
  } else {
    try {
      result = JSON.parse(reply.result.result.value);
    } catch (e) {
      result = { failure: "bad JSON: " + String(e) };
    }
  }
  results.push({ name: doc.name, result });
  process.stdout.write(".");
}
fs.writeFileSync(outPath, JSON.stringify({ results, console: consoleLines }, null, 1));
console.log(`\n${results.length} documents`);
ws.close();
