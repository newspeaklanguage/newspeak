# Session Summary 2026-08-14..29 — AI-IDE access: hangs, web reach, rendering, and an async gate

**Everything below is committed on `master` and `webide-ai-access`, which are in
sync.** Each item was IDE-tested by Gilad before its commit.

| Commit | What |
|---|---|
| `5330e91` | AI chat: watchdog, history repair, Retry/Cancel instead of hangs |
| `ccd60a8` | Fix changeset render for proposed new top-level classes (Gilad's fix, carried over) |
| `404791c` | Session summary 2026-08-15 (the robustness arc) |
| `8ab5918` | Fix `SlotModel>>hash` passing a block to `bitXor:` |
| `4713887` | Actor turn scheduling on JS: `_js call:`, not `js call:` (landed via newspeak-a4) |
| `44e8a5d` | AI web access: server-run search/fetch, a working `local_fetch`, legible failures |
| `6b8af2a` | Host-services design + the async-bridge probe that gated it |
| `04d2f6d` | Chat turns: escape the text, and build the bubble in one place |
| `a086a63` | `classSource`: escape `&` before `"`, or entities decay on every load |

---

## 1. Chats stopped hanging

A session's liveness rested on one promise chain settling. Nothing on the API
path timed out, so a stalled fetch left the UI pinned at "…thinking…" with no
exit but a page reload. Worse, a turn dying between `appendAssistantResponse:`
and `addToolResults:toMessages:` left the history ending in unanswered tool
calls — a shape the API rejects — so *every subsequent turn* failed too.

- **Watchdog** (`Session>>withWatchdog:ms:reason:`) races a promise against a JS
  `setTimeout` rejecter, applied at **both** unbounded waits: the provider
  request and the `Promise.all` over tool results. A hanging tool handler stalls
  a turn just as effectively as a stalled fetch — the original plan covered only
  the request.
- **History repair** (`Provider>>repairTrailingToolUseIn:`) is written once on the
  base class in terms of each provider's own `makeToolResult:`/`addToolResults:`;
  only `pendingToolUseIdsIn:` is provider-specific. Anthropic and
  OpenAI-compatible implement it; **Gemini deliberately does not** — its ids are
  synthesised per round and unrecoverable from the stored message. Called from
  the *send* paths too, not just retry: a new user message on a broken history
  fails exactly as a retry would.
- **Retry/Cancel** live in `ChatStatusPresenter`, the one presenter both chat
  surfaces share, so one implementation serves the inline chat and the chat
  document.

Fixed in passing: `IDEChatDocumentSubject>>markComplete` never advanced
`lastTurnIndexBeforeSend`, so two completions without an intervening send — what
a Retry produces — appended the same assistant turns twice.

## 2. The AI can reach the web

Three faults, each hiding the next.

- **Server-run tools.** `web_search`/`web_fetch` run on Anthropic's
  infrastructure, so CORS does not apply. Declared **per request**, because which
  tool *version* is legal depends on the model and the picker can change the
  model mid-session: Opus 4.6+/Sonnet 4.6+ take the `20260209` variants, older
  models (Haiku 4.5, legacy Sonnet 4) must get the basic ones. No
  `anthropic-beta` header — these are GA, and an early draft of this code sent a
  stale one. Capped via `localStorage ns_ai_server_web_tools`.
- **`MessageNotUnderstood: AIAccess safeAt:field:`.** `webFetch:` is a *module*
  method; `safeAt:field:`/`safeStringAt:field:` were members of the nested
  `Provider`, which a module method cannot see. Every fetch that got a response
  died at the status check — the success path. **Found by the IDE's own AI**
  reading `implementors_of`/`senders_of`. The helpers now live at module level,
  once; the providers reach them lexically. (My first patch duplicated them
  instead, with a rationale that did not survive contact with Gilad's question:
  all 143 sends are implicit, so one definition serves both scopes.)
- **CORS.** `webFetch:` now tries direct and, when the request never completes,
  retries through the local CORS proxy the clone path already uses
  (`tool/cors-proxy.py`, `ns_ai_web_fetch_proxy`, `'off'` to disable). Only
  *transport* failures retry: an HTTP error is a real answer.

Our tool is renamed **`local_fetch`** so it coexists with the provider's
`web_fetch` rather than being shadowed by it; the descriptions tell the model
which instrument is which (server-run: no CORS, but only URLs already in the
conversation; local: no provenance gate, user's own network). Failures are now
readable — HTTP errors carry status and a body excerpt, transport failures say
plainly that the browser exposes no status/headers/body and that this does *not*
mean the site is down.

## 3. Replies stopped truncating

An assistant reply that mentioned markup stopped rendering partway through, so
the answer looked cut off mid-sentence. Backticks appeared to be the trigger.

They were not: backticks parse fine in Newspeak strings under **both** the
predictive and the combinatorial parser (checked), and nothing in the DOM path
treats them specially. `ChatPresenter>>messageFragment:` interpolated the reply
straight into an HTML string, so `DOMParser` read any `<…>` as **markup** and
swallowed the rest of the turn. Backticks only *looked* guilty because an AI
writing about markup puts it inside code spans.

The document path escaped correctly — which was the deeper problem: two copies of
the same bubble markup, drifted on the one thing that mattered. Both now call
`chatBubbleHtml:role:` on `HopscotchForHTML5`. One definition, escaping once.

Separately, `Document>>classSource` escaped `"` but not `&`, while the HTML
parser decodes *every* entity on load — so a class body containing `&quot;` came
back as a bare `"`, one decay per save/load cycle.

## 4. The async gate (design work, not yet built on)

`HOST_SERVICES_DESIGN_2026-08-16.md` covers three entangled decisions: consolidate
the **origin** not the process (`/_ns/…` paths + `/_ns/config` discovery, the
reflector discovered rather than WS-reverse-proxied), expose it to Newspeak as
`platform hostServices` (a namespace of attenuated capabilities, not a façade),
and confine JS promises to a thin adapter.

`AsyncBridgeProbe.ns` gated the last of those and **passed on both runtimes**: a
Newspeak promise can be fulfilled and broken from inside a JS callback, and a
raise inside a `fulfilled:` block breaks the *derived* promise — so ordinary
`on:Exception` discipline works and the "never raise in a `then:`" rule can go.
Two defects surfaced:

- A raise escaping an expat closure loses the rejection on both bridges, but on
  psoup a second one in flight **aborts the VM** (`memory access out of bounds`),
  taking unrelated work down. Specific to the psoup alien bridge — which makes
  fixing it bounded rather than a redesign.
- The probe found **actor turn scheduling on the JS runtime had never worked**
  (`ActorsForJS.ns:49`, `js call:` where every argument is an `_js` node, so an
  unbound self-send). Fixed as `4713887`.

The doc records that on **both** runtimes the provenance is an *artefact, not a
SHA* — a vfuel built from a working copy, a page packaged inside an IDE image —
so both result columns say rebuild before quoting them against a commit.

## 5. Process and tooling

- **Standing rules now have durable carriers**: `CLAUDE.md` at both worktree
  roots (local-only, git-excluded — edit both or they drift) and step 6 of
  `/newspeak-session`. Pretty-print + round-trip + parse-validate gates, no
  commits without asking, rebuild policy, worktree layout.
- **Headless probe harness** (recipe in the design doc §6.2): the native VM has
  **no JS at all** (`primitives.cc` guards those primitives with
  `#if !defined(OS_EMSCRIPTEN)`), so anything touching `js` must run as a
  WebCompiler vfuel in headless Chrome, driven over CDP by emsdk's node 22.
  Newspeak stack traces arrive as console events, which makes it a real debugging
  channel. Give every build a unique vfuel name or Chrome serves a stale one.
- Cross-session collaboration with `newspeak-a4` (NS2JS) and `newspeak-35`
  (Croquet) supplied the NS→JS probe run, the reflector discovery contract, and
  two corrections to my own work.

## 6. Open

1. **`platform hostServices` is designed, not built.** Staging in the doc §7;
   `/_ns/config` first, `ThreadingHTTPServer` + loopback + token before any bus.
2. **The psoup expat-raise bridge fix** — now known to be memory-unsafe, not just
   lossy, and localized to the psoup bridge.
3. **Durable chat history** (`Session exportHistory`/`importHistory:`) — aliens do
   not survive a snapshot, and the document keeps only a projection.
4. **Server-tool version drift**: `web_search_20260209`/`web_fetch_20260209` and
   the model list live together as data in `serverToolSpecs`/
   `supportsDynamicWebTools`; a 400 on the tools array means one-line edits there.
5. Gemini history repair, if its id handling ever becomes recoverable.
