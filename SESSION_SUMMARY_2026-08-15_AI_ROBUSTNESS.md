# Session Summary 2026-08-15 — AI-IDE robustness: no more hanging chats

**Bottom line: DONE, IDE-tested, COMMITTED.** Two commits on master:

- **ccd60a8** — `seedSnapshotForRecord:` parses a proposed new top-level class
  with `extractedSnapshotFromNestedSource:` (Gilad's fix, carried over from his
  working tree; also sets the module category to `'Newspeak'`).
- **5330e91** — watchdog + history repair + Retry/Cancel (`AIAccess.ns`,
  `HopscotchForHTML5.ns`, `AI_IDE_Support.ns`).

Also this session: merged master into `webide-ai-access` (f0a2e02), and moved the
standing working rules out of memory-only into durable carriers (below).

## The problem

Gilad's framing: "if the cloud API fails for whatever reason, sessions in the IDE
hang. We need things to be more robust so that the session can pick up where it
left off." A previous instance analysed this and then — ironically — hung before
drafting anything; its analysis survived in the AnthropicChat document and was
re-verified against the source this session before any code was written. All five
of its claims held up.

Where the hang came from: a session's liveness rested entirely on one promise
chain settling. `waiting:: true` is set in `sendText:`; the only things that clear
it are `markComplete` / `markError:`. Nothing on the API path timed out —
`grep setTimeout:with:` found CodeMirror, the repo cloner, `FragmentFactory
schedule:` and `AIInstallStrategy`, and nothing else. So a stalled `fetch` left
the promise pending forever, the UI pinned at "…thinking…", with no exit but
reloading the page.

And a *clean* error was nearly as bad: a turn dying between
`appendAssistantResponse:` and `addToolResults:toMessages:` leaves `apiMessages`
ending in an assistant message with `tool_use` blocks and no matching
`tool_result` — a shape Anthropic 400s on. So one failed turn made every
subsequent turn fail too, and the only escape was `clearHistory`.

## What landed

**(a) Watchdog — `Session>>withWatchdog:ms:reason:`.** Races a promise against a
JS `setTimeout` rejecter built on `Promise.withResolvers` (the executor pattern
passes nil for both args on this bridge), clearing the timer on settle. It lives
in `Session`, so Anthropic/Gemini/OpenAI all inherit it.

Applied at **two** unbounded waits, not one — the original plan only covered the
API request:

- the provider request (`requestTimeoutMs`, default 120000)
- the `Promise.all` over tool results (`toolTimeoutMs`, default 180000) — a tool
  handler whose own promise never settles hangs a turn just as thoroughly.

Because the timer is JS-side, it also fires in the known case where a rejection
raised out of a then-closure is swallowed by the alien bridge (see
`NEWSPEAK_JS_PROMISE_NOTES_2026-05-18.md`).

`effectiveRequestTimeoutMs` / `effectiveToolTimeoutMs` tolerate nil so a `Session`
that predates the slots (schema migration on hot-load) still gets a watchdog
rather than a DNU.

**(b) History repair — `Provider>>repairTrailingToolUseIn:`.** Synthesises
`is_error` tool_results for unanswered trailing tool calls, so an interrupted
history is valid to send again. Written once on the base class in terms of each
provider's own `makeToolResult:` / `addToolResults:`, so every provider gets
repair in its native message shape; only `pendingToolUseIdsIn:` is
provider-specific.

- **Anthropic**: trailing assistant message's `tool_use` block ids. Implemented.
- **OpenAI-compatible**: trailing assistant message's `tool_calls` ids.
  Implemented.
- **Gemini**: keeps the no-op default *deliberately*. Its ids are synthesised per
  round (`toolUseBlocksFrom:` mints `gem-N` and remembers the function name in
  `pendingCallNames`) and are NOT recoverable from the stored message, whose
  `functionCall` parts carry only names. Repair would mean guessing at ids.

Called from `retryLastTurn` **and both `sendMessage:` paths** — a correction to
the original plan, which only repaired on retry. Typing a new message onto a
broken history fails exactly as a retry would.

**(c) Retry / Cancel.** `Session>>retryLastTurn` re-enters the tool loop with no
new user message: recorded tool results stay recorded, only unfinished work runs
again. If the history already ends assistant-side, the turn had in fact completed
(it died later, e.g. in `extractTextFromResponse:`), so it resolves with the
existing text rather than sending an assistant message back as a prefill.
`Session>>canRetry` gates the UI.

`ChatSubject` gains `retryLastTurn` / `cancelWaiting` / `canRetry` — methods only,
no new slots. `cancelWaiting` releases the *latch*, not the request (nothing in
the fetch path is cancellable); a late settlement still lands harmlessly, and the
message says so.

The buttons live in **`ChatStatusPresenter`**, which is the one presenter serving
BOTH chat surfaces — the inline `ChatPresenter`'s `statusFragment` and the
chat-as-document `thinkingOrModelPicker` amplet (`thinkingPickerFor:`). Anywhere
else would have meant building the recovery controls, and their promise wiring,
twice. Its `definition` is now three-state: waiting → thinking + Cancel; failed →
Retry row above the picker; else → picker. `canRetryQuietly` guards the
`subject canRetry` send because `definition` must never raise mid-render.

**Latent bug fixed on the way**: `IDEChatDocumentSubject>>markComplete` never
advanced `lastTurnIndexBeforeSend`, so two `markComplete`s with no intervening
send — exactly what a Retry produces — appended the same assistant turns twice.
It now advances the watermark, and `retryLastTurn` deliberately does NOT reset it,
so assistant turns that arrived before a failure (never rendered, because
`markError:` ran instead of `markComplete`) finally reach the transcript.

## Open threads, in priority order

1. **`web_fetch` / CORS** — the other lacuna from Gilad's original list, untouched.
   `AIAccess webFetch:` is a bare browser `fetch` with `method: GET`, so it is
   subject to CORS and most interesting targets (including newspeaklanguage.org)
   don't send permissive headers. Two independent fixes, complementary rather than
   alternative:
   - a `webFetchProxy` prefix read from `localStorage` (same per-user config
     pattern as API keys): try direct, retry through the prefix on the `TypeError`
     that CORS failures surface as. Helps *Newspeak code*, including the
     `web_fetch` tool.
   - Anthropic **server-side tools** (`web_search` / `web_fetch` run on their
     infrastructure, no browser, no CORS): needs `buildToolsPayload:` to pass
     through raw server-tool descriptors, and `hasToolUse:` / `toolUseBlocksFrom:`
     to skip `server_tool_use` blocks so they don't fall into `Unknown tool:`.
     Helps the model but not our own code.
2. **Durable history** — `Session exportHistory` / `importHistory:` (JSON via
   `JSON stringify:` / `parse:`) stashed in the chat doc alongside `contents`, so
   a reload rehydrates a real conversation. Today `apiMessages` is a List of JS
   aliens, which don't survive a snapshot; the document HTML keeps only a
   *projection* (user/assistant sections) with no tool-call structure, so it can't
   be replayed into a session.
3. **Gemini repair**, if its id handling is ever made recoverable.

## Housekeeping done this session

- **Merged master into `webide-ai-access`** (f0a2e02): the FragmentFactory
  refactor, the document-save fixes, senders/implementors performance, PWA version
  bump. All merged `.ns` files parse-validate clean.
- **Standing rules now have durable carriers**, not just Claude's memory:
  `CLAUDE.md` at the root of BOTH worktrees (local-only, added to
  `.git/info/exclude` so it can't be committed accidentally — note untracked files
  are per-worktree, so the two copies must be edited together or they drift), plus
  a new step 6 in `.claude/commands/newspeak-session.md`. Covers: pretty-print +
  round-trip-check + parse-validate gates, never commit unless asked, rebuild
  policy (hot-load vs re-parenting/bootstrap), worktree layout.

## Notes for whoever picks this up

- A file copy between worktrees is **not** a safe way to move work: this session
  nearly reverted commit `1c12318`'s `deferredFragment` that way. The safe move is
  to take the other tree's current file and re-apply your own edits on top (done
  twice here, for `AI_IDE_Support.ns` and `HopscotchForHTML5.ns`).
- There is a sibling worktree `.claude/worktrees/hopscotch-list-perf` with large
  Hopscotch changes in flight. The chat classes touched here (`ChatSubject`,
  `ChatStatusPresenter`) live at the end of `HopscotchForHTML5.ns`, well away from
  the list/perf machinery.
