# In-image AI session messaging — implementation spec

**Status:** ready to implement, 2026-08-31. Spun out of the host-services plan
(`HOST_SERVICES_DESIGN_2026-08-31.md` §7) as an independent parallel track.
**Scope:** AI chat sessions *within one IDE image* message each other,
addressed by chat-document name. No server, no `/_ns/bus`, no Croquet.
The bus (host-services step 6) will later extend this same address space to
external agents; do not invent addressing that only works in-image (names are
strings, not object references, in every tool-facing surface).

Read first: `CLAUDE.md` at the worktree root (mandatory editing gates),
`SESSION_SUMMARY_2026-08-14_to_29_AI_ACCESS.md` (the session/watchdog/repair
architecture this builds on).

## 0. Coordination

Work on branch `webide-ai-access` in `dev/web/webide-ai-access`. Another
instance is concurrently implementing `platform host` (server + new module).
Your write set is `AI_IDE_Support.ns` (mostly) and possibly one small addition
to `AIAccess.ns`. Do **not** touch `tool/cors-proxy.py`, any new `Host*.ns`
file, or `HopscotchWebIDE.ns` — those belong to the other track. **Never
commit; Gilad tests in the IDE first.**

## 1. What to build

Two new AI-visible tools, available in every chat session:

- **`list_chat_sessions`** — enumerate the image's chat documents: name,
  provider/model, whether a live session exists, whether it is mid-turn,
  how many messages are queued for it. Excludes the calling session.
- **`send_to_chat`** — input `{chat_name, message}`. Delivers `message` to the
  named chat's session as a full, visible, provenance-stamped user turn, and
  drives that session's completion loop so the target AI actually responds.
  **Fire-and-forget:** the tool returns delivery status immediately
  (`delivered` / `queued behind a running turn`); it never awaits the target's
  completion. Replies are not automatic — the target AI decides whether to
  answer back with its own `send_to_chat`, which is what makes a conversation.

Plus a short system-prompt paragraph so models know the tools exist and what
an incoming `[from chat '<name>']` message means.

## 2. The facts this design rests on

All in this worktree; line numbers verified 2026-08-31.

- **Naming/enumeration.** A chat doc is a `Document` (`Documents.ns:1012`
  holds `name`); the switcher's list comes from
  `chatDocumentsInRoot` (`AI_IDE_Support.ns:1570`), which scans Root for
  values answering `isKindOfChatDocument` (guarded with `on: Exception`).
  Uniqueness is enforced at bind sites only (`startChat`
  `AI_IDE_Support.ns:294`; `create_chat_document` `:3048`). Caveat:
  `create_chat_document` can bind a chat *outside* Root via a dotted path —
  such chats are invisible to this feature in v1; note that in the tool
  description.
- **No registry.** The live subject is cached **on the document**:
  `chatSubjectSlot` (declared in the template class body,
  `AI_IDE_Support.ns:1835`), built lazily by
  `chatSubjectFor:` (`AI_IDE_Support.ns:1631`), which is safe to call
  headlessly — it deliberately does not retarget the current chat. So a
  dormant (never-rendered) chat **can** be woken by materializing its subject
  on demand. `doc chatSubject` / `doc session` forwarders exist
  (`AI_IDE_Support.ns:1841-1842`).
- **Send path.** `IDEChatDocumentSubject>>sendText:`
  (`AI_IDE_Support.ns:786`) appends the visible user bubble, records
  `lastTurnIndexBeforeSend`, calls `session sendMessage:`
  (`AIAccess.ns:1373`), republishes the doc, and returns the turn promise.
  **The promise wiring is the caller's job** — the presenter does it at
  `HopscotchForHTML5.ns:6326`: `then: [markComplete] onError: [markError:]`.
  Nothing else clears `waiting` or renders the assistant's reply into the doc.
- **Busy flag.** `ChatSubject>>waiting` (`HopscotchForHTML5.ns:6104`), set by
  the send paths, cleared by `markComplete`/`markError:`/`cancelWaiting`.
  Caveat: `cancelWaiting` clears it while the fetch may still run, so treat it
  as "probably busy", not a lock.
- **No re-entrancy guard.** `sendMessage:` during an in-flight turn would
  interleave two `completeWithToolLoop` recursions over one `apiMessages`
  list. **Delivery must therefore be serialized per target** (§3.3).
- **Self-healing.** `sendMessage:` calls `repairHistory` itself
  (`AIAccess.ns:1384`), so delivering to a session whose previous turn died
  mid-tool-loop is safe.
- **Tools.** `Tool name:description:inputSchema:handler:` (`AIAccess.ns:30`);
  the catalogue array is in `toolsWithFocus:` (`AI_IDE_Support.ns:2673`);
  dispatch via `toolMap` in `Session>>executeToolCall:` (`AIAccess.ns:1046`).
  Handlers may return a value or a promise; raises and rejections are already
  converted to `is_error` tool results (`AIAccess.ns:1096-1132`). The
  focus-parameterized factory family (`currentFocusToolForFocus:` etc.) is
  the model to follow; `proposingChatFor:` (`AI_IDE_Support.ns:2109`) is the
  existing "which chat am I?" resolver.
- **Cross-session iteration idiom to copy:** `broadcastChangeAppliedBy:records:`
  (`AI_IDE_Support.ns:2129-2141`) — iterate `chatDocumentsInRoot`, read
  `chatSubjectSlot`, skip nil, exclude self with `~=` (Subjects don't
  understand `~~`), wrap each doc in `on: Exception do: [:e | nil]`.

## 3. Design

### 3.1 Identity and provenance

The **sender** is derived from the tool's `focus` (`focus chatDoc`, falling
back to `currentChatSubject_slot` via the `proposingChatFor:` pattern) —
never from model-supplied input, so a model cannot impersonate another chat.
The delivered text is stamped by *our* code:

```
[from chat 'Alice'] <message text>
```

The receiving model can trust the stamp because only the module writes it.
The **target** is named by exact, case-sensitive match against
`chatDocumentsInRoot` names; on a miss, the tool errors with the list of
available names. Sending to yourself is an error.

### 3.2 Delivery is a real turn

Deliver by materializing the target subject (`chatSubjectFor:` semantics) and
calling its `sendText:` with the stamped message, then wiring the returned
promise exactly as the presenter does: fulfilled → `markComplete`, rejected →
`markError:`, each wrapped in `on: Exception do:` and ending with `nil` (the
callbacks cross the JS bridge: return marshalable values, and keep the
never-raise-inside-`then:` discipline — the psoup bridge failure is
memory-unsafe, see the host design §6).

This buys, for free: the visible user bubble in the target transcript, correct
`apiMessages` bookkeeping, history repair, watchdogs, and the assistant's
reply rendered by `markComplete`. Do **not** append transcript sections
directly — that updates the projection without the session and the two
diverge.

The bubble renders with role `'user'` (any other role renders as "Error" —
`chatBubbleHtml:role:`, `HopscotchForHTML5.ns:6433`). A distinct "peer" bubble
style is a flagged nice-to-have, *not* v1: it would touch
`HopscotchForHTML5.ns` and every projection.

### 3.3 Serialization: one queue per target

Module-level **lazy** state in `AI_IDE_Support` (lazy is mandatory — an eager
slot added to a live module crashes on hot-load):

- `lazy pendingPeerMessages = Map new.`  (Document → List of stamped strings)
- `lazy inboundHopByDoc = Map new.`      (Document → Integer; see §3.4)

`send_to_chat` semantics:

1. Resolve target; validate (exists, not self, hop budget §3.4).
2. If target subject exists and `waiting` is true → append to its queue,
   return `queued behind a running turn (position N)`.
3. Otherwise deliver immediately (§3.2), return `delivered`.

Draining: add one call at the end of
`IDEChatDocumentSubject>>markComplete` (`AI_IDE_Support.ns:817`) and one in
`markError:` (`:838`) — `ide aiSupport drainPeerMessagesFor: document` —
which, if the queue for that doc is non-empty and the subject is not
`waiting`, pops **one** message and delivers it (each delivery's own
`markComplete` drains the next; one-at-a-time keeps turns ordered and
interleaves fairly with the human user). These two one-line touches to
existing methods are the only edits outside new code. Guard the drain body
with `on: Exception do:` so a delivery failure can never break `markComplete`
for the human path.

Queued messages do not survive a page reload (nothing session-side does —
durable history is a standing open item). Acceptable for v1.

### 3.4 Loop prevention

Two AIs must not ping-pong until the API budget burns. Mechanism, all inside
the module (numbers are defaults; make them module-level constants):

- **Hop budget.** Every delivery carries a hop number, tracked
  programmatically (never parsed out of text): a message sent from a turn
  that was itself initiated by a peer delivery at hop *h* gets hop *h+1*;
  human-initiated turns are hop 0. Implementation: before driving a delivered
  turn, record the hop in `inboundHopByDoc` for the target doc; clear it in
  the same promise wiring that calls `markComplete`/`markError:`. When
  `send_to_chat` runs, its sender's current entry (absent → 0) determines the
  outgoing hop. **Refuse when the outgoing hop would exceed 4**, with an
  error telling the model the relay chain is too deep and to summarize for
  the user instead.
- **Per-turn send cap.** A session may `send_to_chat` at most **3** times per
  driving turn (count alongside the hop entry; reset when the turn settles).
  Over cap → error, not queue.
- **Visibility.** Every delivered message is a visible bubble in the target
  doc (automatic, §3.2), and the sender's tool call/result appear in its own
  session history. No hidden channel exists.

### 3.5 System prompt

Append a short paragraph to `newspeakSystemPrompt` (set in
`createFreshSessionFor:`, `AI_IDE_Support.ns:1652`): other AI chat sessions
exist in this IDE; `list_chat_sessions` enumerates them; `send_to_chat`
messages one; an incoming message stamped `[from chat 'X']` is from a peer
session, replies go via `send_to_chat` (never assume the peer sees this
transcript); relay chains are depth-limited, so summarize for the human user
rather than relaying indefinitely.

### 3.6 Tool definitions

Follow the factory pattern of `localFetchTool` (`AI_IDE_Support.ns:2839`) for
schema-string style. Both new factories are focus-parameterized
(`listChatSessionsToolForFocus:`, `sendToChatToolForFocus:`) and are appended
to the array in `toolsWithFocus:` (`AI_IDE_Support.ns:2673`).

- `list_chat_sessions`: no required inputs. Returns one line per chat:
  name, provider/model (via `chatProviderOf:`/`chatModelOf:`,
  `AI_IDE_Support.ns:1676/1679`), state (`no live session` / `idle` /
  `mid-turn` / `N queued`). Handler is synchronous (returns a String).
  Description should note that only Root-registered chats are listed.
- `send_to_chat`: required `chat_name`, `message` (both strings). Returns the
  delivery-status string synchronously; all failures raise (the tool loop
  already converts raises to `is_error` results — `AIAccess.ns:1097`).
  Description must say: fire-and-forget, replies arrive later as
  `[from chat …]` messages, budget limits apply.

## 4. Out of scope (v1)

- Croquet: AI chats under Croquet are a standing open item; under the Croquet
  runtime this module must simply not be reachable (nothing new to do — but
  do not add any code that consults client-divergent state from synced code).
- Non-Root chats (dotted-path `create_chat_document` bindings).
- Durable queues, delivery receipts, broadcast/multicast, external agents
  (that is `/_ns/bus`, host-services step 6).
- Auto-routing a target's reply back to the sender.

## 5. Mandatory process gates (from CLAUDE.md — not optional)

1. Pretty-print every modified `.ns` file, then round-trip-check, from the
   worktree's own `tool/`:
   `./pretty-print.sh ../AI_IDE_Support.ns ../AI_IDE_Support.ns` then
   `./round-trip-check.sh ../AI_IDE_Support.ns`.
2. `./parse-validate.sh ../AI_IDE_Support.ns` (and `../AIAccess.ns` if
   touched) — after pretty-printing.
3. `./run-tests.sh NewspeakTypecheckerTestingConfiguration` (275/275 green as
   of 2026-08-31).
4. No commits. No rebuild — everything here hot-loads (that is *why* the new
   module state must be lazy slots).

Language hazards that will bite here specifically: sends to another subject's
members need `public`; `^` in a stored block raises `CannotReturn` later; use
`isNil ifFalse:`, not `notNil`; initialized slots end in `.`, bare slots take
no period; group lazy slots between classes and methods.

## 6. Verification plan

After the gates, hand to Gilad for IDE testing with this script:

1. Create chats `alpha` and `beta` (different models is a better test).
2. In `alpha`: "Use list_chat_sessions and tell me what you see." Expect
   `beta` listed with provider/model and state, `alpha` absent.
3. In `alpha`: "Ask chat beta what 7*6 is." Expect: tool result `delivered`;
   a `[from chat 'alpha']` user bubble in `beta`; `beta`'s assistant reply
   rendered without `beta` ever being opened first (dormant-wake path).
4. In `beta`: "Reply to alpha with the answer." Expect the answer to arrive
   in `alpha` as `[from chat 'beta'] …`.
5. Busy path: give `beta` a long task, immediately send from `alpha`; expect
   `queued`, then delivery after `beta`'s turn completes.
6. Loop guard: instruct both chats to keep forwarding a message back and
   forth; expect the chain to stop with the depth error within 4 hops, both
   transcripts fully legible.
7. Regression: a plain human turn in each chat still works; Retry/Cancel
   still work; changeset broadcast (`propose_changes` path) unaffected.

## 7. Open decisions (flag for Gilad, don't block on them)

- Cap values (hops 4, sends-per-turn 3) — defaults chosen to be boring.
- Sender-side echo bubble ("→ sent to 'beta': …") — v1 relies on the tool
  call being visible in the sender's own history; a visible echo would need
  an appendSection variant and is deferred.
- A distinct peer bubble style (new role in `chatBubbleHtml:role:`) —
  deferred, touches the shared projection.
