# Multiple simultaneously-active AI sessions — milestone plan

Recovered 2026-06-27 from the session transcript (originally drafted 2026-06-18/19,
then shelved while robustness/perf work landed). Design decisions confirmed still
operative by Gilad on 2026-06-27.

## Goal
Remove the "one active chat" constraint so multiple AI **sessions** run
concurrently: several chat docs transcluded in one document, different parts of the
IDE driving different sessions on different problems, one AI reviewing another's
work. Chats are already asynchronous, so they can run in parallel — the blocker is
shared singleton/module-global state.

## Confirmed design decisions
- **Isolation = hybrid** — per-chat focus + per-chat changeset id-space; object
  registry stays shared.
- **New chat = first-class Root `ChatDocument`** (persists, shows in picker),
  created with a provider/model, without disturbing other open chats.
- **Change notification = inject notice into every *other* open chat's next-turn
  context** + handle staleness.
- **Changeset staleness = leave as-is** (diffs don't live-update).

## Prerequisite robustness/perf work — DONE
- Document reactivity (per-presentation `contentsChanged`, retire/teardown).
- Live-view focus fix (DOM-staleness gate) — 2026-06-25.
- Fan-out collapse (obsolete TwoViewEditorPresenters leave the duct) — 2026-06-26.

## Milestones
- **M0 — DONE & committed** (user-verified). New Chat + in-place chat switcher on
  the chat presenter. (`chatDocumentsInRoot`, `chatSwitchMenuActions`,
  `openNewChatSetup`, `makeCurrentChat:` already exist in `AI_IDE_Support.ns`.)
- **M1 — DONE (2026-06-27)** — Decouple from the single-active-chat singleton;
  chats coexist & switchable. `sharedChatSubject_slot` → `currentChatSubject_slot`
  (the *targeted* chat, not the only one); `chatSubjectFor:` no longer retargets on
  render; `makeCurrentChat:`/`startChat`/the switchers do the deliberate retarget;
  `ensureSharedChat` restores the last chat from the localStorage hint. Detail below.
- **M1.5 — DONE (2026-06-27)** — Per-region brain chat. The brain-button inline
  region used to render the global `ensureSharedChat`, so switching one switched
  them all. Now `ProgrammingPresenter` has a mutable lazy slot
  `lazy public regionChat ::= ide aiSupport ensureSharedChat` (defaults to global
  current only when a region is opened); `installAIChatExpanded:`/
  `aiChatExpandedColumn:` render `regionChat`; the embedded `IDEChatPresenter` gets
  an injected `onSwitchHandler` so its switcher retargets THIS region locally;
  `updateVisualsFromSameKind:` carries `regionChat` across refresh. New-Chat left
  as-is (navigates to setup, becomes global current). Each brain region is now an
  independent session.
- **M2a — Per-chat focus — DONE (2026-06-27).** New `ChatFocus` class (block +
  validator + docLabel + `description`); each chat owns one, threaded
  `chatSubjectFor:` → `createFreshSessionFor:focus:` → `toolsForProvider:focus:`
  (so `current_focus` reads the calling session's focus) and onto the
  `IDEChatDocumentSubject` (so it can be written). `captureFocusInto:` snapshots the
  module-global staged focus into a chat. Focus follows navigation via
  `ProgrammingPresenter>>noticeExposure`: when a presenter with an open brain region
  is **exposed** (navigated-to/shown — nesting-agnostic, fires on exposure NOT
  repaint), it re-asserts its `focusAction_slot` and captures into its `regionChat`.
  This beat two dead ends: click-only capture (didn't follow navigation) and
  capture-on-every-render (a live workspace pane repainted constantly and dominated).
  The module global `currentFocusBlock`/`Validator` stay only as the brain-click
  staging source. `currentFocusDescription`/`computeFocusOnly` now dead (left for
  cleanup).
- **M2b — Per-chat changeset routing — DONE (2026-06-27).** Reframed: the id-space
  is already collision-safe (global `nextChangesetIdNum` → unique ids; global
  `proposedChangesets` keyed by them), so the real bug was *attribution* — a
  changeset proposed during one session was enqueued onto whatever chat was
  CURRENT. Fix: `ChatFocus` carries its `chatDoc`; `proposeChangesToolForFocus:`
  (per-session, like `current_focus`) enqueues via `proposingChatFor: focus` →
  `focus chatDoc chatSubjectSlot` instead of `currentChatSubject_slot`.
  `enqueuePendingChangesetId:id forChat:` now takes the target chat. Id-space and
  object registry stay shared (hybrid).
- **M3 — Broadcast system changes to all *other* open chats** (inject notice +
  handle staleness). Previously deferred.

---

## M1 detail (re-grounded against current code, 2026-06-27)

### Current mechanism (the singleton)
`AI_IDE_Support.ns`:
- `sharedChatSubject_slot` (decl ~line 121) — THE one chat subject the brain
  button / inline region / toolbar target.
- Writers that clobber it: ~304, ~315, ~1517 (building/visiting a chat-doc subject
  sets `sharedChatSubject_slot:: doc chatSubject` — so opening a second chat
  overwrites the first as "active").
- `ensureSharedChat` (~1432) — returns cached `sharedChatSubject_slot` or builds a
  default; the inline chat region always renders this.
- Readers: `activeChatDocPrefix` (~1376), `chatLauncher` (~1396, uses slot ~1421),
  `enqueuePendingChangesetId:` (~1985, uses slot ~1996).

### M1 changes
1. Introduce `openChats` — `Map[String → IDEChatDocumentSubject]` of chats with a
   live Session (keyed by doc name).
2. Repurpose the singleton as `currentChatSubject_slot` — the chat the brain/toolbar
   currently *targets* (most-recently-focused), **no longer "the only one"**.
3. On chat-subject build (the ~304/~315/~1517 writes), **register** the subject in
   `openChats` and set `currentChatSubject_slot`; keep writing
   `ns_ai_active_chat_doc` localStorage but treat it only as the *default-on-reload*
   hint. **Deregister** on doc close/delete (prune entries whose Session is gone).
4. Point the readers (`activeChatDocPrefix`, `chatLauncher`, `ensureSharedChat`,
   `enqueuePendingChangesetId:`) at `currentChatSubject_slot` — mechanical;
   single-chat behaviour unchanged.
5. Brain button (`Browsing.ns` ~6549) keeps targeting `currentChatSubject_slot`;
   switching the picker updates the target but leaves other chats live.

NOTE (2026-06-27): the original plan had a UI step here ("add a chat switcher +
New chat… to the inline presenter"). That is **already done by M0** — the inline
`IDEChatPresenter` (~577) renders New Chat + `chatSwitcher` + Clear (~640) and the
chat-doc `ChatControlsPresenter` (~671) has New Chat + switcher (~681). So M1 is
**pure backend decoupling** (steps 1–4 + the brain-button reader); no new UI. The
existing switcher/New-Chat currently clobber the singleton (`makeCurrentChat:`,
`startChat` overwrite `sharedChatSubject_slot`); after M1 they leave all chats live.

### Out of scope for M1 (lands in M2/M3)
- Per-session focus / tool state (still module-global after M1 — same single-chat
  hazard as today; acceptable, deferred to M2).
- Cross-chat change notification (M3).

### Verification (per-milestone, in the running IDE, hot-load)
Open two chat docs; confirm both stay live (each resumes its own conversation),
the switcher targets without killing the other, a new chat from a presenter doesn't
disturb existing ones, and single-chat behaviour is unchanged.
