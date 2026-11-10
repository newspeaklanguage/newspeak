# Croquet multiple cursors / presence — state of play, 2026-09-21

Read this first when resuming the presence work. Previous record for the editor
sync it sits on: `SESSION_SUMMARY_2026-09-18_to_19_CROQUET_EDITOR_DIFF_SYNC.md`
and `CROQUET_EDITOR_DIFF_SYNC_DESIGN_2026-09-18.md` (whose message-rate budget is
now obsolete — see below).

## Status: measurement done, NO production code written

Nothing in this work has touched a `.ns` file or the glue. `git status` on
2026-09-21 shows modified `Browsing.ns`, `HopscotchWebIDE.ns`,
`NewspeakTypechecker.ns`, `NewspeakTypecheckerTesting.ns`,
`tool/clean-croquet-sessions.sh` — all of which belong to other work.

What exists is five untracked probes in `croquet-probes/`, each of which records
its own finding in its header comment:

| Probe | Question it settled |
|---|---|
| `remote-cursor-echo-probe.js` | Does drawing a remote cursor echo? No. |
| `remote-cursor-cost-probe.js` | What does drawing one cost? Batching is mandatory. |
| `presence-channel-probe.js` | Is there an ephemeral channel? Yes, dormant. |
| `presence-rate-probe.js` | What is the budget? Volume, not rate. |
| `view-exit-shape-probe.js` | What does view-exit deliver? Records why the view-level approach fails. |

The build was refreshed and the bus and main server restarted on 2026-09-21. The
Croquet reflector was NOT restarted; a session was live.

## The design decision (Gilad, 2026-09-21)

**Participants' presence is exposed when they change focus between fragments —
not continuously.** No pointer-motion streaming, nothing while a participant is
still. This is the load-minimizing choice and it is the right one on the numbers
below: the budget is message COUNT since the last snapshot, and a focus change is
bounded by human navigation rate (a few per minute) rather than by pointer motion
(10Hz+) or by keystrokes.

Open sub-question, deliberately not yet decided — see "What is still open".

## Measured facts

### 1. An ephemeral cross-client channel already exists, dormant

The model subscribes to `onMouseMove`/`onMouseOver`/`onMouseEnter` and their
siblings on the session scope (`out/croquetpsoup.js:2860-2870`). Their handlers
(`:2955-2978`) re-publish to views *without* calling `addEvent`:

    mouseMove(fid){
        console.log('MouseMove ' + fid);
        this.publish(fid, 'model_mouseMove');
    }

`addEvent` (`:2808`) is what pushes onto `newspeakEvents`, "a list of all events
ever sent to the model", which `doPersistTick` (`:2819`) persists. So these events
cross the reflector, reach every client, and leave NOTHING in the persisted
history. Nothing publishes them today — they are leftover "Leaf fragment support".

Measured: 50/50 delivered at 10Hz, persisted list 3 → 3 on both clients, and a
late joiner replayed the same list with zero presence events.

### 2. A view-only publish does NOT cross clients

`theView.publish` on a scope no model subscribes to is delivered locally only —
the sender got its own 50, the peer got 0. There is no free local channel;
everything cross-client goes through the model. Presence must therefore be a model
handler that publishes without `addEvent`, exactly like the mouse family.

### 3. The budget is retained-message VOLUME, not rate

The 20 msg/s figure in `CROQUET_EDITOR_DIFF_SYNC_DESIGN_2026-09-18.md` is
**obsolete**. It came from hosted Croquet, and the hosted backend is gone
(`tool/run-croquet-reflector.sh`: api.croquet.io does not answer, no new API key
obtainable). We self-host permanently, and the self-hosted reflector applies no
per-second limit: 3 senders x 400Hz = 1200 msg/s offered, 100% delivery, no view
detached, session healthy afterwards.

The real wall is in `croquet/packages/reflector/reflector.js:197-198`:

    REQU_SNAPSHOT = 60000   // reflector starts demanding snapshots
    MAX_MESSAGES  = 100000  // SEND returns without delivering: "Cannot buffer
                            // more messages. Need snapshot." -- wedged session

Counted *since the last snapshot*. Presence therefore costs snapshot pressure
proportional to message COUNT. Three clients streaming at 10Hz is 30/s: the
snapshot-request threshold in ~33 min of continuous movement, the hard wall in
~55. This is the measurement behind the focus-change decision.

### 4. Today's cursor sharing is on the PERSISTED stream

`codeMirror_beforeSelectionChange` is handled at `:3041` via `publishEventAndData`
(`:2832`), which calls `addEvent`. So every selection move a user makes today is
retained in `newspeakEvents` and persisted forever.

This cuts in our favour: routing caret information onto the ephemeral channel does
not add retained volume, it REMOVES volume that exists today.

Also: a remote selection is currently applied as the receiving client's OWN
selection (`HopscotchForCroquet.ns:628`) — which is why everyone shares one cursor.
Multiple cursors means removing that, which also retires much of the guard logic
around not clobbering a local user who has moved on.

### 5. Rendering

- CodeMirror is 5.45.0, so `markText` (ranges) + `setBookmark` (collapsed caret
  carrying a DOM widget). No CM6 decorations.
- **Decorations do not echo.** Drawing and clearing published nothing, with
  working positive controls in the same probe (a user edit published
  `codeMirror_change`; a user selection move with no edit published
  `codeMirror_beforeSelectionChange`). No `croquetOrigin` extension needed.
- **Marks track edits themselves** — a bookmark at ch 4 moved to ch 13 after a
  9-char insert before it. No per-keystroke recomputation.
- **Batching is mandatory, not an optimization.** Un-batched: 41.2ms per
  create+clear cycle on a FORTY-line document. Inside one `cm.operation()`:
  1.6ms. Wrap all cursor updates for one arriving event in a single operation.
- Residual cost is the known virtualization bug, not cursors: the probe reports
  3000 of 3000 lines rendered. A cursor move costs 2.1ms at 40 lines, 6.3ms at
  3000.
- **Presence must be drawn in raw DOM, outside the presenter tree.** Remote
  presence is client-local state, and `chat-id-divergence-probe.js` exists to
  assert that a synchronized fragment tree does not change shape with
  client-local state — fragment ids are minted from a per-type counter and ARE
  the Croquet event addresses. Rendering presence through Hopscotch presenters
  would diverge the session. `markText`/`setBookmark` already satisfy this.

### 6. Cleanup on departure: view-exit

The design wants free cleanup — when a client leaves, its cursor disappears
everywhere, with no heartbeat and no timeout:

    viewExited(viewId){ this.publish('nspresence_', 'presence_gone', viewId); }

A **view-level** subscription to view-join/view-exit never fires: the Croquet
client publishes them with `publishFromModelOnly`, so only a MODEL handler sees
them. The probe's control caught this — C joined and A recorded zero view-joins —
so the equally empty view-exit list was correctly read as proving nothing rather
than as "view-exit does not fire".

Settled by reading the client instead (`out/croquet.min.js`, `generateJoinExit`):

    const r = t => { const {data: e, loc: s} = this.views[t];
                     if (!e) return t;                        // bare viewId
                     const n = {viewId: t, viewData: e};
                     if (s) n.location = s; return n; };

So the payload is the bare viewId STRING unless the client supplied `viewData` at
join. Neither platform does — `meta/croquet-post.js:1651` and
`tool/croquet-glue-js/startup.js:28` both call `Session.join` without it — so a
handler taking a string is correct TODAY. It is conditional, though, and presence
is exactly the feature that would tempt someone to start passing a display name or
colour as viewData, at which point the payload silently becomes an object. **The
presence handler must accept both shapes.**

Verifying against a real `viewExited` model handler needs a rebuild; at that point
the cheap check is to log the payload from `viewExited` directly.

## Scope: BOTH layers (Gilad, 2026-09-21)

(a) **Fragment-level.** Which fragment each participant is focused in, marked on
    that fragment. One message per focus change.
(b) **Per-caret cursors inside a shared editor.** `setBookmark` for the caret,
    `markText` for a selection range.

They stack: (a) is the outer layer, (b) the inner one, and they share one record
per participant — a participant has AT MOST ONE caret at a time, and a focus
change moves it rather than adding another.

(b) does not cost what it appears to: the caret is already on the wire today
(section 4), on the *persisted* stream. Moving it to the ephemeral channel is
strictly less retained traffic than the status quo.

### Protocol

One ephemeral broadcast channel, modelled exactly on the dormant mouse family —
the model handler republishes without `addEvent`, so nothing is retained:

    this.subscribe('nspresence_', 'presence_post', this.presence_post);
    this.subscribe(this.sessionId, 'view-exit', this.viewExited);

    presence_post(p){ this.publish('nspresence_', 'presence_changed', p); }
    viewExited(p){ this.publish('nspresence_', 'presence_gone',
                                (p && typeof p === 'object') ? p.viewId : p); }

Payload: `{viewId, fid, anchor: {line, ch}, head: {line, ch}}`. `fid` carries
layer (a); anchor/head carry layer (b).

`nsPublish` leaves this payload untouched — it is not a `{fid, data}` envelope, so
neither the large-payload detour nor the label machinery fires. Presence events
are never recorded, so `replayEvents` never sees them and a late joiner replays
none.

### Load discipline

- **Focus change: published immediately.** Rare, bounded by human navigation.
- **Caret movement: DEBOUNCED, not throttled.** The caret is published ~300ms
  after the last movement, i.e. only once the caret comes to REST. Continuous
  typing publishes nothing; a pause publishes one event. This is the measured
  "dwell/attention" rule — traffic proportional to pauses, not keystrokes.
- Nothing is published when the record is unchanged.
- A focus change cancels a pending caret debounce and folds into one event.

### Consequence for the persisted stream

Carets stop riding the synchronized stream entirely:

- `codeMirror_beforeSelectionChange` is no longer published.
- The edit event no longer carries a `selection` field.
- A remote selection is no longer applied as the receiving client's own
  (`HopscotchForCroquet.ns:628`, and the selection application inside
  `nsApplyEdits`). The `model_codeMirror_beforeSelectionChange` SUBSCRIPTION stays
  — an old session replaying a recorded selection event must still find a
  subscriber, or the late-join probe's "no subscriber ... skipped" warning
  returns — but the handler ignores the selection.

Safe for lockstep by the argument already recorded at `:627`: this path sets the
visible editor's selection and nothing else — no response, no render, no ids.

### The selection is NOT purely presentational (found 2026-09-22, by regression)

`croquet-probes/typing-test.js` failed its syncRandom phase after the change
above: A evaluated, B did not (`window.rnd` was `undefined` on B). Cause:

    Debugging.ns:133  evaluateResponse
        | src <String> ::= ed editor getSelection. |

"Evaluate Selection" is a SYNCHRONIZED action that runs on every client, and
each client reads its OWN visible editor's selection to decide what to evaluate.
That worked only because a remote selection was adopted as the receiving
client's own. So the one-shared-cursor behaviour was load-bearing, and the note
at `HopscotchForCroquet.ns:627` ("this handler does nothing but set the editor's
selection: no response, no render, no ids") was right about lockstep of ids and
wrong about consequences: a LATER synchronized command reads that selection.

`nsPatchSelectAll` exists for the same reason — it was added (2026-09-17) so that
Cmd-A would publish, precisely so a following Evaluate Selection ran everywhere.

Same shape at `Debugging.ns:292` (pretty-print selection) and `Documents.ns:798`.

**CORRECTION (2026-09-22): publishing the selection on blur does not work, and
the "costs less than before" claim below is wrong.**

The first attempt published the selection of record on blur and before a keydown
action, on the theory that a button click takes focus first. Measured, that
trigger never fires: `evaluate-selection-probe.js` reports `cm.state.focused`
false with a blur handler registered, `nsCurrentSelection` called 0 times, and
`newspeakEvents` flat across the blur. CodeMirror only runs its blur handler if
it believed itself focused, and under a synthetic click it does not. The existing
text-flush on blur rests on the same assumption; it survives only because the
80ms change timer flushes anyway.

So the selection of record needs a trigger that cannot be skipped. It goes back
onto the coalescing window that edits already use: the selection rides the edit
event when there are edits, and a selection-only window publishes a selection
event, exactly as before 2026-09-21. Only the RECEIVING side changes -- the
selection is stored as the deterministic selection of record and is never applied
to the visible editor, which is what keeps cursors multiple.

Consequence for the accounting: **multiple cursors do not reduce recorded volume.
They cost what the old shared cursor cost.** What presence buys is per-caret
fidelity at no recorded cost (continuous caret motion stays ephemeral and
debounced); what the recorded stream still carries is one coalesced selection per
window in which the selection moved -- the pre-existing rate.

**Fix: a selection of record, exactly parallel to the shadow text.** The visible
editor's selection stays the user's own (cursors stay multiple); a DETERMINISTIC
selection per editor is what synchronized commands read:

- the glue keeps a selection beside each shadow; `nsShadowSelText(fid)` answers
  the selected text computed from the SHADOW document, so every client answers
  the same string at the same event position;
- the selection is published only when a command might be about to read it --
  on blur (a button click takes focus first, which is what the existing
  blur-flush already relies on) and before a keydown action -- NOT on every
  caret move, so the volume win is kept;
- the `model_codeMirror_beforeSelectionChange` handler stores it into that
  deterministic slot on every client and NEVER touches the visible editor;
- `selectedTextBeingAccepted` joins `textBeingAccepted` as the thing a
  synchronized response reads; base answers `editor getSelection`, the Croquet
  subclass answers the shadow's.

### Rendering (in the GLUE, not Newspeak)

Presence is drawn entirely in JavaScript, which is what keeps it out of the
presenter tree and away from fragment-id minting. Newspeak's only job is to
report focus and caret, and to keep an editor registry current.

- `nsEditors`: Map fid -> visible `cm`. No fragment id reaches the DOM, so the
  glue cannot find an editor on its own. Registered in `createVisual` and in
  `updateVisualsFromSameKind:` (after adoption, where the lineage keeps the id but
  gets a NEW cm — registering only at shadow creation would leave a stale cm
  here), dropped in `noticeDisposal` (unlike the shadow, which is deliberately
  kept).
- All cursor updates for one arriving event go inside a single `cm.operation()`
  — measured mandatory: 41.2ms -> 1.6ms.
- Colour per viewId by hash. Client-local, so it does not affect determinism.
- The glue injects its own `<style>` element.

### Deliberately NOT in this change

Page-level presence ("Alice is on the Browsing page") needs hooks in the shell and
navigation, a much larger surface than editor focus. Layer (a) here is at editor
granularity, which is where focus is both cheap and well defined. Page-level is a
follow-up.

## Next steps, in order

1. Settle the granularity question above.
2. Add the presence model handler + `viewExited` (accepting both payload shapes),
   publishing without `addEvent`. Glue change => `run.sh syntax-check.js <abs
   path>`, `python3 tool/mirror-croquet-glue.py`, gate `DeploymentManager.ns`
   (parse-validate FIRST), `python3 scratch/splice_test_glue.py`.
3. Log the payload from the real `viewExited` on the first build that has it —
   the one thing section 6 could not settle without a rebuild.
4. Remove the remote-selection-as-own-selection behaviour
   (`HopscotchForCroquet.ns:628`) and the guard logic it drags along.
5. Draw presence in raw DOM, all updates for one arriving event inside a single
   `cm.operation()`.
6. A two-client presence probe: B's cursor appears on A, moves with A's edits,
   and vanishes when B leaves — with a positive control, per the standing rule
   that a probe without a negative control proves nothing.

## Operating notes

- Probes: run in the background with output redirected to `scratch/x.out`, then
  wait with `until grep -q "passed,\|BAIL\|Error:" scratch/x.out; do sleep 5; done`.
  Never run two probes at once. `croquet-probes/run.sh probe-browsers.js --kill`
  also stops leftover drivers (a killed turn leaves one holding port 8098).
- Bridge: reply in text first after a killed turn; one long step per turn.
