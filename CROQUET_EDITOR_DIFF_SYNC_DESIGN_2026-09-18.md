# Croquet editors: publish edits, never text

Status: APPROVED in outline by Gilad 2026-09-18 ("Go ahead"). Not yet implemented.
Requirement, in his words: **performance must be interactive for any size text.**

## Why

Since 2026-08 every synchronized CodeMirror event that concerns text carries the
editor's FULL text: `codeMirror_change`, and also `codeMirror_accept` and
`codeMirror_cancel`. Croquet drops messages over 16KB, so anything over 8KB takes
the Data-API detour (`nsPublish`): upload, publish a handle, every client
downloads. That is about a second per event, and delivery is strictly FIFO.

The keystroke work of 2026-09-16..18 (keydown filter `6393704`, before-change
folded `176c543`, 80ms coalescing `a5150ac`) cut the NUMBER of events. It could
not touch the cost of EACH. On a class source of a few tens of KB Gilad measured
the result by hand on 2026-09-18: "the lag on a largish piece of text was
enormous", and a toolbar click sat behind the queue long enough for a further
edit to be published to an editor the click then retired (recorded events 11-13
of that session: change, image-button click, change - both changes detoured).

No tuning of rates fixes this. The text has to stop travelling.

## The design

### 1. What is published

One event per flush window (the existing `changeCoalescingWindow`, 80ms, a
throttle), carrying everything the editor did in the window:

    {fid, data: {changes: [ {from, to, text}, ... ],   // CodeMirror change records, in order
                 selection: {anchor, head} | absent,    // the LATEST user selection, if it moved
                 sender, seq}}

- `from`/`to` are `{line, ch}`; `text` is CodeMirror's array of inserted lines.
- **`removed` is NOT sent.** CodeMirror puts the deleted text in the record; for
  select-all-and-paste that is the whole old document. Nothing uses it.
- Records in one event are sequential: each is relative to the document after
  the one before. Receivers apply them in order.
- A keystroke is ~100 bytes at ANY document size. Only a large paste is large,
  once; it takes the detour once, which is unavoidable and acceptable.
- The user's selection rides the same event. Today a user-moved selection is its
  own event, per keystroke, and since `e454bb0` it also forces a flush of the
  pending change - so under real typing the coalescing is largely defeated
  (SUSPECTED from the code and from Gilad's storyline, events 8-10; to be
  measured by the probe before and after). A pure cursor move with no edit
  pending starts the same timer.
- `codeMirror_accept` and `codeMirror_cancel` carry the fragment id only. Their
  responses read the editor, never the event's text.

### 2. The shadow document

Each client keeps, per editor, a SHADOW: the text as the ordered event stream
defines it. Every change event is applied to the shadow in session order, by
every client, the sender's own echoes included. Shadows are therefore identical
on every client by construction - the invariant that full-text `setValue` on
every client used to buy.

- Implementation: a `CodeMirror.Doc` per fragment id, held by the JavaScript
  glue (`nsShadowInit`, `nsShadowApply`, `nsShadowText`, `nsShadowDrop`,
  `nsShadowMatches`). It understands the same positions and `replaceRange`.
  **In the glue, not as alien sends from Newspeak**: 2026-09-18 taught that
  alien call semantics differ between psoup and NS2JS. The glue is generated for
  JS deploys by `tool/mirror-croquet-glue.py`, so both platforms run one copy.
- Keyed by fragment id. Same-kind adoption keeps the id, so the shadow survives
  a re-render with no handoff.
- `createVisual` initializes it from the editor's initial text (always
  overwriting: a freshly built editor's text is its `textSlot`, the same on
  every client at that event position).
- A PROGRAMMATIC change (`text:`, the cancel response, `updateEditedText:` -
  CodeMirror origin `setValue` or untagged) resets the shadow from the visible
  text. These happen inside synchronized responses, at the same event position
  everywhere, so the shadows stay identical.
- Dropped on disposal.

### 3. Lockstep: responses read the shadow

Synchronized responses - the change response (colorizing, `updateEditState`,
live evaluation), accept, evaluate - read the text through `textBeingAccepted`.
The Croquet fragment overrides it: **while a synchronized event is being
dispatched** (`reflecting` is false) it answers the shadow's text; otherwise the
visible editor's. So every client runs every response over the same text, even
while one of them has typed ahead.

### 4. The visible editor

- A client that did not send the event applies the records to its visible
  editor with `replaceRange`, origin `croquet` (not republished). CodeMirror
  keeps that client's own cursor where it belongs; the sender's selection, if
  the event carries one, is then applied as today.
- The SENDER ignores its own echoes in the visible editor: its editor already
  has those edits, or later ones. No `setValue`, no cursor jump, no restore.
  This retires the `ahead` machinery of `a5150ac` (`isBehindLocalEdits:`, the
  save-and-restore in the change handler) and the own-selection-echo skip
  becomes the same rule.
- Concurrent typing in ONE editor: a foreign event that arrives while this
  client has edits pending or in flight is applied to the shadow only, and the
  editor is marked DIRTY. When the client's last own echo is in and nothing is
  pending, a dirty editor whose text differs from the shadow is resynchronized
  from the shadow - locally, no network. All clients always converge on the
  shadow. Intention is not preserved when two people edit the same spot at the
  same instant (no operational transformation); that is no worse than the
  last-writer-wins of today and can be revisited.

### 5. Ordering rules kept from this week

Nothing of an editor's is published while a flush is pending: accept, the
keyboard shortcuts and blur flush first; cancel discards. Keyboard select-all
stays tagged `*selectAll`.

### 6. Compatibility

An event with `textBeingAccepted` is an old full-text change: handled as before
(`setValue`), and the shadow is reset from it. Sessions recorded before this
change replay.

## Verification plan

1. **Latency, the requirement.** `typing-test.js` gains a measurement:
   keystroke-to-arrival on the second client, at 9KB and at ~300KB, reported in
   ms; an assertion that it stays under a bound that does not grow with size;
   and an assertion that no typing event takes the detour. Run BEFORE the
   change too, for the record.
2. **Event economy.** The storyline for N typed characters: count events and
   bytes before and after, with real key events (CDP `Input.dispatchKeyEvent`),
   not `replaceSelection`, so that CodeMirror's `+input` selection path is
   exercised.
3. **Convergence under concurrent typing.** New probe: two clients type into
   one editor at once; both visible editors and both shadows must end equal.
4. **Regression.** `determinism-test.js`, `typing-test.js`, `cm-steps-probe.js`,
   `setup-latejoin-probe.js` (incl. `NAV=home`, `HIDDEN_B=1`), on psoup and on
   the Croquet JS IDE deploy.
5. **Replay.** A late joiner over a session with a few hundred edits of a large
   document: catch-up time, orphan-free, shadow == the others'.

## Implementation order (one step per turn; nothing committed until Gilad has tested)

1. Glue: shadow helpers + `nsCodeMirrorChange` without `removed`; regenerate the JS copy.
2. Probe first: the latency and event-economy measurements, run on today's code.
3. `HopscotchForCroquet.ns` CodeMirrorFragment: publisher (list + selection),
   handler (shadow, visible, dirty/resync), `textBeingAccepted`, accept/cancel
   payloads, programmatic reset, disposal. Remove the `ahead` machinery.
4. Probes 1-5 on psoup, then on JS.
5. Gilad rebuilds (full build: the glue changes) and tests by hand on a large class.

## Out of scope

`TextEditorFragment` (plain text fields) still publishes its full text; its
texts are small. Operational transformation. The 20 msg/s reflector budget is
respected by the single event per window.
