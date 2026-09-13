# Late-join replay contamination: programmatic editor changes were published

**Status 2026-09-12:** root cause found, fix in `HopscotchForCroquet.ns`
(uncommitted), headless reproduction `croquet-probes/setup-latejoin-probe.js`
8/8 PASS against a TEST vfuel built from the working tree, including "the
joiner recorded nothing of its own" (A and B both end at 23 events; the two
beyond A's pre-join reading were A's own late events). The
`updateEditedText:` flag fix below is also applied live in Gilad's IDE image
(changeset cs1) for interactive testing of the paste case.

## Symptom

A late joiner (Brave) of Gilad's bus-chat session stalled early:
`Croquet replay: no subscriber for key "nscodemirror_/2..." after 15000ms`,
then more of the same for `/24`, each costing 15s; thousands of events to go.
The original client (Chrome) was fine, as was a Safari client that joined
earlier.

## Diagnosis trail

- Fragment ids are per-client ordinals per kind (`newIdFor:`), never reset.
  Events address the ORIGINATING client's ordinal; a joiner only matches if it
  constructs the same fragments in the same order.
- Censuses from both clients showed `/2` dead on both at the end, yet Chrome
  had published a setValue-shaped pair on `/2` long after the setup form that
  owned it was retired. And at replay position 562 Brave had minted editors
  Chrome had not: the ordinals had diverged.
- The probe, driving the chat SETUP FORM through the real UI (toolbar brain
  button, provider picker, Bus Agent, typing the agent name, Start Chat) plus
  two bus exchanges with the probe acting as the agent (30s delayed replies),
  reproduced it: the joiner caught up "orphan-free" but with 48 recorded
  events of its own beyond the original's 81, five extra editors, and a
  reflector warning about a 4KB payload it sent during replay.

## Root cause

`HopscotchForCroquet CodeMirrorFragment` published EVERY CodeMirror change,
including programmatic ones (origin `setValue`), by design: the local change
response (`changeResponse`, `updateEditState`) ran only when the event came
back from the model, so a setValue that was not published would have had no
response (`isSyncOrigin:`'s old comment: "parts of the document-update
pipeline ride on them").

Consequences:
1. Every client re-renders the same way and published the same setValue:
   each programmatic change was multiplied by the number of clients, and each
   echo ran each client's change response again.
2. A late joiner, re-rendering as it replayed, published its OWN copies on top
   of the recorded ones. Those extra echoes drove extra change responses and
   re-renders on the joiner alone, minting fragment ordinals the original never
   had. From then on every recorded keystroke addressed an editor the joiner
   had numbered differently: 15s orphan waits, one per event.

The chat page made this visible because each exchange re-renders its amplets
several times (phase changes), minting ~6 editor ordinals per turn, and the
old published pairs were 4 events per setValue.

## Fix

`isUserOrigin:` in the Croquet `CodeMirrorFragment`: the change, beforeChange
AND selection publishers publish only USER-originated signals (CodeMirror tags
them `+input`, `+delete`, `paste`, `cut`, `undo`, `*mouse`, `+move`, ...).
Programmatic signals (`setValue`, `croquet`, or untagged) run the base
response locally at once. The existing `reflecting` flag guards the
application path: it is false while a synchronized event is being applied,
and those handlers run the base response themselves.

Principle: a programmatic change is a deterministic consequence of replicated
state that every client produces for itself, in lockstep; it must not enter
the stream. Only user edits need telling the others about. Application code
is untouched.

Result (probe): the recorded storyline shrank from 81 events to 21 — the
user's clicks and keystrokes plus the two coordinated answers; the joiner
caught up in 33s, zero orphans, CodeMirror census identical to the original,
agent saw exactly two requests.

Caveat: a setValue that happens on ONE client only (streaming chunks on the
elected initiator, when streaming exists) no longer propagates via editor
events. It must not: it belongs in a recorded coordinated delivery that every
client's continuation receives at the same stream position.

## Also found

- Croquet `updateEditedText:` leaves `lastChangeWasSynthetic` raised when the
  adopted text is unchanged (it skips the setValue that would consume it), so
  the FIRST real change after a re-render is swallowed as synthetic and the
  editor never enters edit state (Ctrl+Enter ignored). A human's second
  keystroke clears it; a one-chunk programmatic insert does not. This is
  also why PASTING into a re-rendered editor showed no accept/cancel bar.
  FIXED: `updateEditedText:` lowers the flag when it skips the setValue.
- The waiting indicator (`liveLabel:every:`) is a local label update on a
  setInterval; it publishes nothing and is innocent.
- Probe lesson: `cm.setValue` in a probe is now a PROGRAMMATIC change and is
  not published; type with CDP `Input.insertText` (harness exposes `send`).

## Files

- `HopscotchForCroquet.ns` — `respondToChange:`, `respondToBeforeChange:`,
  `respondToBeforeSelectionChange:`, new `isUserOrigin:`, `isSyncOrigin:` comment.
- `croquet-probes/setup-latejoin-probe.js` (new), `croquet-probes/harness.js`
  (`send` exposed).
- `tool/build-croquet-test-vfuel.sh` — builds ONLY
  `out/CroquetHopscotchWebIDE-TEST.vfuel` from the working tree (psoup sources
  first, repo over them, stamped BuildInfo marked TEST).

Run: `sh tool/build-croquet-test-vfuel.sh` then
`NS_SUFFIX=-TEST <emsdk node 22> croquet-probes/setup-latejoin-probe.js`.
