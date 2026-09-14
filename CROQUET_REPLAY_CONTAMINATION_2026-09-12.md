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

## 2026-09-13: two replay-ORDERING defects in the glue (croquet-post.js), found with the fuller recipe

Gilad's fresh session on the fixed build misbehaved again for a late joiner:
"holding early answer" for a completion, then orphaned keystrokes for
nscodemirror_/21. The recipe had three ingredients the first probe lacked -
the chat opened from a CLASS PRESENTER's brain button (embedded region, focus
captured), TOOL CALLS from it, and keystrokes while a reply was pending. With
those in the probe (FROM_CLASS=1, TOOL_TURNS=1, draft typed while waiting) the
joiner diverged: it minted its own coordination key for turn 2 and, in one
run, got itself elected and SENT A NEW REQUEST to the agent while replaying.

Cause (the request-body diff the probe now prints): the joiner's turn-2
request had 4 messages where the original's had 5 - the turn-1 text reply
was missing. On the original: tool_use answer (event 22) → tool runs → tool
result sent → text answer (event 23) → user types message 2. On the joiner
the tool round is asynchronous, so when event 23 came up the joiner had not
yet subscribed for it; the replay HELD it (waitBudget 0 for coordinated
answers, a choice made when unrequested answers caused cascading stalls)
and dispatched the message-2 keystrokes and Send, whose history lacked the
reply. Different body → different digest → a resource nobody recorded.

Fixes in `meta/croquet-post.js` `replayEvents` (uncommitted; spliced into
out/croquetpsoup-test.js only):
1. A coordinated answer waits up to 10s for its requester before being held.
   "Absent now" is not "never coming": a completion's request is issued by
   the CONTINUATION of the previous answer. The bound only bites for an answer
   this client will truly never ask for, itself a bug on a correct app.
2. `nsReplayPace`: after each replayed event, one macrotask + one animation
   frame, so the asynchronous fallout of an event settles before the next
   recorded event is dispatched, as real time separated them live.

Result: 9/9 with the full recipe - no held answers, exactly 4 agent
requests, registry identical on all 9 kinds (buttons and image buttons
included: the earlier "button numbering" discrepancy did not recur), joiner
recorded nothing. Control without the glue change: 7/9 (registry drift) or
5/9 (joiner re-issued a request). The glue also carries another session's
uncommitted ledger work; stage selectively.

Principle restated: application code is untouched. Both defects were the
replay running AHEAD of the application's in-flight asynchronous work.

## 2026-09-13 (later): tool results are now SHARED, not computed per client

With both glue fixes live, Gilad's next session still lost its Safari joiner
at an editor ordinal (/21). The census showed why: Safari held a coordination
key Chrome never had (perform.744686816.1). The divergence was a TOOL RESULT:
an evaluate the agent ran had printed `theModel.newspeakEvents.length` - a
value read from Croquet's model, not from the replicated image. A replaying
joiner's model already holds the whole history, so it answered 1081 where the
original answered 267; each client put its own result into the history, the
request bodies differed, and so did every later key and render.

Determinism itself held: a tool that reads only image state answers the same
everywhere (the probe's current_focus rounds proved it). But `evaluate` runs
arbitrary code, and tools that fetch, read the clock or the browser cannot
promise it. So the platform now shares tool results the way it shares fetch
results, transparently to the IDE and any future tool user:

- `Host.Performer>>shareText:via:` (psoup Host.ns): for a computation whose
  EFFECTS must happen on every participant but whose RESULT the session must
  agree on. Plain host: run op, answer its text.
- `HostForCroquet` override + `coordinatedShare:via:`: every client runs op
  here and now (effects), then its text goes through the same election as a
  performed request (`coordinatedText:` under `performKeyFor:`); the elected
  client's text is recorded and every client - and every replaying joiner -
  fulfils with the recording, its own discarded.
- `AIAccess Session>>toolResultFor:handlerValue:isError:` now answers a
  PROMISE of the provider result: the normalized text first goes through
  `shareToolText:forCall:` (key `tool <tool_use id>`, shared already since it
  came from the model). Degenerate with no host / no seam / breakage: local
  text. All call sites already sat inside JS promises.
- Probe: TOOL=evaluate (default) makes the agent's tool_use an evaluate that
  prints the session's event count - client-local by construction - and
  checks the joiner's transcript shows the ORIGINAL's number.

RESULT (probe, TOOL=evaluate, FROM_CLASS, TOOL_TURNS, delayed replies):
9/10 with the only miss a DOM observable (CodeMirror virtualizes lines;
since replaced by an A-vs-B rendering comparison). Zero sharing fallbacks;
A mints a `perform.` key per tool round and B holds the identical seven
keys - the turn-2 completion key digests the whole body, tool result
included, so equal keys prove B's history carries A's text; no held answers,
no extra agent requests, registry identical on 9 kinds, B recorded nothing.
Found on the way: the Session sent `performer`, BusProvider's accessor, not
visible from Session - a silent MNU fallback; the module accessor is
`hostPerformer`. The fallback now prints a 'shareToolText:' console line.

Not covered yet: media in tool results (screenshots) stay local; a client
whose local tool run failed adopts the recording silently (a console line
would be better).

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

## 2026-09-13 (later still): a failed coordinated fetch is an ANSWER, not a vacancy

Found with the probe's `FAIL_TURN=1` (the mock provider answers a turn's text
request with HTTP 500 once; the user clicks Retry). Under the old semantics a
failure DELETED the model's entry "so a retry can re-elect" and the failure
broadcast was unrecorded. A late joiner replaying the Send then found no entry
for the first attempt's key (`fetch.<digest>.1`), was elected, and POSTed the
original request to the provider itself: a call the original never made, a
reply the original never saw (the mock's third text reply against the
original's first), no Retry row (its fetch had succeeded) so the replayed
Retry click orphaned, the retry's recorded answer (`.2`) held forever, and
every later key diverged (6 of 13 checks failed).

Fix: record failures the way loaded answers are recorded.

- Model (`meta/croquet-post.js`, and the embedded copy in
  `DeploymentManager.ns`): `coordinatedFetch_failed` keeps the entry as
  `{status: 'failed', reason}` and `publishEventAndData`s the failed event; a
  request against a failed entry gets a recorded repeat failure (as a loaded
  entry gets a repeat loaded); an await against one gets an unrecorded
  `model_coordinatedFetch_awaitedFailure` (as `awaited`). Nothing re-elects
  for the same key: every live caller reaches the coordinator through
  `HostForCroquet`, which mints a key per ATTEMPT (`sharingKeyFor:` /
  `performKeyFor:` ordinals), so a retry is a new request under a new key. No
  raw-key caller that retried under the same key remains (Documents go through
  the host fetcher).
- Client (`HopscotchForCroquet.ns` `subscribeCoordinatedFetchEventsFor:`):
  the failed handler is subscribed through `subscribeFragment:` (counted, the
  event is now in the history); `awaitedFailure` through `nsSubscribe`
  (uncounted). The replay loop's 10s requester wait and the held-answer stash
  already cover the new event: they key on the `nscoordfetch_` scope.

Result (TEST artifacts, `NS_SUFFIX=-TEST NS_PAGE=croquetpsoup-test.html
FAIL_TURN=1 PROVIDER=openai-compat`): 13/13. Storyline: the completion's
failure is event 35, the Retry click 36, the retry's answer 37; the joiner
replays with 0 orphans and 0 held answers (so it showed the Retry row and the
click found its button), the provider saw exactly 5 requests, and every answer
recorded after the join repeats a known key (the model re-records answers to
late requests by design - "no new recorded events after join" is the WRONG
observable; the probe now checks for NEW KEYS).

Side effect worth knowing: model-discovery failures (Anthropic 401 without a
key, Ollama's port refusing) are now in the history too (events 1 and 5 of the
storyline), so a joiner meets the recorded failure rather than trying its own
discovery - consistent with everything else coordinated.

Also found on the way, not Croquet: a chat embedded in a class presenter's
region (inline `IDEChatSubject`) had a no-op applied hook, so a user's Apply
click never queued the "user applied your proposed changeset" notice for the
model (only the choke point's "codebase changed" line). Fixed in
`AI_IDE_Support.ns` `changesetSubjectFor:`; the probe's `NOTICE=1` recipe
checks both notices ride turn 2's first request.

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
