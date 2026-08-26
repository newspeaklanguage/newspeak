# Determinism for Newspeak-on-Croquet: timers, randomness, time, transclusion

2026-08-23. How Croquet's own client achieves replicated determinism, why our
architecture cannot use it directly, and concrete designs for covering the
Newspeak end. Companion to CROQUET_NOTES.md (Known gaps).

STATUS (2026-08-25): WebTransclusion (now via the domain-neutral
coordinatedFetch primitive - see implementation notes), Timer and syncRandom
are IMPLEMENTED and verified headlessly on BOTH platforms - psoup
(croquetpsoup-test.html + CroquetHopscotchWebIDE-TEST.vfuel) and NS2JS
(CroquetJSIDE-TEST.*, freshly deployed through the packager from these
sources). Six suites, each ALL-PASS on fresh sessions after the refactor:
election + dual install + late-joiner-from-stored-bytes; idempotent start +
teatime-paced recorded ticks + model self-stop; identical PRNG streams at JS
and NS level (scratchpad croquet-{transclusion,timer,random}-test.js and
croquet-js-* variants). Typechecker suite green. syncTime remains DESIGN
ONLY - see below, it needs an event-envelope change. Edits: Documents.ns (fetch seam),
HopscotchForHTML5.ns (documentZipNamed: base + TimerFragment repair),
HopscotchForCroquet.ns (synchronized overrides + syncRandom accessor),
primordialsoup/meta/croquet-post.js and its embedded mirror in
DeploymentManager.ns (model transclusion election + timer future-ticks +
nsSyncRandom). Verification artifacts staged additively as out/*-TEST.* so
the live session on the stock files was never touched; the stock
out/croquetpsoup.js and out/*.vfuel still predate these changes and need a
normal rebuild once no session is live.

Build gotcha rediscovered the hard way: when assembling a compile directory
by hand, copy psoup's newspeak/*.ns FIRST and the repo's *.ns AFTER -
tool/build.sh's order. 29 filenames exist in BOTH trees (including
JavascriptGeneration.ns, NewspeakCompilation.ns, AliensForJS.ns), and the
psoup copies are stale; with the wrong precedence the deploy packager dies
with 'Failed to process an intrinsic ... Factory globalAt:' because the
Sep-2025 JavascriptGeneration lacks vocabulary the stale AliensForJS uses.

## What the Croquet client does (teatime/src, checked out at ../croquet)

- **Randomness** (`vm.js:438-496, 1414-1424`): each session VM owns a
  SeedRandom PRNG **seeded with the session id** and its state is serialized
  into every snapshot (late joiners restore mid-stream). `Math.random` is
  patched globally to route to `CurrentVM.random()`, which THROWS when called
  outside model simulation - randomness is replicated because model code runs
  identically everywhere, and it is fenced so nothing else can consume it.
- **Time** (`model.js:675`): model `now()` is teatime - advanced only by
  reflector heartbeat, frozen during a step, identical on every client. Views
  get `externalNow`/`extrapolatedNow` for display only.
- **Timers** (`vm.js:760-800`): `model.future(ms).method(args)` inserts a
  message into the SAME priority queue as reflector messages, with a
  deterministic interleave (future messages get even sequence numbers,
  reflector messages odd). Repetition via `futureExecAndRepeat`; `cancelFuture`
  removes by handle, method, or wholesale. Pending future messages ride in the
  snapshot, so late joiners continue schedules seamlessly.

## Why we cannot use it directly

Our state lives in the Newspeak heap, per client, synchronized by replaying
user events in reflector order; the Croquet model is an event log plus relay
(paper section 3.1). Model-side determinism therefore does not protect us: our
mutations run view-side. The invariant we must preserve instead is:

    heap state = replay(recorded events)

so every nondeterministic input must be (1) routed through the reflector as a
RECORDED event, (2) derived deterministically from recorded events, or
(3) explicitly non-synced (NonSyncingPresenter territory).

## TimerFragment: model-driven ticks

Today (`HopscotchForHTML5.ns:5777`): a local `setTimeout:every: 1000` mutates
`timeLeft` per second per client - free-running divergence.

Design:
- The root Croquet model gains timer support. On `timer_start
  {fid, interval, count}` it dedups by fid (every client publishes on
  realization; the model ignores repeats), then `future(interval)` a tick
  loop. Each tick publishes AND RECORDS `model_timer_tick {fid, n}` in
  `newspeakEvents`; after `count` ticks (the countdown length travels in the
  start event) the model stops itself deterministically. `timer_stop` cancels
  early (dedup again).
- The Newspeak `TimerFragment` override does no local scheduling: it publishes
  start on realization, subscribes to `model_timer_tick` to run the update,
  and relies on the model's count for completion.
- Properties: ticks pace on TEATIME - identical on all clients, no relative
  drift; recorded ticks make replay exact for late joiners.
- **Decision point (history growth)**: every tick is a recorded event. A 1s
  timer is 3.6k events/hour, all replayed by late joiners. Acceptable for
  demo-scale timers; long-lived timers want tick coalescing, which really
  wants heap snapshots - out of scope here, worth an explicit ceiling
  (e.g. the model refuses intervals under some threshold, or auto-stops after
  N ticks) until then.

## Synchronized randomness and time for Newspeak code

The same discipline Croquet enforces model-side, recreated at the event
level:

- **syncRandom**: a Newspeak-side deterministic PRNG seeded from the session
  id (exactly Croquet's seeding trick). Because synchronized event handlers
  run in identical order on every client - and replay re-runs them in that
  order - a PRNG advanced ONLY inside handlers stays replicated and
  replay-correct with no extra machinery. The fence is discipline rather than
  Croquet's hard throw; expose it as `hopscotch syncRandom` with the rule
  documented, and consider a debug assertion (only-during-dispatch flag).
- **syncTime** (design only): the model stamps `this.now()` (teatime) into
  every `model_` event it publishes; the Newspeak side exposes the current
  event's time (e.g. `hopscotch currentEventTime`). Shared logic that needs
  "now" reads that - identical everywhere and under replay; wall-clock stays
  available for purely local display. NOT implemented yet: carrying the stamp
  without breaking existing handlers means wrapping every model-published
  payload in an envelope ({__nsT, data}) and unwrapping in nsSubscribe's
  wrapper AND in replayEvents, tolerating unwrapped payloads from stale
  vfuels. That touches every event dispatch, so it should be its own
  carefully-tested change, not a rider on this batch.

## WebTransclusionFragment: the file-loading pattern

Today (`Documents.ns transcludeFromServer:`): if the named document is not in
Root, EVERY client independently fetches it from the server inside
`asyncContent:` and installs it on local timing - divergent bytes are
possible (server content can change mid-session), install timing races
deferred realization, and late joiners re-fetch yet another version.

Design - exactly the FileChooserFragment shape plus a one-client election:
1. On realization with the document absent, each client publishes
   `transclusion_request {fid, name, viewId}`.
2. The model dedups by name (first request wins, status map in model state)
   and publishes + records `model_transclusion_fetch {name, viewId}` - the
   reflector's ordering IS the election.
3. Only the client whose `localViewId` matches fetches the document from the
   server, stores the raw bytes via the session Data API (encrypted, on the
   file server), and publishes `transclusion_loaded {name, handle}` -
   recorded, so replay and late joiners get it.
4. Every client, on `transclusion_loaded`, fetches the bytes by handle,
   installs the document into Root (guarded: already-present short-circuits),
   and fills the async content. Identical bytes, synchronized install order.
5. Failure: the elected client publishes `transclusion_failed {name, msg}`
   and everyone shows the message. **Decision point**: if the elected client
   dies silently, v1 leaves retry to the user (reload the toggle); a
   timeout-based re-election is a v2 refinement.

This generalizes: "one client performs the IO, stores the result, everyone
consumes the stored bytes" is the reusable recipe for any per-client fetch
(images, feeds), with the reflector's message order as the election.

## Implementation notes (built 2026-08-23, refactored 2026-08-25)

1. **WebTransclusion — via a domain-neutral coordinated-fetch primitive.**
   Originally the seam was `hopscotch documentZipNamed:` - document
   vocabulary in the UI framework, which Gilad rejected on layering grounds
   (2026-08-25). The seam is now
   `hopscotch coordinatedFetch: key via: fetcher ifSuccess: sb ifFailure: fb`:
   a once-per-session IO primitive. The caller supplies the fetcher block
   (bytes to its first argument, failure message to its second) under an
   arbitrary string key; the HTML5 base is degenerate (`fetcher value: sb
   value: fb`); the Croquet override runs the election - of all clients
   requesting a key, the model elects the FIRST requester, only that client
   runs ITS OWN registered fetcher, stores the bytes with the Data API and
   publishes the recorded loaded event everyone (and every late joiner)
   consumes. All document knowledge (the `<name>.zip` XHR, unzip, Root
   install) moved back into Documents `loadFromServerNamed:`, which uses keys
   of the form `document:<name>`. Contract note: callers must NOT assume
   their own fetcher runs.
   Constraint found the hard way: **Croquet rejects subscription scopes
   containing ':'** (its internal scope:event separator). The primitive
   sanitizes the key once (':' -> '.') into an event key used for ALL wire
   traffic - the scope suffix AND the recorded fid, which must match for
   replay lookup - while raw keys stay local (pending lists, fetcher
   registry, handler closures). Distinct raw keys that sanitize alike would
   collide in the model.
   Replay-cursor subtlety: the recorded `model_coordinatedFetch_loaded` is
   subscribed through the counted `subscribeFragment:` wrapper, while the
   UNRECORDED election/failure broadcasts use raw `nsSubscribe` - counting an
   unrecorded event would desynchronize `lastProcessedEvent` from
   `newspeakEvents`. For the same reason the model records EVERY loaded
   answer it publishes, including repeat answers to late requests (receivers
   with no pending request skip the byte fetch entirely).
   Next steps per Gilad: realize the common IO recipe (store bytes / publish
   handle / consume stored result - FileChooser, MediaCreator and this
   primitive all hand-roll it today) as shared code, then extract a shared
   sync service (the `platform sync` facet) as the home for this,
   syncRandom, and the future syncTime; a DocumentsForCroquet override
   remains under consideration by Gilad.
2. **Timer**: base `TimerFragment` was repaired first - it was unused and
   broken (`setTimeout:every:` is a one-shot `setTimeout`, so it decremented
   exactly once, and reconciliation sent the nonexistent `#timeId`); it now
   counts down per second with `setInterval` and stops at 0. The Croquet
   override publishes `timer_start {interval, count}` on realization and only
   subscribes; the model dedups by fragment id, drives `future(interval)`
   ticks (clamped to >= 250ms, count >= 1, so a caller cannot flood recorded
   history), records each tick, and deletes the timer after the last one.
   Residual hazard: ticks recorded for a fragment a late joiner never
   realizes hit replay's wait-for-subscriber timeout (15s per event) - keep
   countdowns short until heap snapshots allow history coalescing.
3. **syncRandom**: implemented in the glue (mulberry32 over an FNV-1a hash of
   the session id) as `nsSyncRandom()`, exposed as
   `hopscotch syncRandom`. Seeded ONCE per client lifetime - the view
   constructor also runs on snapshot restores, and reseeding there would
   reset a stream handlers already drew from. The draw-only-in-handlers
   discipline is documented at both definition sites; a debug-mode
   only-during-dispatch assertion remains a possible hardening.
4. **syncTime** - not built; see the design-only note above.
