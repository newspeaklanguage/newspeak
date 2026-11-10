# Croquet I/O: from "first request wins" to "the connection's owner performs"

**Status:** PLAN, 2026-09-28. Nothing here is built. Written at Gilad's request
after reviewing the `Host_Services` Ampleforth document, whose last third
proposes this reform. This plan turns that proposal into staged, probe-gated
work. It supersedes nothing yet; `HOST_SERVICES_DESIGN_2026-08-31.md` §5 and
`CROQUET_REPLAY_CONTAMINATION_2026-09-12.md` describe what exists.

---

## 1. The problem, restated precisely

Under Croquet every client runs the same code in lockstep, so every client
reaches every host I/O call. Today the choice of which client actually performs
it is made by the reflector: each client publishes `coordinatedFetch_request`
carrying its viewId, and the model's handler elects whichever arrives first
(`DeploymentManager.ns` ~2070, mirrored in `primordialsoup/meta/croquet-post.js`
1475). For that to work, clients must agree on a *key* per request without
talking to each other, so `HostForCroquet` mints it as
`<digest of URL+body>.<per-client ordinal>` (`sharingKeyFor:body:`,
`performKeyFor:`), mutating a per-client counter table (`uriFetchCounts`).

Two defects follow from the principle itself, not from bugs in its execution:

1. **The performer is arbitrary.** It is whoever's packet won, and may change
   from request to request on the same resource. That is fine only for a
   resource every client can reach identically with identical credentials. It
   is wrong for anything machine-local (the agent bus, a local model, a local
   file, the client's own front door) and for any credential that should be
   private to one participant. The bus case was patched with `canPerformHere:` +
   `agentReachableHere:then:` + `awaitCoordinatedText:` — i.e. a hand-built
   exception to the election for one resource.
2. **Agreement on keys is fragile.** It needs every client to make the same
   host calls, in the same order, *per resource*. Any call started from a
   promise continuation, a render, or an unsynchronized startup path can land
   at a client-determined position and skew that resource's ordinal forever
   (the `sharingKeyFor:` comment says as much; `HopscotchWebIDE.ns` ~1117 admits
   the startup model refresh does it). Several of the last month's fixes
   (failure recorded as an answer, 10s requester wait, key per attempt) exist
   to keep keys and elections consistent under replay.

Defects that are **not** caused by the election, and that this reform does not
touch: programmatic editor changes being published (fixed by `isUserOrigin:`),
the replay running ahead of in-flight async work (`nsReplayPace`, the held-
answer stash), and tool results that read client-local state (fixed by
`shareText:via:`). They stay fixed; nothing below removes them.

## 2. The reform

**Every host request has an owner — a participant identity — determined from
replicated state, so every client computes the same owner without consulting
the reflector. Only the owner performs; the result is recorded exactly as
today; everyone else (and every replaying joiner) consumes the recording.**

The owner of a request is, in order:

1. **The owner of the connection it is made on**, if any. A *connection* is a
   Newspeak object representing an ongoing relationship with one external
   resource (an AI chat's provider, a repository, a bus agent). Its owner is
   fixed when it is created, and is a slot of the object — captured, not looked
   up. Requests on it are numbered by a slot of the object.
2. **Otherwise, the initiator of the synchronized event being dispatched** when
   the request is made — the participant whose click or keystroke that event
   records. This covers one-shot I/O issued directly by a UI action (loading a
   document on a link click, model discovery from the setup form).
3. **Otherwise it is a bug**, and the platform says so (see §4.4). There is no
   silent fallback to an election in the end state.

This is Gilad's design from the document, with one refinement forced by the
code: the document assumes a tool request "is being processed as part of a
croquet subscription, and so it is run on each client at the same virtual
time", so an ambient "current initiator" register would be correct when the
tool issues I/O. It is not: tool rounds, and every completion after the first
in a turn, run in JS `then:` continuations of the previous answer
(`AIAccess.ns` `completeWithToolLoop` ~2755/2826, `toolResultFor:...` ~3288),
after the dispatch that delivered the answer has returned. On psoup Newspeak
promise callbacks drain before control returns to JS
(`ActorsForPrimordialSoup.ns` MessageLoop `finish: drainQueue`), but on NS2JS
each is a `setTimeout 0` macrotask (`ActorsForJS.ns` 45-55), so the register
could hold a later event's initiator by then. Hence rule (1) takes precedence
and rule (2) may be consulted **only synchronously inside a dispatch**.

### 2.1 What this removes

- The election race in `coordinatedFetch_request`; the reflector no longer
  chooses anything.
- `uriFetchCounts`, digest+ordinal keys, and the constraint that all clients
  make the same calls in the same order per resource. Keys become
  `c.<connection id>.<seq>` (connection requests) or `e.<event index>.<k>`
  (event-initiated requests), both derived from replicated state.
- `canPerformHere:` and `awaitCoordinatedText:` as special cases: *every*
  non-owner awaits; that is the normal path.
- The need to re-elect or not re-elect after failures: nobody but the owner is
  ever asked.

### 2.2 What stays

- Recording of answers, loaded and failed, in `newspeakEvents`; late joiners
  consume recordings. The owner itself, when it replays after a reload, also
  consumes recordings for requests already answered.
- `shareText:via:` for tool results (every client runs the tool for its
  effects; the owner's text is the one recorded).
- The replay machinery (dispatch chain, pacing, held answers) and
  `isUserOrigin:`.

### 2.3 What it newly costs

- **A stall when the owner is absent.** Requests on its connections wait
  until it returns or someone takes over (§4.3). Today any client can serve a
  public resource. This is the correct semantics for owned resources and a
  regression for public ones, which is why rule (2) exists and why takeover is
  part of the plan rather than a later nicety.
- **A stable participant identity**, which does not exist today (§3).

## 3. Participant identity (prerequisite)

Croquet's viewId is per join: a reload gets a new one, and nothing in the glue,
`JSForCroquet`, or `HopscotchForCroquet` persists any client identity
(`JSForCroquet` now keeps its virtual localStorage purely in memory). An owner
identified by viewId cannot "come back".

**Proposal:** a *participant id* minted by the glue on first load and kept in
the browser's real `sessionStorage` under a reserved key (`ns_participant`).
`sessionStorage` survives reload, is per tab (two tabs are two participants —
correct, since each runs its own image copy and its own pending closures), and
is outside the replicated image. Passed to `Session.join` as `viewData`; the
model learns `viewId -> participantId` on `view-join` (the handler shape is
already documented at glue ~1308-1317: Croquet then delivers
`{viewId, viewData}`).

Decisions for Gilad:
- **Per tab (sessionStorage) or per browser profile (localStorage)?** Per
  machine is what bus/file locality really cares about, but two tabs sharing
  an identity would both think they own a connection. Recommend per tab.
- The participant id must **never** be used by Newspeak code to branch on
  "am I the owner" except inside `HostForCroquet`/`HopscotchForCroquet`; to the
  application it is opaque data. (Branching on it in application code is the
  one way to reintroduce divergence.)

## 4. Mechanism

### 4.1 Stamping the initiator on events (glue + model)

- `nsPublish` (glue 746), the single outbound path, adds `by: <participantId>`
  to every envelope (the `{fid, label, bare}` wrapping at 775-780 already
  normalizes shapes, so this is one place).
- The model's `publishEvent` / `publishEventAndData` (1171-1186) copy `by` into
  the recorded event and into the broadcast, and also record the event's
  **index** (`newspeakEvents.length - 1`), which is globally agreed.
- The view-side dispatch (the `nsSubscribe` wrapper, 1042-1072, and the replay
  thunk, 1684-1726) sets two globals around the handler call:
  `nsDispatchInitiator` and `nsDispatchIndex`, and clears them after. This is
  the only place they are set, so "inside a dispatch" is testable.
- The embedded copy of the model in `DeploymentManager.ns` must change in
  lockstep (it is the one the deployed builds use).

### 4.2 Owned requests in the model

`coordinatedFetch_request` gains an `owner` field. Model behaviour:

- no entry → create `{status: 'pending', owner}`; if a live view of `owner` is
  present, publish `model_coordinatedFetch_fetch` **addressed to that view**;
  otherwise leave it pending and publish an unrecorded "waiting for owner"
  notice for the UI.
- `loaded` / `failed` → as today (recorded repeat answer).
- `pending` and the requester **is** the owner (e.g. the owner reloaded and its
  replay re-reached the request, re-registering the closure) → publish `fetch`
  to it again. This is how an owner that dropped mid-request resumes; the
  request is re-issued because its answer never entered the session.
- On `view-join` of a participant that owns pending entries: nothing
  immediate — its replay will re-request them (above), which is also the moment
  its closure exists.
- The Newspeak `fetch` handler checks `electedParticipant = localParticipant`
  instead of viewId.

The unowned election path is retained, unchanged, as `owner: null`, until
§6 phase 6 removes it.

### 4.3 Takeover

A recorded event, `connection_transfer {connection id, newOwner}`, issued from
a UI action ("Take over this chat") by the participant who wants it. Every
client applies it at the same stream position: the connection object's owner
slot changes; the model re-addresses any pending entry for that connection to
the new owner. Deterministic by construction. The UI offers it only when the
owner is absent (presence already tracks `view-exit`).

Open: takeover of a bus or local-model connection only makes sense if the new
owner can reach the resource; the UI should run the existing
`agentReachableHere:` preflight before offering it.

### 4.4 Newspeak API

In `HostForCroquet` (and a trivial counterpart in psoup `Host.ns`, so the API
is uniform across platforms):

```
host connection        (* a new Connection; owner := current dispatch initiator *)
aConnection fetcher    (* Fetcher whose requests are owned by the connection *)
aConnection performer  (* likewise *)
host fetcher / host performer   (* unchanged names: event-initiated requests *)
```

- `Connection` holds `owner` (opaque) and `seq`; its id is minted from
  `nsDispatchIndex` + a per-dispatch counter, so it is agreed everywhere.
  Creating one **outside a dispatch** is an error under Croquet (raise with a
  message naming the rule) — this is where misuse is caught early.
- On the base `Host`, `connection` answers an object whose fetcher/performer
  are the plain ones. Applications written against connections run unchanged
  off Croquet.
- `host fetcher` requests made **outside a dispatch** under Croquet: in the
  end state an error; during migration, a console warning naming the call
  site, then the legacy election (so we can find them all before forbidding
  them).

### 4.5 Where owners come from for each call site

(From the call-site survey; line numbers approximate.)

| Call site | Trigger | Owner |
|---|---|---|
| Chat completions (`Provider>>completionVia:...`, AIAccess ~2242) | first request: user Send/Retry; later: continuations | the chat's connection |
| Bus completions (`BusProvider>>performRequest:through:` ~784) | same | the chat's connection; `canPerformHere:` goes away |
| Tool-result sharing (`Session>>shareToolText:forCall:` ~3157) | continuation | the chat's connection |
| `send_to_agent` (`AI_IDE_Support postToBusOnce:` ~4099) | tool continuation | the chat's connection (the agent must be reachable from the chat's owner — an honest constraint, stated in the tool's error) |
| Model discovery from the setup form (`refreshModelCacheFor:` ~481, via `ensureModelCacheRefreshedFor:` at **render**) | render within a click's dispatch | event initiator — **verify** render is synchronous inside the dispatch (phase 0) |
| Model refresh buttons | click | event initiator |
| Startup model refresh (`HopscotchWebIDE refreshProviderModelsInBackgroundFor:` ~1109) | unsynchronized startup | none — **disable under Croquet**; discovery happens from the setup form |
| Document load (`Documents loadFromServerNamed:...` ~2922) | link click / render / transclusion | event initiator — verify transclusion loads are inside a dispatch |
| Inbound bus traffic (`synchronizedInbox:`) | local SSE frame | unaffected: already posted once and recorded |

**The chat's connection** is created in `IDEChatSetupSubject>>startChat`
(AI_IDE_Support ~898), inside the Start Chat click's dispatch, and stored where
the chat's Session will find it. The Session itself is built lazily at render
(`chatSubjectFor:` ~1747, `createFreshSessionFor:focus:` ~1975), so the
connection must be created at startChat and handed down, not created by the
Session. It must **not** be persisted into the chat document's saved form: a
participant id is meaningless outside the Croquet session. A chat document
reopened in a later session gets a new connection on its first Send (owner =
the sender).

## 5. Risks and unknowns

1. **Render outside dispatch.** If a presenter renders in a later animation
   frame rather than synchronously in `updateGUI:` from the handler, rule (2)
   has no initiator for render-triggered I/O. Phase 0 measures this.
2. **Runtime difference in promise turns** (psoup drains synchronously, NS2JS
   uses setTimeout). The design never reads the ambient initiator from a
   continuation, so it should not matter; the probes must nonetheless run on
   both runtimes.
3. **Owner reload mid-request re-issues a POST.** For a model completion that
   is a second billed call whose first answer was lost. Acceptable (the session
   never saw the first), but should log.
4. **Event payload growth.** `by` + index on every recorded event: ~40 bytes
   each; measure against the retained-volume budget noted in the presence work.
5. **Two copies of the model JS** (glue file and `DeploymentManager.ns`) must
   stay identical; add a check to the build or a probe.
6. **Old sessions.** Persisted `newspeakEvents` without `by`: treat a missing
   `by` as "unowned" and run the legacy path, so old sessions still replay.

## 6. Phases

Each phase ends with probes green on psoup and, from phase 4 on, on the NS2JS
deploy too. No phase ships without Gilad testing interactively. Nothing is
committed without his say-so.

**Phase 0 — Baseline and measurement (no behaviour change).**
- Run the maintained batteries against a TEST build of the current tree and
  record results: `model-discovery-battery.js`, `completion-election-probe.js`,
  `bus-election-probe.js`, `bus-locality-probe.js`, `setup-latejoin-probe.js`
  (default recipe, `FAIL_TURN=1`, `TOOL=evaluate`, `INBOUND=1`),
  `share-probe.js`, `outbound-once-probe.js`, `host-probe.js`.
- Instrument (TEST build only) every `HostForCroquet` entry point with "inside
  dispatch? which call site?", and run the chat, document and discovery
  recipes. Output: the definitive table of §4.5 with measured, not inferred,
  triggers. This decides risks 1 and the transclusion question.

**Phase 1 — Participant identity and stamped events.**
Glue + model: participant id in sessionStorage, `viewData`, view-join map,
`by` and index on events, dispatch globals. Newspeak: `HopscotchForCroquet`
accessors `dispatchInitiator` / `dispatchIndex` / `localParticipant`. No
consumer yet.
Probe (new, `participant-probe.js`): two clients; every recorded event carries
the right `by`; a reload keeps the participant id and gets a new viewId; a
replaying joiner sees the same `by`/index as the originals; old persisted
sessions still replay.

**Phase 2 — Owned requests in the model and HopscotchForCroquet.**
`coordinatedFetch_request` with `owner`; addressed `fetch`; pending-owner
state and notice; owner re-request after reload. `coordinatedText:` /
`coordinatedFetch:` gain an owner argument; old signatures pass null.
Probe (new, `owner-probe.js`, extending `host-probe.js`): B issues a request
owned by A → A performs, B never does; A absent → pending, no performer, notice
shown; A returns → performs once, both fulfil; joiner performs nothing.
Negative control: the same recipe with owner null shows the old
first-arrival behaviour (so the probe can tell the two apart).

**Phase 3 — Connection API.**
`host connection` on HostForCroquet and base Host; connection keys; the
outside-dispatch error for creation; warnings for unowned requests outside
dispatch. Unit-level tests in the IDE on the base Host; Croquet probe for key
agreement across clients and replay.

**Phase 4 — AI chats onto connections.**
Connection created in `startChat`, threaded to Session/Provider; completions,
bus perform, `shareToolText:`, `send_to_agent` through it; remove
`canPerformHere:` usage (keep the reachability preflight at Start Chat and
before takeover).
Probes: `setup-latejoin-probe.js` all recipes; `completion-election-probe.js`,
`bus-election-probe.js`, `bus-locality-probe.js` (now expecting the *owner*'s
machine, not "a machine that can reach it"); new recipes:
- turn typed on B, chat started by A → request leaves from A;
- private credential: key configured only on A → B's turns still succeed;
- A reloads mid-turn → turn completes after A returns, exactly one answer
  recorded;
- A leaves → B sees "waiting for A", takes over → B's machine performs.

**Phase 5 — Documents and discovery.**
Event-initiated ownership for `loadFromServerNamed:` and setup-form discovery;
startup background refresh disabled under Croquet.
Probes: `model-discovery-battery.js`; a two-front-door document probe (the
document exists only on A's server: B clicks the link → B's host is asked,
fails, and the failure is shared; A clicks → loads for both). That second case
makes the semantics visible and is worth Gilad's judgement.

**Phase 6 — Retire the election.**
Delete the unowned path in the model, `uriFetchCounts`, `sharingKeyFor:`,
`performKeyFor:`, `canPerformHere:`, `awaitCoordinatedText:`/`coordinatedFetch_await`
and the stale comments (e.g. `runCoordinatedFetcherFor:`'s "re-elect"). Unowned
requests outside a dispatch become errors. Full battery on both runtimes.

**Phase 7 (optional) — Truly private credentials.**
An API key in the image is replicated to every participant, closure or not.
To make "only A has the key" real, the key must live outside the image: in A's
front door (`/_ns/fetch` injecting a configured header) or A's glue. Phase 4's
credential probe then tests the real thing rather than an image slot that B
also holds.

## 7. Decisions (settled by Gilad, 2026-09-28)

1. **Participant identity is per tab** (`sessionStorage`).
2. **One-shot (event-initiated) requests wait for their owner, exactly like
   connection requests.** No fallback to "any present participant"; revisit
   only if a real case needs it.
3. **A chat reopened in a later session adopts its first sender as owner.**
4. **Takeover is UI-only** — never available to AI tools.
