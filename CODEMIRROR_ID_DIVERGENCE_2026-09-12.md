# Chat fragment-id divergence: the mechanism, read off the source

2026-09-12. Supersedes the earlier version of this file, which blamed
render-count skew in `newIdFor:`. That was wrong and the data refuted it.
Companion to `CROQUET_SCOPED_FRAGMENT_IDS_2026-08-18.md`, whose invariant this
violates.

## The invariant being broken

From `CROQUET_SCOPED_FRAGMENT_IDS_2026-08-18.md`:

> That scope string **is** the Croquet event address: a widget publishes on it,
> and every client's corresponding widget subscribes to it. Clients therefore
> agree on which fragment an event refers to **only if they create fragments in
> the same order**. … Anything that lets one client create fragments in a
> different order — or merely a different *number* of them — permanently skews
> every id after that point on that counter.

That doc found three violating constructs (lazy sequences, async content,
web transclusion) and fixed them by scoping. **The chat is a fourth, unscoped.**

Stated as a rule the codebase should enforce:

> **No synchronized fragment may be constructed on a code path whose execution
> depends on client-local state.** In-flight status, error state, viewport,
> async arrival order, and election outcome are all client-local.

## The violation

`HopscotchForHTML5.ns`, `ChatStatusPresenter>>definition` (~6410) has four
shapes, and which one runs is decided entirely by client-local state:

| condition | synchronized fragments built |
|---|---|
| `subject waiting` | 1 button (Cancel), **no dropdown** |
| `canRetryQuietly and: [ errorMessage isNil not ]` | retryRow's button + modelPicker's **dropdown** + refresh button |
| otherwise | modelPicker's **dropdown** + refresh button |

`subject waiting`, `subject errorMessage` and `subject canRetry` are per-client.
`button:` mints `newButtonId`; `dropDownMenu:` mints `newDropDownMenuId`
(`HopscotchForCroquet.ns:819`, scope `nsdropdownmenu_`). Both counters are
global — no `withFragmentScope:` anywhere near this code.

So two clients rendering the same chat at slightly different moments consume a
different number of ordinals. From that instant every later id on those counters
is skewed, and events land on nothing (or, worse, on the wrong widget).

`ChatPresenter>>messagesArea` (~6650) has the same defect in miniature:

```
subject errorMessage isNil ifFalse: [ fragments add: (label: 'Error: ' …) ].
fragments isEmpty ifTrue: [ fragments add: (label: …) italic ].
```

## Why this explains everything we have seen

- **Chat-only.** A class view's fragment tree has no transient state, so it is
  constructed identically everywhere. Class-view CodeMirrors sync fine; chat ones
  do not. Confirmed by Gilad.
- **`nsdropdownmenu_/12` (the earlier, shelved symptom)** — the dropdown is
  exactly the fragment that exists in one branch and not the other. It was never
  a separate bug.
- **`NotFound: 'Claude Opus 5' in setupCroquetView`** — a replayed menu click
  arriving at a client whose menu was built from a different model list, because
  the menus had diverged.
- **The originating clients die too.** This needs no joiner: any two clients whose
  in-flight windows differ by one render diverge from each other.
- **Bus and coordinated completions make it systematic, not a race.** The elected
  client performs the exchange; the others consume a recorded reply. Their
  in-flight windows are structurally different *by design*, so `subject waiting`
  is guaranteed to differ across a render. This is why bus chats fail reliably
  after one or two trivial turns, while inline chats merely "work for a while".
- **Late join looks worst** because the joiner then pays 15s per unmatched event
  (`croquet-post.js:840`), so one early skew turns into a visible hang.

## Confirmed, quantitatively

**Live measurement** (Gilad, three clients on one session). Distinct lineages per
counter:

| counter | Chrome (originator) | Safari (joiner) | Brave (joiner) |
|---|---|---|---|
| `nsbutton_` | **532** | **527** | 527 |
| `nsdropdownmenu_` | 224 | 224 | 224 |
| `nsmenu_` | 0 | 0 | 0 |
| `nscodemirror_` | 90 | 90 | 90 |

The two joiners agree with each other and differ from the originator by five
buttons. That is the signature: the extra mints come from local `updateGUI:`
renders during an in-flight turn, which are not recorded events, so no replaying
client ever performs them.

**Deterministic construction test** (`croquet-probes/chat-id-divergence-probe.js`,
section A) — a real `ChatStatusPresenter` over a real `ChatSubject`, one fresh
presenter per state, counting what the minting ledger records:

```
waiting = {button: 1}
idle    = {imageButton: 2, dropDownMenu: 1}
errored = {imageButton: 2, dropDownMenu: 1}
```

One render mints **one id when waiting and three when idle, of disjoint types**.
Waiting mints only `button` (Cancel); idle mints only `imageButton` (refresh) and
`dropDownMenu` (the picker).

The two measurements agree exactly. Five extra *waiting*-state renders on the
originator give +5 `nsbutton_` and +0 `nsdropdownmenu_` — which is what was
observed. The types discriminate: extra *idle* renders would have skewed the
dropdown and not the button. It is the other way round.

From that skew, every button minted afterwards is misaddressed. The chat's
Send/Cancel/Retry were minted after; the rest of the IDE's buttons were minted
before. Hence a dead chat in a session that otherwise syncs — on the originating
clients too, with no joiner involved.

Also established: the ledger agreed at 26/26 between two clients doing the same
things, so it does not manufacture false alarms; and it labels each mint with the
presenter that made it (`{"t":"imageButton","o":25,"s":"","c":"AllWorkspacesPresenter"}`),
so a live divergence is attributable rather than merely visible.

## The fix

The transient controls are **inherently per-client**: whether *I* am waiting,
whether *my* turn errored, whether *I* can retry. They are a client's view of a
shared turn, not shared state. So:

1. Build them with `NonSyncingPresenter` (HopscotchForCroquet's existing escape
   hatch — "information that is not-synchronized, but instead restricted on a
   client", which overrides every fragment factory to the non-syncing variant).
   Nothing transient then touches a counter.
2. Sync the *decision*, not the widget. Model selection should be shared state on
   the chat document, changed by an ordinary synchronized action; the picker that
   sets it can be non-syncing. That also removes the `menuMap` NotFound crash
   class, since no menu click is ever replayed into a differently-built menu.
3. Same treatment for `messagesArea`'s error/empty branches.

Scoping (`withFragmentScope:`) is the wrong tool here: it would contain the
damage but the counters are monotone within a scope too, so repeated renders in
differing branches still drift. Not synchronizing per-client UI is the correct
answer, and it is what the architecture already provides for.

## Standing guard worth adding — BUILT 2026-09-14/15

A divergence alarm: each client reports its minting-ledger length at
synchronization points; a mismatch logs loudly *at the moment it happens* rather
than hundreds of events later, naming the action responsible. The next construct
that breaks the invariant then reports itself instead of being debugged from
consequences.

**As built** (croquet-post.js, mirrored in DeploymentManager.ns; HopscotchForCroquet.ns),
in two halves, both deterministic per recorded event — no digests, no timing
races between concurrent users:

1. **Delivery count** (newspeak `75426ee`, psoup `44f9585`). The root model tells
   its own view about every event it records (`nsEventRecorded`, a local
   model-to-view publish). The view counts expected vs actual deliveries per
   address (scope + fragment id + event kind) and, after a bounded wait for
   deferred realization, reports an event that reached no handler:
   `console.error('Croquet DIVERGENCE ...')`, or a warning if this client had
   retired the fragment (a click racing a navigation). Silent when a fragment of
   the *same kind* sits at the address — exactly the 2026-09-14 case (Cancel
   where Apply should be), which delivered fine to the wrong button.
2. **Label check** (2026-09-15). Every subscription registers what its fragment
   IS — `Fragment>>croquetLabel`: the enclosing presenter's `presenterLabel`
   (made public for this walk; `class` is not a public message), the fragment's
   kind, and a button's or link's text, e.g.
   `EvaluatorPresenter/ButtonFragment:Evaluate Selection`. The publisher's label
   rides in the reflector payload (`nsPublish`; a bare fragment id becomes
   `{fid, label, bare}` and the model's `publishEvent` unwraps it), is recorded
   beside the event, and every client compares it with its own label at the
   address on receipt — live once the event is delivered (`nsCheckDelivery` →
   `nsCheckLabel`), under replay before dispatch. Old histories carry no labels
   and are not checked. Labels must be identical on clients that are in sync:
   nothing client-specific may enter one.

Reports accumulate in `nsDivergences` (`kind: 'delivery' | 'label'`) for the
probes. `setup-latejoin-probe.js` asserts a clean run reports nothing on either
client, and its `PROVOKE=1` mode swaps two of B's button addresses, has A click
one, and expects exactly one `label` report on B naming both labels (16/16 on
the TEST build, 2026-09-15). Hazard found on the way: an unguarded `p class name`
on another object raises, so every label was empty until `presenterLabel` was
used — the census probe `label-census-probe.js` shows what a build registers.
