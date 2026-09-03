# Croquet fragment identity & subscription lifecycle — implementation plan

2026-08-27. **Status 2026-08-30: IMPLEMENTED (uncommitted), psoup-verified headlessly;
awaiting Gilad's interactive pass. See §8 (Implementation notes) at the end.** Companion to the eval-"stall"
diagnosis (see SESSION summary / project_croquet_revival memory): the stall was
an empty selection at click dispatch, caused by the defects below.

## 1. Established facts (probe evidence, both platforms)

1. **Construction subscribes.** Every Croquet fragment override runs
   `setupCroquetView` in its instance initializer. Presenter definition rebuilds
   construct fragments wholesale, including fragments whose visuals never
   attach; each construction mints a fresh `fragmentId` and subscribes under
   `<kind>_<id>`. Nothing ever unsubscribes. Measured: after three workspace
   evaluations, the registry holds `nscodemirror_/1../4` (six eventSpecs each),
   `nsbutton_/1../16`, `nsImagebutton_/1../56` — for ONE live CodeMirror and one
   row of buttons.
2. **Identity adoption is cosmetic and too late.** `updateVisualsFromSameKind:`
   copies only `scope_slot` from the old fragment — after the initializer has
   already subscribed under the new id. The publish side uses `fragmentId`
   (fresh), so publish-id and adopted scope diverge by construction.
3. **The base CM update drops one handler.** HopscotchForHTML5
   `CodeMirrorFragment>>updateVisualsFromSameKind:` copies and re-targets
   `beforeChangeHandler`, `changeHandler`, `keyHandler` — but NOT
   `beforeSelectionChangeHandler` (neither copied nor re-targeted). The
   selection hook therefore points at generation 1 forever: observed as
   changes publishing under the newest fid while selections publish under `/1`.
4. **Consequence: stream pollution.** With 2+ generations live on one editor,
   an echo applied by one generation is observed by another generation's hook,
   whose per-instance `reflecting` flag knows nothing of the application, and
   the stale cursor state is re-published — appended to the authoritative
   order AFTER newer selections. Every client then faithfully converges on a
   collapsed cursor; a dispatched Evaluate click reads an empty selection.
   (Recorded histories show the `(end,end)`/`(0,0)` pair re-appearing verbatim
   after the select-all.)

The selection-sync design itself is sound: with a single generation, reflector
ordering guarantees the select-all is the last-applied selection before the
click. The fix restores that invariant; it does not change the design.

## 2. Design principles

- **One Croquet identity per visual lineage.** A fragment lineage = an attached
  visual and the chain of same-kind fragments that successively own it. The id
  is minted when the lineage FIRST attaches and is adopted by every same-kind
  successor. Recorded histories then reference ids that stay live as long as
  the visual does.
- **Subscription lifecycle == visual lifecycle.** Subscribe on first
  attachment; transfer (not duplicate) on same-kind update; unsubscribe on
  disposal (kind-replacement or removal).
- **Retarget, don't resubscribe.** Same-kind updates re-point the existing
  subscription's handler at the new fragment, mirroring the base CM's
  CallBackWrapper `callback:` idiom. Unsubscribe is reserved for disposal.

## 3. Mechanism, layer by layer

### 3a. Glue: `nsUnsubscribe` (canonical `primordialsoup/meta/croquet-post.js`; mirror: `DeploymentManager.ns` croquetSupportScript — keep in sync; splice into staged croquetpsoup.js)

```js
function nsUnsubscribe(scope, eventSpec) {
    const key = scope + eventSpec;
    const entry = newspeakSubscriptions.get(key);
    if (!entry) return;
    newspeakSubscriptions.delete(key);           // durable act: replaySubscriptions
                                                 // resubscribes only what is here
    if (theView && theView.session) {
        theView.unsubscribe(scope, eventSpec, entry.handler);  // handler-specific
    }                                            // (croquet >= 1.1 API); detached
}                                                // view: deletion above suffices
```

Notes:
- `view.unsubscribe(scope, event, handler)` is handler-specific (teatime
  view.js:243), so removing one entry cannot disturb another subscription on
  the same scope, and avoids the append-on-resubscribe double-delivery trap.
- Replay compatibility: `replayEvents` resolves handlers from
  `newspeakSubscriptions` at execution time. Because disposal is driven by
  synced GUI updates, it happens at the same event position on every client
  and during replay, so an event recorded while its subscriber lived finds the
  subscriber live at that point of the replay too.

### 3b. HopscotchForCroquet: handler indirection + lifecycle

The module-level `Fragment` override (inherited by every leaf via class
hierarchy inheritance — it is where `subscribe:eventSpec:handler:` already
lives) gains the shared machinery:

- `croquetTarget` — a one-slot cell (`CroquetHandlerTarget` or a plain holder)
  carried per lineage. Subscription handlers close over the CELL, not over a
  fragment: `[:e | croquetTarget value handleModelEvent...]`-style, i.e. each
  leaf's `setupCroquetView` closures reference `croquetTarget value` (the
  current fragment) instead of `self` for anything generation-sensitive.
  Simplest faithful form: the closures stay as written in each leaf, but are
  created by the CURRENT lineage owner; on adoption the cell is repointed and
  the closures are re-created against the new owner by re-registering the RAW
  handler in place (see below).
- `croquetEventSpecs ^<List[String]>` — per-leaf list of the model eventSpecs
  it subscribes (`{#model_button_click}` for Button; the six CM specs; etc.).
  Default in the Fragment override: empty.
- `retireCroquetSubscriptions` — `croquetEventSpecs do: [:spec |
  js global nsUnsubscribe: scope eventSpec: spec]`. No-op when the list is
  empty.

Two candidate shapes for the same-kind transfer; DECISION POINT (see §6):

**(i) unsubscribe + resubscribe under the adopted scope** — in
`updateVisualsFromSameKind:`: adopt `fragmentId`/`scope` from old, then for
each eventSpec `nsUnsubscribe(scope, spec)` and re-run `setupCroquetView`
(subscribing the NEW fragment's closures under the OLD scope). Registry key
unchanged; net one subscription. Simple to reason about; two glue calls per
eventSpec per reconciliation.

**(ii) retarget through the cell** — subscribe ONCE per lineage (at first
attach) with closures that indirect through `croquetTarget`; adoption copies
the cell and repoints it (`croquetTarget value: self`). No glue traffic on
reconciliation at all; matches the base CM CallBackWrapper idiom. Slightly
more moving parts (every leaf's handlers must consistently indirect).

Recommendation: **(ii)** — it is the established idiom, and reconciliation is
hot (every GUI update); but (i) is acceptable if the indirection is judged too
subtle.

**DECIDED 2026-08-30 (Gilad): go with (i) — explicit unsubscribe/resubscribe —
for now**; easier to debug if anything goes wrong. Once everything works,
migrate to the retarget-cell shape (ii) as a later stage. The `croquetTarget`
cell machinery above is therefore DEFERRED; implement (i) with the closures as
each leaf writes them today.

Per-leaf changes (Button, ImageButton, Checkbox, RadioButton, Hyperlink,
HyperlinkImage, CodeMirror, TextEditor, Picker, ColorPicker, DatePicker,
TimePicker, Slider, DropDownMenu, FileChooser, Timer — final list from an
audit of which overrides mint ids):

1. Initializer: REMOVE the `setupCroquetView` call (no subscription at
   construction).
2. `createVisual` override: `setupCroquetView. ^super createVisual` —
   subscription happens exactly when a lineage first attaches (fresh render or
   kind-replacement). Replay drives real realization, so replayed histories
   subscribe at the same points.
3. `updateVisualsFromSameKind:`: adopt `fragmentId` (not just `scope`) from
   the old fragment, transfer per (i)/(ii), then `^super ...`.
4. Publishers already use `fragmentId`; after adoption publish-id ==
   subscription-id == the lineage id for the visual's whole life.

TimerFragment (`timer_<id>` starts), coordinatedFetch, and FileChooser
domain-keyed subscriptions are NOT generational and are untouched.

### 3c. Base HopscotchForHTML5 (two small changes, benefit both platforms)

1. **Fix the dropped selection handler**: `CodeMirrorFragment>>
   updateVisualsFromSameKind:` copies `beforeSelectionChangeHandler` from the
   old fragment and re-targets it (`callback: [:cm :sel | 
   respondToBeforeSelectionChange: sel. nil]`) exactly like the other three.
   This is a standalone base bug (stale generation keeps receiving the CM's
   selection signals).
2. **Disposal hook**: `Fragment` gains `public noticeDisposal = ()` (name
   subject to Gilad's taste — `retire`?), default empty, called on the OLD
   fragment wherever a fragment's ownership of a visual ends without a
   same-kind successor:
   - `updateVisualsReusingFrom:` else-branch (kind replacement),
   - composite child-removal sites in reconciliation (the
     `container removeChild: gone visual` family, including the keyed
     reconciliation path — call-site audit during implementation).
   The Croquet Fragment override implements it as
   `retireCroquetSubscriptions`.

Whole-tree teardown (navigation) needs no special case: navigation is itself a
synced GUI change, and page replacement flows through the same reconciliation
entry points; where it provably does not (audit), the shell's page-swap calls
`noticeDisposal` down the outgoing tree via `childrenDo:`.

## 4. Sequencing

1. Glue: add `nsUnsubscribe` to `meta/croquet-post.js`, mirror into
   `DeploymentManager.ns`, splice staged copies. Inert until used.
2. Base: selection-handler retarget fix + `noticeDisposal` hook (+ call-site
   audit). Re-run plain-platform sanity (plain-eval-probe, typechecker suite):
   the retarget fix alone may change nothing observable on plain HTML5, but
   the CM behaviour must be verified there first since both platforms share it.
3. Croquet: shared machinery in the `Fragment` override; convert
   **ButtonFragment and CodeMirrorFragment first** (they cover the entire
   probe scenario), verify, then convert the remaining leaves mechanically.
4. Verification battery (§5), then Gilad interactive pass, then commit
   (master + psoup glue + mirror when webide-ai-access unblocks).

All .ns edits go through pretty-print / round-trip / parse-validate gates and
the typechecker suite, per standing rules. Testing against ADDITIVE
`out/*-TEST.*` artifacts; stock `out/` untouched while sessions may be live.

## 5. Verification

- **Registry invariant** (new probe assertion): subscription-key count is
  CONSTANT across N workspace evaluations; exactly one generation per visual;
  publish fid == subscription fid.
- **The original bug**: eval-probe steps w1, w2, m1 ALL complete with the
  plain 2.5s flow (no reselect hack), psoup and NS2JS.
- **Stream cleanliness**: recorded history contains no re-published stale
  selection pairs after edits (assert no duplicate `(end,end)/(0,0)` echoes
  following a select-all).
- **Regression sweep**: croquet-liveview-edit-test (caret/focus/scroll,
  convergence, late joiner), the six determinism suites
  (transclusion/timer/random × psoup/NS2JS), persistence cold-join test.
- **Late-join + disposal**: new probe — navigate between pages (retiring
  subscriptions), then late-join and assert full catch-up (exercises
  replay-through-disposal ordering).

## 6. Decision points — RULED BY GILAD 2026-08-30

1. Transfer shape: **(i) explicit unsubscribe/resubscribe** for now (easier to
   debug); retarget-cell (ii) as a later stage once everything works.
2. Disposal hook: **`noticeDisposal`, declared default-empty on base Fragment;
   meaningful implementation only in the HopscotchForCroquet Fragment
   override.** Gilad asked whether the declaration itself could live entirely
   in the Croquet override. Verified in code: it cannot, because the call
   sites are base HopscotchForHTML5 reconciliation code shared by both
   platforms — `updateVisualsReusingFrom:` (line 1844) and the child-removal
   sites (2643, 2835, 4325, …) — and HopscotchForCroquet overrides none of
   those methods; on plain HTML5 the send would DNU without the base default.
   Moving the call sites into the Croquet module would mean duplicating the
   reconciliation methods there, which would drift from base. Gilad's premise
   holds exactly as stated: the base contribution is one empty method — no
   state, no behavior, no overhead beyond an empty send at disposal sites —
   and ordinary Hopscotch never overrides or observes it.
3. Id minting at first attachment: **accepted.** No worries about old
   sessions (all dev-experiment session state was wiped 2026-08-30; reflector
   persist/ and out/files/apps/ are empty).
4. Evaluate-event payload capture: **declined for now** — do not add traffic
   to the Evaluate event. Revisit only if stable identities prove
   insufficient.

## 7. Risks

- Missed disposal call-site → a lingering generation (today's status quo,
  strictly no worse); the registry-invariant probe is the tripwire.
- Over-eager disposal (retiring a fragment that still receives events) →
  orphaned replay lookups surfacing as the 15s poll + warn/skip; the
  late-join disposal probe covers the navigation case.
- The `reflecting`-flag protocol interacts with handler transfer: the flag is
  per-fragment state; with one generation per lineage this is exactly the
  regime the protocol was written for. The initiator's own-echo toggle
  semantics must be preserved verbatim through the transfer (copy the flag in
  adoption).

## 8. Implementation notes (2026-08-30, uncommitted)

Files: HopscotchForHTML5.ns, HopscotchForCroquet.ns, DeploymentManager.ns,
primordialsoup/meta/croquet-post.js (+ spliced staged croquetpsoup.js in both
out/ trees). TEST artifact: out/CroquetHopscotchWebIDE-TEST.vfuel. Probes:
croquet-probes/eval-probe5.js (plain-flow w1/w2/m1 + registry invariant),
croquet-probes/latejoin-probe.js (nav→eval→back→nav→eval, then cold join),
croquet-probes/nav-trace-probe.js (subscription add/remove tracing).

Deviations from / additions to the plan as written:

1. **Id minting stays at construction** (initializer slots unchanged in shape,
   now `public ... ::=` for adoption). The scoped counters are driven by synced
   construction, so construction-minting is exactly as deterministic as today —
   and id sequences are UNCHANGED from the old code, so plan §6.3's persisted-
   history orphaning caveat never materializes. Only the SUBSCRIPTION moved to
   first attach (createVisual -> ensureCroquetSubscriptions), guarded by a
   `lazy croquetSubscribed` flag on the Croquet Fragment override.
2. **Disposal is not final — revival re-arm.** Subjects cache their presenters,
   so history navigation RE-DISPLAYS trees whose subscriptions were retired
   (visuals + DOM handlers intact ⇒ they publish under original ids nobody
   hears). Found by latejoin-probe: the revived home page's Workspaces link was
   dead. Fix: `rearmCroquetSubscriptions` — a dedicated walk over childrenDo:
   driven from the Croquet shell's displayPresenter:, plus a noticeExposure
   hook for exposure paths that bypass displayPresenter: (toggle composer).
   The noticeExposure walk ALONE is insufficient: base CodeMirrorFragment and
   HolderComposer override it without a super send, cutting the walk (that is
   why the revived workspace's CodeMirror stayed dead until the childrenDo:
   walk was added).
3. **reflecting flag is NOT copied in CM adoption** (plan §7 said copy): its
   steady state is true and a mid-application false belongs to the OLD
   fragment's handler epilogue; copying false would leave nobody to restore it
   and swallow one event. Origin tags (isSyncOrigin:) cover in-flight echo
   fallout. Documented at the CM updateVisualsFromSameKind: override.
4. **retire:at:in: (lazy-list scroll windowing) deliberately does NOT dispose**:
   scroll-driven, client-local, not a synced position. Commented in base.
5. DropDownMenuFragment adopts `dropDownMenuId` in addition to the shared
   identity (its publishes carry that id, not fragmentId).
6. Converted leaves: Button, ImageButton, Checkbox, RadioButton, Hyperlink,
   HyperlinkImage, ToggleComposer, TextEditor, CodeMirror, Picker, ColorPicker,
   DatePicker, TimePicker, Slider, DropDownMenu. Untouched by design:
   FileChooser + MediaCreator (domain-keyed), Timer (non-generational), Menu
   (not a Fragment — still leaks one subscription set per menu open; open
   item), HopscotchShell (window-lifetime).

Verified (psoup, headless, fresh sessions):
- eval-probe5: w1/w2/m1 ALL complete with the plain 2.5s flow (no reselect
  hack); registry steady after first eval (one generation per live visual;
  previously +6 codemirror/+4 button/+12 imagebutton keys PER EVAL); the
  select-all is the last selection before the click (no stale echo pair); 19/19
  events; no JS errors.
- latejoin-probe: A nav→eval→back (workspace lineages retired)→nav (revived
  home works)→eval all pass, 15/15; cold joiner B catches up 15/15 in 30s,
  ZERO 'no subscriber' skips, census identical to A, sees the result.
- Typechecker suite 275/275 throughout; pretty-print/round-trip/parse-validate
  clean on all three .ns files.

Not yet run: NS2JS half (CroquetJSIDE-TEST deploy takes ~25min; the deploy
driver lived in the reboot-wiped scratchpad), liveview-edit and
transclusion/timer/random determinism suites (same — need reconstruction from
their session summaries). Stock out/ vfuels still pre-change; stock
croquetpsoup.js already carries nsUnsubscribe (additive, inert for old vfuels).

## 9. Follow-through (2026-09-03)

COMMITTED after Gilad's interactive pass: newspeak master c973a10 (base
disposal + CM selection-handler fix) + f68667c (Croquet lifecycle, glue
mirror, plan doc, probe harness); psoup extraRevs 257f085 (nsUnsubscribe);
webide-ai-access merged master (24c843a). Only my hunks were staged in
HopscotchForHTML5.ns - another session's uncommitted work (navigator
registerNewPresenter rework, AI model picker; also AIAccess.ns,
AI_IDE_Support.ns, Documents.ns) was left untouched.

NS2JS half VERIFIED: deploy driver reconstructed
(croquet-probes/deploy-driver2.js - packages a Croquet JS IDE deploy from a
headless plain psoup IDE via a workspace doIt, ~25s with
--disable-background-timer-throttling, artifacts renamed to
CroquetJSIDE-TEST.*). eval-probe5 js and latejoin-probe js both FULL PASS,
censuses and scoped ids identical to psoup.

typing-test.js (reconstruction of the liveview test's risky core): 9KB
buffer over the detour, 6 chars typed under echo pressure - A==B
convergence PASS, focus held, registry steady at 6 CM keys, syncRandom
draw agrees across clients. Some typed chars interleave with delayed
full-text echoes: the KNOWN PARKED fast-typing race (rate budget), not a
regression - the identity machinery is idle during typing (no
reconciliation; registry constant). A stock-baseline A/B run failed
environmentally (stock vfuel likely stale vs committed state).

MENU LEAK FIXED (uncommitted, awaiting Gilad's IDE pass): Menu gains
public retire; DropDownMenuFragment holds currentMenu (adopted through
same-kind transfer), retires the previous menu inside the synchronized
open (updateContent) and at noticeDisposal. menu-probe.js: 3 synced opens
=> exactly 1 nsmenu_ key throughout (was +1 per open). eval-probe5 +
latejoin-probe re-PASS on the rebuilt TEST vfuel; typechecker 275/275.

Still unreconstructed from the reboot: transclusion/timer determinism
suites and the full document-liveview test (croquet-liveview-edit-test).
NS2JS deploy predates the menu fix (platform-neutral; re-package via
deploy-driver2.js when wanted). Stage-ii retarget-cell migration remains
deferred until the explicit unsub/resub has soaked.
