# Hopscotch list performance — IDE test plan

A script for the IDE's AI to execute, so the changes can be verified without a
human clicking through them. Every check below states an expression to evaluate
and a **machine-decidable** pass condition — a number, a boolean, an identity —
never "looks right".

The headless suite (`./run-tests.sh HopscotchListPlanningTestingConfiguration
../HopscotchForHTML5.ns`, 24 tests) already covers the pure decision logic:
which elements correspond, which must move, which window to realize. It runs
without a browser and should be green before any of this is attempted. What
remains here is everything that touches a visual, which only a live IDE has.

## How to evaluate protected methods

Several probes call methods that are protected — deliberately, since the
framework's constructors exist to be inherited by presenters, not called from
outside. Two ways in, both available to the IDE AI:

- **Evaluate in the context of an object.** The IDE evaluates a snippet with a
  chosen object as `self`, so an implicit-receiver send reaches protected
  members. Probes marked *(in context of X)* require this.
- **Inherit.** For anything reusable, declare a workspace class inheriting
  `FragmentFactory` and expose what is needed, exactly as
  `HopscotchListPlanningTesting`'s `PlanningProbe` does.

Do **not** make framework members public to make a probe convenient.

## Identity technique

The question "was this DOM node reused or rebuilt?" is the crux of most checks
here, and it is answerable exactly. Stamp a node before the action and read the
stamp after:

```
node at: 'nsProbe' put: 4711.        (* before *)
(node at: 'nsProbe') = 4711          (* after: true iff it is the same node *)
```

Stamp integers, not Newspeak objects — objects do not round-trip reliably across
the alien bridge. Read back only nodes you stamped, so an absent property never
has to be distinguished from a present one.

## Operating notes (learned the hard way, 2026-08-15 run)

Read these before Group 3. Each one cost the previous runner real time.

**An amplet expression is evaluated about four times per render, and only one of
the resulting fragments is the one inserted.** Holding "the" composer from an
amplet gets you an orphan with `measured=false` and no observers, which looks
exactly like a virtualization bug and is not one. Publish *every* instance the
expression creates into a Root-visible collection, then pick the one whose
visual answers `isConnected`. Verify with the stamp technique before trusting
any reading: stamp the composer's `visual`, then confirm the on-screen node
carries the stamp.

**Navigating away from the document detaches its DOM.** Any reading taken after
a navigation describes a corpse. Do a whole scroll-and-read sequence without
touching the browser, and note that scroll and read must be *separate* tool
calls — IntersectionObserver fires asynchronously, so a read in the same call
sees the pre-scroll window.

**A lazy column only virtualizes once it has a row height.** If the sequence's
rows may not report a height on sight (editors, images, async content), build it
with `lazyColumnOfSize:rowHeight:elementAt:` rather than waiting for
measurement — or send `assumeRowHeight:` to a column already built.
`measured=false` with `rowHeight=0` is the signature of a column stuck at its
bootstrap window.

---

## Group 1 — Keyed reconciliation preserves DOM (Part 2)

Keys come from `Fragment>>key`: nil by default, the subject for a `Presenter`,
the tag for a `ToggleComposer` or `TaggedHolderComposer`. Sequences whose
elements do not all answer distinct non-nil keys fall back to the previous
positional behaviour, so both paths need exercising.

**1.1 Insertion at the front reuses every surviving row.**
This is the case that previously rebuilt the entire sequence.

Setup (in context of any Presenter, so the factory methods are in scope):
```
old:: column: {
  (holder: (label: 'a') tag: #a).
  (holder: (label: 'b') tag: #b) }.
oldVisual:: old visual.
(((oldVisual at: 'children') at: 0) at: 'nsProbe') put: 101.
```
Note the row for `#a` is `children[0]`. Stamp `#b`'s row 102 likewise.

Action:
```
new:: column: {
  (holder: (label: 'z') tag: #z).
  (holder: (label: 'a') tag: #a).
  (holder: (label: 'b') tag: #b) }.
new updateVisualsFrom: old.
```

Pass conditions — all must hold:
- `((new visual at: 'children') at: 'length') = 3`
- `(((new visual at: 'children') at: 1) at: 'nsProbe') = 101` — `#a`'s node survived
- `(((new visual at: 'children') at: 2) at: 'nsProbe') = 102` — `#b`'s node survived
- `new visual` is `old visual` (stamp the container too and check)

Before this change the second and third conditions failed: differing lengths
forced a wholesale rebuild.

**1.2 Deletion from the middle keeps the survivors' nodes.**
Old tags `{#a. #b. #c}` stamped 201/202/203, new `{#a. #c}`. Pass: length 2,
stamps 201 and 203 present in that order, and no node carries 202.

**1.3 Reordering moves the minimum.**
Old `{#a. #b. #c}` stamped, new `{#c. #a. #b}`. Pass: length 3, all three stamps
still present, in the new order. The point of the LIS is that only `#c`'s node is
reinserted; that this is *minimal* is covered headlessly, so here only
correctness of the result is checked.

**1.4 Unkeyed sequences still work.**
`column: {label: 'a'. label: 'b'}` — plain labels answer nil to `key`. Refresh
against a same-length column and confirm the container is the same node and
contents update. This exercises the positional fallback, which most of the IDE
still uses.

**1.5 Duplicate tags decline gracefully.**
Two `collapsed:expanded:` toggles with no `tag:` both key `''`. Refreshing a
column of them must not crash and must not collapse both rows onto one — the
keyed path is expected to decline and positional matching to take over.

## Group 2 — Style writes are skipped when nothing changed (Part 1)

**2.1 Steady-state refresh writes no per-child style.**
Do not time this. Observe it exactly, using the technique the 2026-08-15 runner
invented, which is strictly better than the timing recipe this plan originally
carried: plant sentinel values on a reused node before the refresh and see
whether they survive.

`alignFragment:` writes `flex-grow`, `overflow`, `align-self` and `flex-shrink`.
So on a column of 200 unchanged rows, set a reused row's node to
`flex-grow: '0.5'`, `overflow: 'scroll'`, refresh, and read them back.

- Pass: the sentinels **survive** — the write was correctly skipped.
- **Positive control, required:** repeat with one row's `elasticity` changed. The
  sentinels must then be **overwritten**. Without this, surviving sentinels
  could mean styling is broken outright rather than correctly skipped.

This needs no `master` baseline, which the earlier version did.

**2.2 Changed geometry is still applied.**
Build a column where one row has `elasticity: 1`, refresh with that row changed
to `elasticity: 0`, and confirm `flex-grow` on that row's node changed. This
guards against the optimisation skipping a write it should have made — the one
way Part 1 could be wrong.

## Group 3 — Lazy columns (Part 3)

**3.1 A huge column builds a small DOM.** The headline claim.
```
lc:: lazyColumnOfSize: 100000 elementAt: [:i <Integer> | label: i printString ].
```
Open a presenter whose definition is `lc`, then:
- `lc count` = `100000`
- `((lc visual at: 'children') at: 'length')` < `200`
  (rows plus two spacers; the bootstrap window is 30 and the measured window
  depends on viewport height)
- `lc lastShown` < `200`

Fail condition worth stating explicitly: if children length is ~100002, nothing
is being virtualized.

**3.2 It is fast.** Do **not** build an eager 100000-row column — that risks
hanging the session, and was declined by agreement on the 2026-08-15 run. Time
eager `column:` builds at bounded sizes (2k / 8k / 32k) and report the scaling
curve alongside the lazy build's time. Note that a full verdict needs a `master`
baseline; without one, record the numbers and mark the comparison unmet rather
than inferring a pass.

**3.3 Scrolling advances the window.**
Record `lc firstShown` and `lc lastShown`, scroll the pane to the bottom, and
read them again. Pass: both increased, `lastShown` is at or near `100000`, and
children length is still < 200. This exercises the IntersectionObserver
sentinels and the geometry-derived window together.

**3.4 A jump lands in one step.**
Drag the scrollbar from top to middle in a single motion. Pass: `firstShown` is
near 50000 and the content is correct. This is the check that distinguishes
geometry-derived windowing from incremental extension — the latter would
require many callbacks and would visibly lag.

**3.5 Spacers keep the scrollbar honest.**
With `lc rowHeight` measured, pass:
`(lc leadingSpacer at: 'style') at: 'height'` equals
`((lc firstShown - 1) * lc rowHeight) printString , 'px'`.

**3.6 Pinning protects unaccepted edits.** The most important correctness check,
and still **unverified** as of 2026-08-15 — treat it as the top open item.

Build the column with `lazyColumnOfSize:rowHeight:elementAt:`, not by
measurement. The previous
attempt failed here: a column of `codeMirror:` rows never measured (a bare
CodeMirror reports zero height until it sizes itself) and so never virtualized,
which made the check unrunnable. That gap is now fixed — measurement scans for
the first row that has a height and retries on every observer callback — but
declaring the height outright removes the variable entirely, and is what real
code with editor rows should do anyway.

Setup: a lazy column of a few thousand rows, each a `column:` pairing a label
with a `codeMirror:`, built with `assumeRowHeight: 40` (or whatever the row
actually measures). Stage an unaccepted edit by setting the editor fragment's
`isInEditState` — it is a public mutable slot, and it is exactly what
`hasPendingChanges` consults. Confirm before scrolling that the row answers true
to `hasPendingChanges`.

Then scroll far away and back. Pass:
- while scrolled away, that row's index appears in `lc pinnedIndices`
- the pinned fragment still answers true to `hasPendingChanges`
- its visual still exists (pinning detaches the node, it does not destroy it)
- on returning, the row is back in the window with its edit intact

Fail means the pinning protocol is not doing its job, and the feature is not
safe for editable rows.

**3.9 A column whose first row has no height still virtualizes.** Regression
guard for the defect found on 2026-08-15. Build a lazy column of a few thousand
rows where **row 1** is a bare `codeMirror:` (zero height on sight) and later
rows are labels. Scroll. Pass: `measured` becomes true, `rowHeight` > 0, and the
window advances. Fail — `measured=false`, `rowHeight=0`, window stuck at the
bootstrap 30 — means the measurement retry has regressed and any such column
silently stops virtualizing.

**PASSED 2026-08-15**, on the third attempt, following
`HOPSCOTCH_CHECK_3_9_INSTRUCTIONS.md`. Observed: gate held (row 1
`offsetHeight` 0, row 2 16, so the column was genuinely laid out); control
column measured `rowHeight=16`; subject column measured the same 16 despite its
zero-height first row; after scrolling, window at `firstShown=142
lastShown=244` with 105 children. Re-run via those instructions, not from this
summary — the two earlier attempts both produced a false PASS from here, one by
substituting `assumeRowHeight:` and one by reading the source.

**3.7 Rows without state are genuinely discarded.**
Same, with plain label rows: after scrolling away and back,
`lc pinnedFragments size` = 0. If pinning is not rare, the memory advantage is
lost.

**3.8 Refresh preserves the window.**
With the column scrolled into the middle, run `updateGUI: []`. Pass: `firstShown`
and `lastShown` unchanged, children length unchanged, scroll position unchanged.

## Group 4 — The IDE still works (regression)

These cover the paths the change actually touches in anger. The
`TaggedSequenceComposer` change is the riskiest edit in the branch: it now
prefers the inherited keyed reconciler when tags are usable, where before it
detached and reattached every child.

**4.1** Open a class presenter, expand several toggles, edit a method without
accepting, then force a refresh (`updateGUI: []`). Pass: toggles still expanded,
edit still present and unaccepted. This is the invariant the class comment cares
about, and keyed reconciliation is supposed to make it *more* reliable, not less.

**4.2** Navigate back and forward through several presenters. Pass: state
preserved, no exceptions in the console.

**4.3** Open a namespace with many classes, a class with many methods, and the
senders/implementors views. Pass: correct contents; note the timings, since
these are the lists that motivated the work.

**4.4** Open an Ampleforth document containing amplets and a `taggedColumn`.
Pass: renders correctly, amplets still live.

**4.5** Watch the console throughout. A `MessageNotUnderstood` on any of the
branch's new selectors is a fail — it means some fragment class or platform is
missing an implementation:

```
key            mayDerealize          updateVisualsReusingFrom:
reuseMapFor:   reconcileKeyed:with:into:
SequencePlanning >> reuseMapFrom:to:  stationaryIndicesIn:
               windowFor:viewport:rowHeight:count:overscan:
assumeRowHeight:                      lazyColumnOfSize:elementAt:
lazyColumnOf:elementAt:               lazyColumnOfSize:rowHeight:elementAt:
lazyColumnOf:rowHeight:elementAt:
```

Note `insertBefore:before:` is a DOM call through the alien bridge, not a
Newspeak selector — searching implementors for it finds nothing, which is
expected and not a finding. A runtime DNU on it would still be a fail.

## Reporting

For each check: identifier, pass/fail, the observed values, and for timing
checks both the branch and `master` numbers. A fail should carry the expression
evaluated and the actual result, not a narrative.
