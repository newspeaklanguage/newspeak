# Session summary 2026-09-19: the document sync probe lands; typing cost is measured and is not where we thought

Read this first when resuming. Previous record:
`SESSION_SUMMARY_2026-09-18_to_19_CROQUET_EDITOR_DIFF_SYNC.md`, whose "Still
owed" list this session worked down.

**Nothing is committed.** All changes are new probe files plus one untracked
build script; no `.ns` file was modified. The typechecker suite was green at
session start (275/275) and no production code changed, so it is still green.

## 1. ampleforth-sync-probe.js is finished, and proven against the bug (item (a))

The probe existed but could not navigate to a document, so its assertions had
never run. Its header recorded the conclusion that **no evaluated expression
could ever navigate** — that a hook had to be click-triggered from a presenter,
because the verb is on neither the Workspace model nor `ide`.

That was wrong. `Browsing>>navigateTo: aSubject` is public and does exactly
this; it was added for the AI tools, which have no presenter either.
`AI_IDE_Support.ns:1678` already drives a document with the same shape. One
workspace evaluation is enough, with **no production code at all**:

```
ide browsing navigateTo: (ide documents DocumentSubject onModel:
    (ide documents freshDocumentNamed: #ProbeDoc initialText: 'Probe body.'))
```

Use `DocumentSubject`, not `TwoViewEditorSubject`: its presenter is
`DocumentPresenter`, which holds the `TwoViewEditorPresenter` in a
`twoViewEditor` slot and is what the IDE itself shows. A bare
`TwoViewEditorSubject` renders a live view through a presenter no IDE path
builds, so a break in the IDE's own wrapper would go unseen.

**The lesson worth keeping:** when a verb seems missing, check the module
objects hanging off `ide` (`ide browsing`, `ide documents`, `ide debugging`)
before concluding it does not exist.

### The negative control — the part that makes the probe worth anything

A green probe proves nothing on its own. `tool/build-bugged-test-vfuel.sh`
(new) stages the tree exactly as `tool/build-croquet-test-vfuel.sh`
does, `sed`s the fix out of the **staged copy only** (the working tree is never
touched — Gilad's IDE saves land there), and compiles
`out/CroquetHopscotchWebIDE-BUG.vfuel`. The script aborts unless the pattern it
removes matches exactly once, so a moved fix cannot silently yield a snapshot
identical to the good one. The probe takes `NS_SNAPSHOT` so the control needs
no edit.

| | fixed build | bugged build |
|---|---|---|
| events recorded | 9 -> 15 | **3 -> 3, flat** |
| B receives the text | 12 of 12 | **0 of 12** |
| live views agree | yes | **no** |
| divergence alarm | 0 | **0 — still silent** |
| console errors | 0 | **0** |

The bugged column is the direct demonstration of why `9141e50` survived a week:
nothing was published, the divergence alarm only fires for events that WERE
recorded, and nothing was logged. This probe is the only thing that sees it.

## 2. The shadow "leak" is not a leak (item (b))

Recorded previously as "the one known defect shipped knowingly — one
`CodeMirror.Doc` per editor ever built", worst case an Ampleforth document
because it "rebuilds editors continuously". **Measured, that does not happen.**
`croquet-probes/shadow-census-probe.js` (new) reads `nsShadows.size` at each
step:

| step | shadows |
|---|---|
| home, before anything | 0 |
| document open | 3 |
| after 6 rounds x 10 keystrokes in the live view | 3, 3, 3, 3, 3, 3 |
| 3 x (home -> history -> **same** document again) | 3, 3, 3 |

**0 growth for 60 keystrokes; 0 growth per away-and-back trip.** A live-view
rebuild mints no shadow, because `adoptCroquetIdentityFrom:` keeps the
lineage's id and drops the adopter's own pre-adoption shadow. What does add
shadows is a genuinely new editor lineage (a fresh document costs about 2). The
true bound is one Doc per distinct lineage ever shown — an unevicted cache, not
a runaway heap. **Priority: much lower than recorded.**

A trap worth recording: re-entering the document by evaluating
`freshDocumentNamed:` again makes a NEW document with NEW editors, and counting
those as leaked shadows measures nothing. The probe reported a confident "~2
per visit" until re-entry went through the history page instead.

**If eviction is ever added it must be keyed on event position, not wall
clock.** The shadow is the deterministic text source (`textBeingAccepted`
answers it whenever one exists), so a client that swept while another had not
would answer from its visible editor while the other answered the shadow — a
divergence manufactured by the cleanup itself. `echoDeadline` may use the local
clock only because it governs visible-editor decisions only. Use
`theModel.newspeakEvents.length`, which every client replays identically.

## 3. Concurrent typing converges (item 3 of the old list)

`croquet-probes/concurrent-typing-probe.js` already existed (written after that
list was drafted) and had never been run. It passes, and does better than the
design promises: not just convergence but intention preservation.

```
A: "first line:aaaa...(30)\nmiddle line\nlast line:bbbb...(30)"
B: identical
PASS visible editors converge | no character lost (30 a, 30 b)
PASS shadows identical on both | visible editor == its shadow (A and B)
PASS no divergence reported
```

This is the only exercise of the dirty/resync path.

## 4. The 300KB runs, and what they actually say (items (c) and (d))

### The diff-sync did its job

At 307268 characters, 20 typed characters produced **5 events, 0 detoured**
(0.25 events/char). The >8KB Data-API detour that cost ~1s per payload and was
strictly FIFO is gone, at 300KB, which is what the whole diff-sync effort
existed for. No character lost, order preserved, no divergence, no errors.

### But the latency bound still fails, and styling is only part of the cost

`BOUND_MS=1500`: FAIL at every configuration tried.

| 300KB, N=20 | styling on | styling stubbed | saved |
|---|---|---|---|
| median latency to B | 9236 ms | 5155 ms | 44% |
| max | 11235 ms | 8460 ms | 25% |
| A event-loop lag, median | 3065 ms | 2440 ms | 20% |

`markText` ran **18520 times for 20 characters** — 926 per keystroke, one full
re-mark of all 3704 tokens per change event, scaling linearly with document
size. So incremental re-marking (item (c)) is real and worth ~44%, but it
**cannot reach the bound**: with marking entirely free the median is still
5.2s, 3.4x over.

### Where the rest goes — SUPERSEDED, read the addendum

> **This subsection's conclusion is wrong.** It reads the profile of the
> UNFIXED editor, where the viewport cost dominates and hides the colorizer.
> Once the editor height is bounded, `newspeak-vm` goes from 5% to 40-45%
> and the colorizer is the second wall. See the addendum at the end.


CPU profile of the typist with marking stubbed: **codemirror 37%, newspeak-vm
(wasm) 5%**, croquet 8%. The colorizer is Newspeak code, so its whole-document
re-parse is NOT the bottleneck. The hot functions are CodeMirror's own layout
and measurement: `updateHeightsInViewport`, `iterN`, `makeChangeInner`,
`endOperations`. The journey trace shows A's own editor taking ~580 ms per
character *before anything is published at all*.

### The control that reframes everything

`typing-cost-control.js SIZE_KB=300 N=20 BARE=1`, one client, **the PLAIN IDE
with no Croquet loaded**, against a bare CodeMirror created on the same page:

| same page, same 300KB, same 20 keys | per key, median | total |
|---|---|---|
| IDE workspace editor (no Croquet at all) | **1593 ms** | 42249 ms |
| bare CodeMirror, outside Hopscotch | **31 ms** | 2719 ms |

**51x, with Croquet not even in the picture.** CPU: the IDE case is codemirror
58% / newspeak-vm 13%, dominated by `updateHeightsInViewport` (3634 ms),
`iterN` (3062 ms), `findViewIndex` (1510 ms); bare CodeMirror is 53% idle and
barely touches them (90 ms, 129 ms).

**Conclusion.** Neither Croquet, nor the shadow machinery, nor the colorizer is
what makes a large editor slow. Something Hopscotch/the IDE does around the
editor forces CodeMirror to re-measure its viewport on every keystroke, and
that is worth 51x — far more than everything the last two sessions optimized
put together. The per-token `editor refresh` was already removed (the probe
reports `refresh: 0`), so this is a different trigger; candidates worth checking
first are the reactive re-render of the editor's container on each change
(`updateGUI:`) and the `autorefresh` CodeMirror addon that the document shell
loads.

**Recommendation: do not build incremental re-marking next.** It is the smaller
half of a problem whose larger half is not in the sync layer at all. Find the
per-keystroke re-measurement first; a 51x floor makes the 44% moot.

## What is left

1. **Find what makes the IDE's CodeMirror re-measure per keystroke** (new, and
   now the top item). Reproduce with `typing-cost-control.js` — it needs no
   Croquet, no reflector and one browser, so it is a fast loop.
2. Incremental re-marking (item (c)) — real, worth ~44%, but only after 1.
3. `cm-steps-probe` on the JS deploy (item (d), the only part not done).
4. Shadow eviction — low priority per section 2; event-position keyed if ever.
5. The finished `ampleforth-sync-probe.js` should join whatever suite runs
   routinely; it is the only document-level sync coverage there is.

## New files (all untracked)

| file | what |
|---|---|
| `croquet-probes/ampleforth-sync-probe.js` | finished: navigation + `NS_SNAPSHOT` + corrected header |
| `croquet-probes/shadow-census-probe.js` | new: shadow retention census |
| `tool/build-bugged-test-vfuel.sh` | new: negative-control vfuel builder |
| `scratch/*.out` | probe transcripts quoted above |

---

# ADDENDUM: the source of the remaining performance problem, found

> Scope: everything below is the WORKSPACE CODE EDITOR. For what applies to
> Ampleforth documents (cause 2 does not), see the scoping correction at the end.
>
> **The 57%/36% split below is superseded.** It was computed from the BOUNDED
> C->D step. Measured in the SHIPPED (unbounded) configuration, colorizing is
> 1114 ms/key of 1269 - **88%** - and fixing it alone is 8.2x. The two causes
> multiply rather than add: the viewport tax is 126 ms/key alone but 561 ms/key
> in colorizing's presence, because each of the 3704 markText calls pays it.
> See `INCREMENTAL_COLORIZATION_PLAN_2026-09-19.md` section 1.

`croquet-probes/editor-viewport-probe.js` and
`croquet-probes/editor-cost-decompose-probe.js` (both new). Plain IDE, **no
Croquet, no reflector, one browser**, 307266 characters, one editor, one
difference peeled off at a time, with a discarded warm-up run first:

| state | per key | markText/key | CPU buckets |
|---|---|---|---|
| A  as the IDE builds it | 1389 ms | 3704 | codemirror 53%, (program) 17%, newspeak-vm 15% |
| B  + bounded height, native scrollbars | 604 ms | 3704 | **newspeak-vm 40%**, codemirror 39% |
| C  + lineWrapping off | 521 ms | 3704 | newspeak-vm 45%, codemirror 38% |
| D  + our change handlers detached | **16 ms** | **0** | idle 54%, codemirror 10% |
| BARE  fresh CodeMirror, same page, same text | 30 ms | 0 | idle 41% |

**There are two causes, not one, and they are of the same order.**

## Cause 1: every editor renders its whole document (57% of the cost)

`CodeMirrorFragment>>createVisual` sets `scrollbarStyle: 'null'` and then forces
the wrapper's height to `'unset'`, so the editor grows to fit its content inside
the Hopscotch flow layout. CodeMirror can only virtualize its viewport when it
has a scroller to virtualize inside, so with no bounded height it renders and
re-measures **every line**. Measured directly:

| | rendered line views | DOM line elements | wrapper height |
|---|---|---|---|
| as built | **3703** | 3703 | **125893 px** |
| bounded to 500px | **19** | 20 | 500 px |

That is the whole document in the DOM, and it is why
`updateHeightsInViewport`, `iterN` and `findViewIndex` dominate the profile.
Bounding the height alone: 1389 -> 604 ms/key.

**This is a design question, not just a bug:** the IDE deliberately lets editors
grow so the page scrolls rather than the editor. Fixing it means either giving
large editors a bounded height with their own scroller, or capping the rendered
viewport some other way. Gilad's call.

## Cause 2: the whole document is re-colorized on every keystroke (36%)

`markText/key = 3704` in states A, B and C - one full re-mark of all 3704 tokens
**per keystroke** - and 0 once our handlers are off. Detaching the handlers is
worth 505 ms/key and lands at 16 ms, at or below the bare floor.

Note what state B did to the profile: with the viewport cost removed,
`newspeak-vm` jumps from 15% to 40-45%. The colorizer was never cheap; in state
A it was simply hidden behind the viewport cost. **An earlier reading in this
same session ("newspeak-vm 5%, so the colorizer is not the bottleneck") was
drawn from the unfixed state and was wrong** - it measured what the colorizer
costs while something worse dominates.

So the colorizing pass is the second wall, and it has two halves of comparable
size: the Newspeak-side parse and range computation (the `newspeak-vm` bucket)
and the 3704 `markText` calls (part of the `codemirror` bucket). Item (c),
incremental re-marking, is the second half only.

Under Croquet the per-keystroke cost is masked by the 80ms coalescing window -
20 characters produced 5 change events, so 926 markText per keystroke rather
than 3704 - which is why the plain IDE is the better rig for this work.

## What this means for the plan

1389 -> 16 ms is **87x**, and reconciles with the 51x the control first
reported. Both fixes are needed; either alone leaves a wall:

- height bounded, colorizer untouched -> 604 ms/key
- colorizer fixed, height untouched -> ~885 ms/key (1389 - 505)

Neither is in the sync layer, the shadow machinery or Croquet, none of which
this session found to be at fault anywhere.

**Suggested order.** Cause 2 first: it is pure optimization with no UX
consequence, and it is the one already on the list. Do it as incremental
*colorizing* (re-colorize only the changed region), which gets the `markText`
half for free, rather than as incremental re-marking alone. Then Cause 1, which
needs a decision about how large editors scroll.

`editor-cost-decompose-probe.js` is the measurement rig for both: one browser,
no Croquet, ~4 minutes, and it prints the whole table above.

## SCOPING CORRECTION: which "document"?

Gilad asked what "document" meant above, since **Ampleforth documents are not
colorized**. He is right, and the distinction narrows the result.

**Everything in the addendum was measured on the WORKSPACE CODE EDITOR.** The
probe clicks `Workspaces` and fills that CodeMirror with 300KB of Newspeak
comment lines; "document" there meant the editor's text buffer, in CodeMirror's
sense, not an Ampleforth document.

`croquet-probes/document-cost-probe.js` (new) measures an actual Ampleforth
document instead — plain IDE, no Croquet, a document whose body is built in
Newspeak by doubling a paragraph, with `markText` hooked on every editor on the
page so "is anything colorized here" is counted, not assumed:

| | per key | markText/key |
|---|---|---|
| Ampleforth LIVE view, body 90112 chars (live text 79870) | **33-35 ms** (p90 45-73) | **0** |
| workspace code editor, 300KB | 1389 ms | 3704 |

So:

- **Cause 2 (whole buffer re-colorized per keystroke) does not apply to
  Ampleforth documents at all.** Measured `markText/key = 0`: nothing colorizes
  them. It is a CODE-EDITOR problem — workspace evaluator, method and class
  editors — which is also where the original complaint came from (typing in a
  large class under Croquet).
- **Typing in a document's live view is interactive at ~80KB**: 33-35 ms/key,
  about the bare-CodeMirror floor, with the whole `updater` ->
  `scrubbedLiveViewSource` -> `updateFromRawView` pipeline running per
  keystroke. Not a problem at this size.

**Cause 1 does apply to a document's RAW view, on code grounds, but was NOT
measured.** `scrollbarStyle: 'null'` occurs in exactly one place, the single
`CodeMirrorFragment>>createVisual` (HopscotchForHTML5.ns:1211), which also
forces the wrapper height to `'unset'`; `Documents.ns:501` sets only the raw
view's WIDTH (`cm editor setSize: '40em'`). So every editor in the system is
built unbounded-height, the raw view included. The probe could not verify it
live: the document page opens with no CodeMirror present, the raw view is
behind editing chrome that renders as untitled image buttons, and neither a
text match on 'Toggle Raw HTML' nor a tooltip match on 'Edit' found a control
(the page's only text control is the title, and the only tooltips are the
toolbar's). **Exposing the raw view from a probe is unfinished work.**

Net effect on the plan: Cause 2 is worth doing for code editors and is
irrelevant to Ampleforth; Cause 1 is worth doing for both, and is the only one
of the two that touches documents.
