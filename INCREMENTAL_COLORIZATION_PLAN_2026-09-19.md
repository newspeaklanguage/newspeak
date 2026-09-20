# Incremental colorization — implementation plan

2026-09-19. Written at Gilad's request after the typing-cost measurements in
`SESSION_SUMMARY_2026-09-19_PROBES_AND_TYPING_COST.md`. Cause 1 (unbounded
editor height defeating CodeMirror's viewport virtualization) is **deferred** —
it forces a decision about how nested presenters scroll and resize. This plan is
Cause 2 only, and is worth doing on its own.

## 1. What the measurements say

`croquet-probes/editor-cost-decompose-probe.js`, plain IDE, **no Croquet**,
workspace code editor holding 307266 characters (3704 colorized tokens), 12 real
keystrokes per state, warm-up run discarded:

| state | per key | markText/key |
|---|---|---|
| A  as shipped (unbounded height) | 1269 ms | 3704 |
| **A2 as shipped, colorizing handlers detached** | **155 ms** | **0** |
| B  bounded height + colorizing | 708 ms | 3704 |
| D  bounded height, handlers detached | 29 ms | 0 |
| BARE  fresh CodeMirror, same page | 36 ms | 0 |

**Colorizing costs 1114 ms per keystroke: 88% of the total, in the configuration
that ships today.** Fixing it alone is 1269 -> 155 ms/key, **8.2x**, without
touching cause 1.

The two causes are **not additive, they multiply.** The viewport tax is only
126 ms/key on its own (155 - 29) but 561 ms/key in colorizing's presence
(1269 - 708), because each of the 3704 `markText` calls pays the
unbounded-editor penalty. That is why colorizing should be fixed first even
though cause 1 was, in isolation, measured as the larger single factor: most of
cause 1's damage is inflicted *through* colorizing.

An earlier reading in the same session quoted 57%/36% from the bounded C->D
step. That understates colorizing in the shipped configuration; the A->A2 step
above is the number to plan against.

## 2. What happens today, exactly

Per keystroke, in every code editor (workspace evaluator, method editor, class
editor — **not** Ampleforth documents, which are not colorized at all):

1. `EvaluatorPresenter>>changeResponse` (Browsing.ns) picks
   `liveChangeResponse` or `deadChangeResponse`. **Both colorize**, so turning
   Live Evaluation off does not avoid any of this.
2. Either calls
   `ide colorizer colorizeDoIt: src fromClass: nil via: (colorizingBlockFor: editor)`.
3. `Browsing>>colorizingBlockFor: cm` (Browsing.ns:8728) sends `cm resetStyles`
   and returns a block that, **per range**, allocates a fresh `JSObject`, sets
   `css` from `cssFor: r kind`, and sends `cm style:from:to:`.
4. `NS3BrowserColorizer>>colorizeString:withProduction:via:`
   (NewspeakColorization.ns) parses the **whole** string with the combinatorial
   parser, accumulating ranges through `noteRange:from:to:` into `rangeMap`; a
   parse error notes `#error` from the failure position to `inputSize`.
5. `feedRangesTo:` calls `consolidateRanges` — `rangeMap asArray`, a **sort** of
   all ranges, then a pairwise overlap merge/truncate — then sends the block
   once per surviving range.
6. `CodeMirrorFragment>>resetStyles` sets `resetPending`, empties the queue, and
   queues one default-style range covering the whole text.
7. `style:from:to:` appends to `styles` and calls `scheduleStyling`.
8. `applyStyles` runs in a promise turn: one `startOperation`; if
   `resetPending`, **clear every marker from the previous pass**; then per
   queued style `applyStyle:` = two `posFromIndex` sends plus one `markText`;
   `endOperation`.

At 300KB that is, per keystroke: one full parse, one sort of 3704 elements,
3704 `JSObject` allocations and alien crossings, 3704 marker clears, 7408
`posFromIndex` sends and 3704 `markText` calls — **all to redraw colours that
are identical everywhere except within a token or two of the caret.**

## 3. Plan

Four stages. Each is independently shippable, independently measurable, and
ordered by benefit per unit of risk. Stages 0 and 1 together are expected to
capture most of the 8.2x; 2 and 3 exist to make the settle pass cheap enough
that it is not felt.

### Stage 0 — stop allocating a style object per range (trivial)

`colorizingBlockFor:` builds `JSObject new` for every range on every pass. There
are on the order of twenty distinct kinds. Cache one JSObject per kind in a Map
held by the Browsing module (a **lazy** slot — an eagerly-initialized slot added
to a live module crashes on hot-load) and hand out the shared one.

- Touches: `Browsing>>colorizingBlockFor:`, plus one lazy slot.
- Removes 3704 allocations and 3704 alien crossings per pass.
- No behaviour change: the objects are read-only style descriptors.
- Risk: none beyond confirming nothing mutates the style object downstream.
  `applyStyle:` only passes it to `markText`.

### Stage 1 — do not colorize on every keystroke (the big, cheap win)

Colorizing is cosmetic. It should run when typing pauses, not per character.

- Add to `CodeMirrorFragment` a coalescing `scheduleColorizing`, mirroring the
  existing `scheduleStyling` pair: a bare `colorizingScheduled <Boolean>` slot
  and a `colorizeGeneration <Integer>` slot (**bare, nil-tolerant**, following
  the deliberate precedent documented at HopscotchForHTML5.ns:781 so instances
  that predate a hot-load behave).
- The change responses call `editor scheduleColorizing: [ ... colorizeDoIt: ... ]`
  instead of colorizing inline.
- Delay: 120-200ms of idle. Unlike `scheduleStyling`, this one genuinely needs a
  delay, so it uses a timer rather than a promise turn. **That is safe here
  precisely because it is cosmetic**: on an unpainted page timers are throttled
  to 1/s and then 1/min, which merely postpones colours on a page nobody is
  looking at. Do not use this pattern for anything a page depends on.
- Colorize immediately, cancelling any pending pass, on accept, on blur and on
  Escape, so a settled editor is never left half-coloured.
- **Croquet:** nothing here is recorded or published. `applyStyles` only marks;
  it never touches document text. A client-local timer therefore cannot cause
  divergence. Verify by running the determinism suite before and after, and by
  confirming no new call reaches a `publish:`.
- Expected: during a burst, 1269 -> ~155 ms/key. One ~1114 ms pass after the
  pause, which at 300KB is still a visible hitch — hence stages 2 and 3.

### Stage 2 — reuse markers instead of clearing and re-marking

The colours produced by two consecutive passes are identical except near the
edit. CodeMirror's `TextMarker`s **move with the text automatically**, so the
previous pass's markers are still in the right places after a small edit.

- Alongside `styleMarks`, keep `appliedStyles`: the list of `{start. end. kind}`
  triples that produced them, in the same order.
- Change the fragment's styling API to carry the **kind symbol** rather than an
  opaque JSObject (`style:from:to:` gains a kind, or is replaced by
  `styleKind:from:to:`), so comparison is symbol identity and integer equality
  and no JSObject need be built for an unchanged range. This composes with
  stage 0.
- In `applyStyles`, instead of clearing everything:
  1. Compute the longest common **prefix** of the new and stored triple lists,
     comparing `(start, end, kind)` directly — ranges before the edit are
     unmoved.
  2. Compute the longest common **suffix**, comparing the stored triple shifted
     by `delta = newTextSize - oldTextSize` — ranges after the edit moved by
     exactly the edit's length change.
  3. Clear only the markers in the differing middle; mark only the differing
     middle's new triples; splice `styleMarks` and `appliedStyles` accordingly.
- For a one-character edit this is O(n) **integer** comparisons with no DOM
  access at all, and about two `markText` calls, against 3704 clears + 7408
  `posFromIndex` + 3704 `markText` today.
- Edge cases to handle explicitly:
  - A parse error notes `#error` to end-of-text, so the suffix legitimately
    differs and the tail is re-marked. Correct, and self-limiting.
  - `resetStyles` must stop unconditionally clearing; it should instead mark the
    pass as "full" only when the fragment has no `appliedStyles` (first pass,
    after adoption from a fragment that had none, or after `setValue`).
  - `updateVisualsFromSameKind:` already hands `styleMarks` over
    (HopscotchForHTML5.ns:1070); it must hand `appliedStyles` over with it, or
    the next pass will diff against nothing and do a full re-mark — correct but
    slow, so this is a performance bug, not a correctness one.
- Risk: moderate, and contained in `CodeMirrorFragment` plus the one-line
  protocol change in `colorizingBlockFor:`.

### Stage 3 — make the parse itself incremental (only if still needed)

After stages 0-2 the remaining per-pass cost is the combinatorial parse, the
sort in `consolidateRanges`, and building the range list. Do this stage only if
the settle pass is still felt; measure first.

Two cheap non-incremental wins to take first, since they need no new machinery:

- `consolidateRanges` sorts every range on every pass. Ranges are largely
  produced in source order; either insert in order in `noteRange:from:to:` or
  detect the already-sorted case, and the sort disappears.
- Skip the pass entirely when the text is unchanged (re-render, refocus,
  adoption). Cheap identity/size guard.

Then, genuine incrementality:

- Find the smallest **safe re-parse region** around the edit with a cheap
  lexical prescan (far cheaper than the parser): scan back to a statement
  boundary — a `.` at bracket depth zero, outside any string or comment — and
  forward to the next one.
- Re-parse only that region with the corresponding sub-production, with ranges
  returned in absolute coordinates (`setString:` would need an offset, or the
  caller shifts them).
- Splice: replace the stored ranges inside the region and shift every later
  stored range by the delta. Feed the result to stage 2's differ, which will
  then re-mark only what genuinely changed.
- **Fall back to a full parse** whenever the prescan cannot prove safety: the
  edit touches a comment or string delimiter, bracket depth does not balance
  across the region, or the edit inserts a `.`. Conservative fallback is the
  whole correctness argument; it must be the default on any doubt.
- Risk: high. It is the only stage that touches `NewspeakColorization` and the
  grammar, and a wrong safe-region calculation produces *wrong colours*, which
  are visible but harmless — still, it needs the equivalence test below.

### The alternative shape, for the record

The idiomatic CodeMirror answer is a **mode**: CodeMirror tokenizes lazily, only
for rendered lines, with incremental per-line state, and no `markText` at all.
That would make colorizing O(visible lines) instead of O(document), and it
composes with cause 1 — fix the height and a mode colorizes twenty lines
regardless of document size.

Against it: it duplicates Newspeak's lexical layer in a second place, and the
parser-derived kinds (`messagePatternDecl`, types, modifiers, `#error`) are not
lexical, so they would still need an occasional overlay pass. It is the right
long-term shape and the wrong next step; stages 0-2 get most of the benefit for
a fraction of the work and leave this option open.

## 4. Verification

- **Performance:** `croquet-probes/editor-cost-decompose-probe.js` already
  prints per-key median and `markText/key`; states A and A2 bracket the target
  (1269 -> 155). Run at 300KB and at a realistic size (a large class, ~30-60KB).
  Success for stages 0-1 is per-key cost during a burst approaching A2.
- **Correctness (new, needed before stage 2 ships):** a colorization
  equivalence probe. Colorize a text from scratch; then apply a scripted
  sequence of edits with incremental colorizing on; then force a full re-colorize
  and compare the resulting marker set (positions and kinds) with the
  incremental one. They must be identical after every edit. This is the only
  thing that will catch a wrong diff or a wrong safe region, and it is cheap to
  run in the plain IDE with one browser.
- **Gates, per the standing rules:** parse-validate *before* pretty-print on
  every `.ns` touched, then pretty-print, round-trip-check, parse-validate
  again, then `./run-tests.sh NewspeakTypecheckerTestingConfiguration`
  (275/275 today).
- **Hot-load:** all of stages 0-2 are method-only plus **bare** slots, so they
  hot-load; no rebuild, no glue change, no `DeploymentManager` regeneration. No
  class is re-parented.
- **Croquet:** run the determinism suite and `typing-test` after stage 1 to
  confirm the timer changed nothing recorded.

## 5. Blast radius

`colorizingBlockFor:` is the single funnel — Browsing.ns has ten call sites of
`via: (colorizingBlockFor: ...)` and they all route through it, so the protocol
change in stage 2 is one method plus `CodeMirrorFragment`. The change responses
that need stage 1's scheduling are `deadChangeResponse` and `liveChangeResponse`
plus the equivalent change blocks for method and class editors; they should all
be routed through one helper rather than edited individually.

**Ampleforth documents are unaffected throughout.** They are not colorized
(measured: `markText/key = 0`, `croquet-probes/document-cost-probe.js`), and
their live view types at 33-35 ms/key at 80KB today.

## 6. Recommended first step

Stages 0 and 1 together: one lazy Map, one coalescing scheduler, and routing the
change responses through it. Method-only, hot-loadable, no grammar work, no
Croquet exposure, and expected to take a 300KB editor from 1269 to roughly
155 ms/key while typing. Measure with the decompose probe before and after, then
decide whether the settle pass justifies stage 2.
