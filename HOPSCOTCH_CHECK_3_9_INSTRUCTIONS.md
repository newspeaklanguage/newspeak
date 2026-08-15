# Check 3.9 — a column whose first row has no height must still virtualize

Standalone procedure for the IDE's AI. Everything needed is here; the wider test
plan is not required.

## What this guards

`LazySequenceComposer` cannot virtualize until it knows a row height. It learns
one in `measureRowHeightIn:`, and until 2026-08-15 that method read the height of
**row 1 only** and gave up permanently if it was zero. A row can legitimately
report zero height — an editor before it sizes itself, an image before it loads —
so any such column silently stopped virtualizing and sat at its 30-row bootstrap
window forever, looking correct while doing none of its work.

The fix was twofold: scan for the first row that *has* a height rather than
trusting row 1, and retry on every observer callback rather than latching
failure. This check confirms both. It is the only guard against that defect
returning.

## Three prohibitions

These are not stylistic. Each one has already produced a false PASS.

1. **Do not call `assumeRowHeight:`, and do not build the column with
   `lazyColumnOfSize:rowHeight:elementAt:`.** Both supply a height directly and
   bypass measurement, which is the entire subject of this check. A column that
   virtualizes because you told it the row height proves nothing.
2. **Do not conclude anything by reading the source.** The defect being guarded
   against lived in code that read correctly to two reviewers. Only observed
   numbers count here.
3. **Do not run this on a column that is not laid out.** Off-screen every row
   reports `offsetHeight = 0`, including the ones that should have a height, so
   the measurement cannot distinguish the case it exists to handle. There is a
   mandatory gate below that detects this.

**NOT RUN is a correct and welcome outcome.** If the preconditions cannot be
met, say so and stop. A PASS you cannot support with observed numbers is worse
than no result, because it retires a guard that is still needed.

## Setup

Build **two** lazy columns of 5000 rows in one live Ampleforth document. They are
identical except for row 1, and that difference is the whole experiment.

- **Column A (the subject).** Row 1 is a fragment guaranteed to occupy no
  vertical space; rows 2..5000 are labels.

  ```
  lazyColumnOfSize: 5000 elementAt: [:i <Integer> |
      i = 1
          ifTrue: [ html: '<div style="height:0;margin:0;padding:0;border:0"></div>' ]
          ifFalse: [ label: i printString ] ]
  ```

  A literal zero-height div is used rather than a `codeMirror:` because it is
  deterministic. A real editor is the motivating case but its height depends on
  when CodeMirror sizes itself, which would make a failure ambiguous.

- **Column B (the control).** Identical, but row 1 is `label: '1'` like every
  other row, so every row has a height.

  ```
  lazyColumnOfSize: 5000 elementAt: [:i <Integer> | label: i printString ]
  ```

Put both in the same document so they share layout conditions, and navigate to
it so they are genuinely rendered.

## Finding the live composer

An amplet expression is evaluated about four times per render and only one of the
resulting fragments is inserted. Reading the wrong one gives `measured=false`
and no observers — indistinguishable from the bug. So:

1. Have the amplet expression append every composer it creates to a Root-visible
   collection.
2. Pick the one whose `visual` answers `isConnected` true.
3. Confirm your choice before using it: stamp it with
   `(theComposer visual) at: 'nsProbe' put: 3939`, then verify the node actually
   on screen carries `nsProbe = 3939`. If it does not, you are holding an orphan
   — find the right one before going further.

Do not navigate away at any point after this. Navigation detaches the DOM and
every subsequent reading describes a corpse.

## Mandatory precondition gate

Before judging anything, prove the experiment is capable of producing a result.
On **column A**, read the realized rows' heights:

```
(rowOne visual) at: 'offsetHeight'      "expect 0"
(rowTwo visual) at: 'offsetHeight'      "expect > 0"
```

- Row 1 must be **0**. If it is not, the zero-height row is not zero-height and
  the check is not exercising anything — report NOT RUN.
- Row 2 must be **greater than 0**. If it is 0, the column is not laid out —
  report NOT RUN. This is the failure both previous attempts hit.

Only if both hold does anything below mean anything.

## The check

**Step 1 — measurement.** Read on both columns:

```
theComposer measured
theComposer rowHeight
```

- **Column B must report `measured = true` and `rowHeight > 0`.** It is the
  control: if the control fails, measurement is broken generally and this check
  cannot say anything about row-1 handling. Report NOT RUN.
- **Column A must report `measured = true` and the same `rowHeight` as column
  B.** This is the check. Column A's row 1 has no height, so a passing result
  means measurement looked past it to a row that did.

**Column A reporting `measured = false` and `rowHeight = 0` while column B
reports a height is the defect, and is a FAIL.**

**Step 2 — the window advances.** On column A, record `firstShown` and
`lastShown`, scroll the page a few thousand pixels, then — **in a separate
evaluation**, because `IntersectionObserver` fires asynchronously and a read in
the same call sees the pre-scroll state — read them again.

Pass: both increased, and `((theComposer visual) at: 'children') at: 'length'`
is still under 200.

Fail: the window is unchanged and still at `firstShown = 1, lastShown = 30`. That
is the bootstrap window, and a column stuck there is not virtualizing.

## Verdict

- **PASS** — the gate held, column B measured, column A measured to the same
  height, and column A's window advanced on scroll.
- **FAIL** — the gate held and column B measured, but column A did not measure,
  or measured but did not advance.
- **NOT RUN** — any precondition failed: row 1 was not zero-height, row 2 had no
  height, the control did not measure, or no connected composer could be found.

## Reporting

Give the observed numbers, not a narrative: row 1 and row 2 `offsetHeight`;
`measured` and `rowHeight` for both columns; `firstShown`/`lastShown` before and
after the scroll; children length after. If the verdict is FAIL or NOT RUN, say
which step produced it and what the numbers were at that point.
