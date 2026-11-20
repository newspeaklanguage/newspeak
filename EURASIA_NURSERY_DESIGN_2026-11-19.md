# Eurasia: a nursery for the collector, design

**Date:** 2026-11-19
**Status:** Implemented (section 7), uncommitted.
**Context:** the arena (`EURASIA_ARENA_DESIGN_2026-11-19.md`); the
performance work (`EURASIA_PERFORMANCE_2026-11-19.md`). Decided with Gilad:
the nursery and its write barrier before the compiler, so that compiled
code emits the barrier from the start.

## 1. Why: the IDE's heap

Measured on the IDE packaged for Eurasia (`scripts/ide.sh`), in the browser
pane, with a heap-statistics export added to the web host
(`eurasia_heap_stat`):

| | objects | words | collections |
|---|---:|---:|---:|
| the IDE started | 119K | 0.86M | 0 |
| after opening four inspectors | 925K | 6.6M | 0 |
| after the first collection (the live set) | 264K | 2.0M (16 MB) | 1 |

Full collections on the native build cost about 55 ns per live object and
7 ns per dead one (`gcprobe`, the IDE image: 6 to 8 ms as loaded, 13 to
15 ms after a million dead allocations). A light IDE session therefore
pauses about 20 ms native, about 45 ms in the browser, every four or five
UI actions; a heavier one (0.5 to 1 million live objects: documents, the
debugger, histories) 70 to 130 ms in the browser. Every collection is a
full one, so the pause grows with everything the IDE keeps.

## 2. The nursery is the arena's tail

- **Young** is everything allocated since the last collection: the words
  from `boundary` to the end of the arena (and, likewise, the bytes from
  `byte_boundary` and the codes from `code_boundary`). Everything below is
  old.
- **A minor collection** copies the young objects reachable from the VM's
  roots and the remembered set (below) breadth first (Cheney) into a new
  space, then truncates the arena at `boundary` and appends the copies,
  doing the same for the tails of the byte space and the code table.
  Dead young objects are never visited. Survivors become old (promotion
  on first survival). Old objects are neither marked nor moved. (A first
  version slid the young survivors down, like the full collection; it
  visited every dead young object two or three times, and a minor
  collection of a million dead objects took 9 ms. Copying takes none.)
- **A full collection** is the present one: everything, with the weak and
  ephemeron rules. It runs when the old part has grown by a factor (2) since
  the last full one, and for checkpoints (`collect_keeping_weak`, as now).
- After either, `boundary` is the end of the arena.

## 3. The write barrier and the remembered set

- **Invariant:** every old object that may refer to a young object is in
  the remembered set.
- **Where:** every store of a Value into a heap object goes through
  `Heap`'s API (Step 1 of the arena). The barrier is there:
  - the setters (`set_method_field`, `set_mixin_field`, `set_promise`,
    `set_activation_frame`, `detach_activation`, the promise lists, ...)
    remember an old object they write;
  - the APIs that hand out a mutable slice (`fields_mut`,
    `regular_slots_mut`, `array_elements_mut`, `contents_mut` inside the
    heap) remember an old object before handing it out, whatever is then
    written: a coarse barrier, per object and per access, that needs no
    cooperation from the caller;
  - `set_class` likewise (bootstrap and commit only).
- **Recorded once:** a header bit, `REMEMBERED`, says an object is in the
  set; the barrier is a comparison with `boundary` and a bit test on the
  fast path. The bit comes from the space field (22 bits to 21: two
  million actors).
- **Cleared** at every collection: a minor one empties the set (all
  survivors are old, and nothing young remains); a full one too.
- **Bulk rewrites** (commit's `forward_identities`, `clone_graph`, the
  snapshot reader) work on the whole heap; a commit runs a full
  collection's worth of rewriting anyway, so the simplest correct rule is:
  after a commit the next collection is full.

## 4. Weakness at a minor collection

- A young WeakArray's elements are weak as now.
- An old WeakArray or Ephemeron that refers to a young object has been
  written since the last collection, so it is remembered. At a minor
  collection its references to young objects are treated as in a full
  collection (weak: cleared if the young object dies; an ephemeron's value
  kept only if its key survives), and its references to old objects are
  untouched.
- Old garbage survives a minor collection; old weak references are
  cleared only by full collections. Both are admissible (`gc-semantics.tex`:
  a collection may take any garbage).

## 5. Determinism

When a collection runs, and whether it is minor or full, is decided by
allocation counts and the old part's size, both deterministic, so replay
is unaffected; recorded logs are from this version on.

## 6. Steps and gates

1. The barrier and the remembered set, with `REMEMBERED`; unit tests that
   every API that writes remembers.
2. The minor collection; unit tests: a young object reachable only from an
   old one survives; weak and ephemeron cases; bytes and codes tails.
3. The policy in `Vm::collect_garbage`; `GC_STRESS` runs minor
   collections (and every Nth a full one).
4. Gates as before (check, kernel with `GC_STRESS=64`, reflection, replay,
   genesis, web, a debug-build kernel run); benchmarks; the IDE heap's
   pause, measured.

## 7. Implemented: results

- **The barrier** is in `Heap`'s write APIs (`remember`): the mutable-slice
  APIs, the field setters, `set_class`, `set_behavior_field` and an
  in-place reshape. `REMEMBERED` is bit 31 of the header's third word; the
  space field is 21 bits.
- **The minor collection** (`Heap::collect_minor`) copies, as section 2
  says; a copied object's old header holds its new offset (its
  `REMEMBERED` bit, which no young object otherwise has, marks it
  forwarded). The VM forwards its roots through a sorted list of
  (old, new) offsets. Weak references from copies and from remembered
  WeakArrays to dead young objects become nil; ephemerons follow the full
  collection's fixed point. The full collection (`collect`) is the
  sliding one, now able to start at an offset.
- **The policy** (`Vm::scheduled_collection`): minor, unless a commit
  asked for a full one or the old space has doubled since the last full
  one (at least a million words). `vm garbageCollect`, `allInstances` and
  the class queries stay full. Under `GC_STRESS`, every fourth collection
  is full.
- **Checkpoints.** The first replay test failed: a run restored from a
  checkpoint has every object old, while the original run still had young
  ones, so later minor collections kept different garbage and the next
  checkpoint's digest differed. The fix: taking a checkpoint now runs the
  checkpoint's collection (keeping weakly reachable objects) on the
  running heap too, whether or not anyone records, so both continue from
  the same heap with everything old. And the two places where a program
  can see the arena's order, `allInstances` and the subclass queries, now
  answer in allocation (sequence) order, since a restored heap is in that
  order and a running one need not be.
- **The web host** exports `eurasia_heap_stat` (objects, words,
  collections), for measuring.

Measured:

| on the IDE heap (native, `gcprobe`) | pause |
|---|---:|
| full collection, 117K live objects | 10 ms |
| minor, a million young objects, all dead | 0.0 ms |
| minor, a million young, 1% surviving | 0.7 ms |
| minor, a million young, 10% surviving | 8.7 ms |

A minor collection costs about 80 ns per survivor, whatever the size of
the old space (the same 8.7 ms with 667K live objects, where a full one
would take about 40 ms), and nothing per dead object.

The benchmarks (native, runs per second, against the quickened build):
NLRImmediate 470 to 515, ClosureDefFibonacci 23.7 to 25.9,
ParserCombinators 7.4 to 7.9, Richards 115 to 120; the rest within noise.
The barrier costs nothing measurable. The large-heap workload: building
the million nodes 729 to 630 ms, walking them 1194 to 974 ms (survivors
copied in discovery order end up closer together).

In the browser, the IDE runs on it; its live heap after collections in a
light session is 330K to 390K objects.

Gates: `check.sh`, kernel tests (also `GC_STRESS=64`, which exercises the
barrier hardest), reflection, replay (from the start and from every
checkpoint), genesis, web, and debug against release twice (identical;
one earlier difference was a wall-clock timer test).
