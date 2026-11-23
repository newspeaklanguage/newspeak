# Eurasia Tier 2: the object model, a plan

**Date:** 2026-11-19
**Status:** Step 0 done (section 5), uncommitted; Steps 1 and 2 not started.
**Context:** `EURASIA_PERFORMANCE_2026-11-19.md`. Tier 1 is committed
(eurasia `885c615`): Eurasia is about 3.5x slower than psoup, down from 20x.

## 1. What the profile says now

macOS `sample`, 4 s each, native release build, shares of samples by the
function at the top of the stack:

| Benchmark | interpreter loop (`step`, `event_loop`) | malloc and free | memcpy/memmove | collector |
|---|---:|---:|---:|---:|
| ClosureFibonacci | 42% | 29% | 8% | 0% |
| Richards | 42% | 14% | 7% | 2% |
| Splay | 42% | 12% | 8% | 6% |

Two findings change the order of the work:

1. **Much of the malloc is not the object model.** It is still waste of the
   Tier 1 kind, in particular:
   - `activate_closure` clones the whole `Closure` (its `copied` `Vec`
     included) on every closure call, then drops it;
   - a native whose outcome is not a plain answer (the closure `value`
     natives answer `ActivateClosure`) copies its arguments into a `Vec`,
     and several `Outcome` variants carry `Vec`s;
   - number natives (`comparison`, arithmetic) build `BigInt`s even for
     SmallIntegers when the fast path does not apply (a Float operand, or
     a common selector without one).

   Fixing these is days, not weeks, and touches no format.
2. **The arena helps less than Tier 1 did.** What the object model itself
   costs (an object is an `Object` with a `Body` enum, most bodies own a
   `Vec`, so an allocation is two mallocs and a free at collection; slot
   access goes through two indirections) shows up as part of the malloc
   share, the collector's share and the memcpy share. My estimate: 1.5x
   to 2x on allocation-heavy code (Splay, closures), 1.1x to 1.3x on
   send-heavy code (Richards, DeltaBlue). The interpreter loop, the largest
   share, is not touched by Tier 2 at all.

## 2. The plan

### Step 0: the remaining allocation waste (days)

- Closure activation reads the closure in place; no clone.
- Natives' outcomes carry their arguments by position on the stack, or in
  a small inline array, instead of a `Vec`; arguments are copied only on
  the failure path.
- SmallInteger operands in the number natives without `BigInt`
  (`comparison`, `integer_arithmetic`, `division`), and the Float cases of
  the common selectors.
- Then profile again.

Gates as in Tier 1: `scripts/check.sh`, kernel, reflection and replay
tests, GC stress (`GC_STRESS=64` kernel tests), and `scripts/benchmarks.sh`
before and after.

### Step 1: an accessor layer over the current heap (a week)

About 300 `Body::` matches in five files (natives 79, snapshot image 78,
interpreter 72, gc 39, builder 17) read and write object contents
directly. Before the representation changes, they go through typed
accessors on `Heap`: `slot(v, i)`, `set_slot(v, i, x)`, `size(v)`,
`bytes(v)`, `method(v) -> MethodRef`, `behavior(v)`, `closure(v)`, and so
on, returning views or copies rather than `&Body`. This is a mechanical
refactor with all tests green at every commit, and it is the part that
makes Step 2 possible without one enormous change.

### Step 2: objects in one arena (one to two weeks)

- **Heap:** one `Vec<u64>` of words. An object is a header and then its
  fields inline: header word 1 is the class; word 2 holds the sequence
  number (identity and hash, unchanged); word 3 holds format, flags,
  space and size. A `Value` reference becomes the object's word offset,
  which the tagged encoding already allows (`value.rs`: "the object's slot
  in an arena").
- **Formats:** pointers (Regular, Array, WeakArray, Ephemeron, and the
  program objects: Method, Mixin, Class, Metaclass, Closure, Activation,
  FarRef, Promise, whose fields are Values or SmallIntegers), bytes
  (Bytes, String, LargeInteger magnitude, packed into words), and Float
  (one word). Fields that are not Values today (a method header, a
  closure's `initial_ip`, a promise's state) become SmallIntegers in
  fixed positions. Variable parts (a closure's copied values, an
  activation's detached temps, a promise's waiters and queue) become
  either inline tails or separate Arrays.
- **Bytecode:** a method's bytecode is a bytes object it references; the
  frame's cached `Rc<[u8]>` moves to a side table keyed by method, filled
  on first activation and cleared when the lookup cache is.
- **Allocation:** a bump of the word vector. No malloc per object.
- **Collector:** the same algorithm and the same semantics (mark from the
  roots, weak and ephemeron rules, then slide survivors down in
  allocation order, so identity order, sequence numbers and hashes are
  unchanged). The forwarding table maps word offsets. It is a sliding
  compactor over contiguous memory instead of rebuilding a `Vec<Object>`.
- **Unchanged:** the snapshot format (`docs/SNAPSHOT_FORMAT.md`): the
  reader and writer translate to and from the arena, so images, checkpoints
  and replay logs from before still load. The semantics, the natives'
  behaviour, and everything a program can observe.

Gates: as in Step 0, plus a check that every committed test image still
loads and that recorded replay logs from before Step 2 replay.

### Step 3: measure, then decide

Benchmarks and a profile after each step. If the interpreter loop is
then clearly the largest share, Tier 3 (inline caches, then a template
or baseline compiler) is next.

## 3. Risks

- **Identity and hashing.** Sequence numbers stay in the header, so
  identity hashes do not change; the collector must keep allocation order
  (a sliding compactor does).
- **Determinism.** Allocation counts and collection points must not
  change, or replay logs recorded before the change diverge. The arena
  changes how an object is stored, not when objects are allocated or when
  a collection is due (the budget counts objects, not bytes, and stays
  so).
- **wasm32.** The word vector is `u64` on every target, as `Value` is, so
  layout and indices are identical on native and wasm.
- **`unsafe`.** The crate denies it; the arena is plain indexing into a
  `Vec<u64>`, with bounds checks. If bounds checks show up in the profile,
  that is a later decision.

## 4. Recommendation

Do Step 0 first: it is cheap, it is where much of the remaining malloc
is, and its result tells us how much Step 2 is still worth. Then Step 1
and Step 2, in that order.

## 5. Step 0: the result

Done:
- `value` to `value:value:value:` on a closure answer a new outcome,
  `ActivateReceiver`: the closure and its arguments are already on the
  stack, so nothing is copied, and `activate_closure` reads the closure in
  place instead of cloning it (its copied values included).
- SmallInteger operands in the number natives (`+ - *`, the comparisons,
  `=`, `// \\ quo: rem:`, `& | xor`) compute without `BigInt` when the
  result is a SmallInteger; anything else takes the `BigInt` path as before.
- Not done: copying an instruction's bytes byte by byte instead of with
  `copy_from_slice` measured slower, so it was left as it was.

Native, runs per second (Tier 1 numbers from
`EURASIA_PERFORMANCE_2026-11-19.md` section 5; noise between runs on this
machine is about 5% to 10%):

| Benchmark | after Tier 1 | after Step 0 | psoup | now slower by |
|---|---:|---:|---:|---:|
| ClosureDefFibonacci | 13.9 | 16.4 | 50.7 | 3.1x |
| ClosureFibonacci | 17.6 | 24.8 | 89.3 | 3.6x |
| DeltaBlue | 60.2 | 64.7 | 187.2 | 2.9x |
| MethodFibonacci | 28.8 | 29.1 | 89.3 | 3.1x |
| NLRImmediate | 343.3 | 355.2 | 1157.0 | 3.3x |
| NLRLoop | 70.2 | 80.8 | 238.5 | 3.0x |
| ParserCombinators | 4.5 | 4.9 | 21.5 | 4.4x |
| Richards | 56.3 | 70.4 | 198.2 | 2.8x |
| SlotRead | 26.8 | 27.2 | 92.1 | 3.4x |
| SlotWrite | 21.3 | 21.4 | 53.5 | 2.5x |
| Splay | 103.5 | 109.3 | 274.7 | 2.5x |

The profile afterwards: malloc and free are gone from the top of the stack
in ClosureFibonacci and Richards (from 29% and 14%); in Splay they are
still 12%, with the collector at about 6%, which is the object model's own
cost. The interpreter loop is now about half of every profile.

What that means for Steps 1 and 2: the arena's case now rests on
allocation-heavy code (Splay, anything building many objects) and on the
collector; for send-heavy code it would buy little. Tier 3's inline caches
and a faster dispatch loop address the larger share. Whether to do the
arena next or move to Tier 3 is the decision this result leaves.
