# Eurasia performance: where it stands, and options

**Date:** 2026-11-19
**Status:** Measured; Tier 1 done (section 5), uncommitted.

## 1. How slow

BenchmarkRunner's eleven benchmarks, measured as `BenchmarkRunner>>report`
does: a 500 ms warm-up, then the median of three 1000 ms windows. Scores are
runs per second (higher is better). Same machine, same session.

| Benchmark | psoup native | Eurasia native | slower by | Eurasia wasm (Node) |
|---|---:|---:|---:|---:|
| ClosureDefFibonacci | 50.7 | 3.2 | 16x | 3.2 |
| ClosureFibonacci | 89.3 | 3.5 | 26x | 3.8 |
| DeltaBlue | 187.2 | 6.8 | 28x | 5.8 |
| MethodFibonacci | 89.3 | 4.3 | 21x | 4.3 |
| NLRImmediate | 1157.0 | 86.9 | 13x | 79.6 |
| NLRLoop | 238.5 | 14.4 | 17x | 13.0 |
| ParserCombinators | 21.5 | 0.7 | 31x | 0.6 |
| Richards | 198.2 | 7.8 | 25x | 5.4 |
| SlotRead | 92.1 | 3.8 | 24x | 3.2 |
| SlotWrite | 53.5 | 3.3 | 16x | 2.7 |
| Splay | 274.7 | 27.3 | 10x | 21.9 |

- **Eurasia native is 10x to 31x slower than psoup native**, about 20x
  typically. Splay, which mostly allocates, suffers least; send-heavy code
  (ParserCombinators, DeltaBlue, Richards, the fibs) most.
- **Eurasia's wasm build is about as fast as its native one** (0.7x to 1.1x),
  so the browser is not the problem: the interpreter is.
- Against psoup's wasm build in Chrome (July baseline,
  `BENCHMARK_BASELINE_2026-07-16.md`, shorter windows): Eurasia's wasm is
  roughly 9x to 24x slower (Richards 5.4 against 130, DeltaBlue 5.8 against
  95). NS2JS in Chrome is far ahead of both.

How it was run: `EurasiaBenchmarkApp.ns` (an entry like
`EurasiaKernelSmokeTest`, packaging psoup's Kernel, collections and the
eleven benchmark modules with Eurasia's Actors and Runtime), packaged with
`target/kerneltests/EurasiaPackager.vfuel`, genesis with
`target/release/eurasia genesis.eus base.eus`, then
`target/release/eurasia base.eus [names]`, and
`node web/run-node.mjs eurasia_web.wasm base.eus`. psoup:
`out/ReleaseX64/primordialsoup out/snapshots/BenchmarkRunner.vfuel`.
`eurasia/scripts/benchmarks.sh` now does all of this (`PSOUP=1` adds
psoup's run).

## 2. Where the time goes

macOS `sample`, 6 s of Richards and DeltaBlue on native Eurasia, by the
function at the top of the stack:

| Share | Where | Why |
|---:|---|---|
| ~30% | `Vm::method_at`, plus `memcmp` (~5%) | Every send searches each class's method array linearly, comparing the selector's bytes with each method's. There is no method cache. |
| ~20% | drop glue of `VmError` | `ok_or(VmError::Malformed(..))` builds an error value on every call, and the loop in `method_at` does it once per method compared; dropping it is not free because other `VmError` variants own `String`s and `Vec`s. |
| ~16% | malloc and free | `selector_bytes` copies the selector into a new `Vec` on every send; every object is an enum whose body is its own `Vec` (`Body::Regular(Vec<Value>)` and so on), so each allocation is two mallocs; activations, closures and failures allocate. |
| ~6% | `step` | Each instruction looks the method up in the heap again to fetch its bytecode. |
| ~5% | `find_application_of`, `slot_index`, `instance_slot_count` | Every slot read or write walks the receiver's class chain to find the mixin's application, then walks it again to count the slots above it. |
| rest | sends, activation, natives | `3 + 4` is an ordinary send: the common-selector opcodes (176-207) have no fast path for SmallIntegers, so arithmetic and comparisons go through lookup and a native activation. |

Release-build settings are not the issue: LTO, one codegen unit and
`panic = "abort"` gained 5% to 9% (Richards 7.7 to 8.0, SlotRead 3.9 to
4.1, MethodFibonacci 4.4 to 4.8).

## 3. Options

In order of payoff for effort. The first group is local to
`interpreter.rs` and changes no format, bytecode or semantics; each must
keep the replay tests' outputs identical (they are deterministic, and none
of these change what a program observes).

### Tier 1: remove the obvious waste (days)

1. **A global lookup cache** keyed by (receiver class, selector, send kind
   and, for lexical sends, the sending mixin), holding the method found.
   Flushed when a class or mixin changes (`commit`, mixin application,
   reflection natives that install methods), and on restore. This removes
   the linear search and most of the selector copying. Psoup's interpreter
   has the same structure, so it also shows what to flush on.
2. **Compare selectors by identity**, if the packager and the compilers
   intern them (psoup's symbols are canonical); fall back to bytes
   otherwise. With 1, this matters only on a miss.
3. **Construct errors lazily**: `ok_or_else` instead of `ok_or` on hot
   paths, or a small `Copy` error code inside the interpreter with the
   rich `VmError` built at the boundary. About a fifth of the time today.
4. **Cache slot offsets**: the offset of a mixin's slots in a class is
   fixed until the class changes, so keep it in the class (or in the lookup
   cache entry, beside the getter or setter it was found for).
5. **SmallInteger fast paths** for the arithmetic and comparison common
   selectors (`+ - * // \\ < > <= >= = & | << >>`) when both operands are
   SmallIntegers and the result fits, as psoup does; overflow and anything
   else take the ordinary send.
6. **Keep the current method's bytecode in the frame** (or a raw slice
   valid until the next allocation or collection), so `step` does not look
   the method up per instruction.
7. **Release profile**: `lto = "fat"`, `codegen-units = 1`,
   `panic = "abort"` for native and wasm: 5% to 9%, for one line each.

Expected together: something like 5x to 10x on send-heavy code, which
would put Eurasia within a few times of psoup. That is an estimate from the
profile, to be checked benchmark by benchmark.

### Tier 2: the object model (weeks)

8. **Objects in one arena** instead of `Vec<Object>` with a `Vec` per body:
   a header and the slots inline, so an allocation is a bump, a slot read is
   one indirection, and the collector copies contiguous memory. This is
   what Splay and allocation-heavy code (and the GC) need; it touches the
   heap, the collector, the snapshot reader and writer, and every
   `Body` match.
9. **Contexts without heap objects** for ordinary activations (already
   mostly so: frames are Rust structs; activations are made only on
   demand), and closures that do not copy into a fresh `Vec`.

### Tier 3: beyond an interpreter (months)

10. **Inline caches** per send site (monomorphic, then polymorphic), once
    the global cache shows its hit rate.
11. **A template or baseline compiler**: native code for each method, or,
    in the browser, generated wasm per method or per hot method. This is
    where psoup is not, and where NS2JS gets its 10x-100x; for Eurasia it
    must coexist with replay (the compiled code must make the same host
    calls in the same order) and with checkpoints taken at safepoints.

## 4. Recommendation

Do Tier 1, measuring after each item with the harness above, and stop to
reassess when it is done. It is low risk (no format or semantic change,
and replay checks determinism), and the profile says most of the time is
there.

## 5. Tier 1: what was done, and the result

Native, same machine and measuring as section 1, runs per second:

| Benchmark | before | after | gain | psoup | now slower by |
|---|---:|---:|---:|---:|---:|
| ClosureDefFibonacci | 3.2 | 13.9 | 4.3x | 50.7 | 3.6x |
| ClosureFibonacci | 3.5 | 17.6 | 5.0x | 89.3 | 5.1x |
| DeltaBlue | 6.8 | 60.2 | 8.9x | 187.2 | 3.1x |
| MethodFibonacci | 4.3 | 28.8 | 6.7x | 89.3 | 3.1x |
| NLRImmediate | 86.9 | 343.3 | 4.0x | 1157.0 | 3.4x |
| NLRLoop | 14.4 | 70.2 | 4.9x | 238.5 | 3.4x |
| ParserCombinators | 0.7 | 4.5 | 6.4x | 21.5 | 4.8x |
| Richards | 7.8 | 56.3 | 7.2x | 198.2 | 3.5x |
| SlotRead | 3.8 | 26.8 | 7.1x | 92.1 | 3.4x |
| SlotWrite | 3.3 | 21.3 | 6.5x | 53.5 | 2.5x |
| Splay | 27.3 | 103.5 | 3.8x | 274.7 | 2.7x |

From about 20x slower than psoup to about 3.5x (2.5x to 5x).

The wasm build (Node, run while the replay tests were also running) gained
as much: Richards 5.4 to 36.3, DeltaBlue 5.8 to 36.8, MethodFibonacci 4.3
to 19.1, ParserCombinators 0.6 to 2.8, Splay 21.9 to 67.3. Against psoup's
wasm build in Chrome (the July baseline: Richards 130, DeltaBlue 95), that
is about 3x slower, down from about 20x.

What changed, all in `eurasia-core` and none of it in a format, the
bytecode or what a program observes:

- **A global lookup cache** (`Vm::send`): direct-mapped, 4096 entries, keyed
  by the receiver's class, the selector, the rule (ordinary, self, super,
  implicit receiver, outer at a depth) and, for all but ordinary sends, the
  sending method's mixin. An entry holds the method, where its receiver comes
  from (present, the frame's, or a fixed enclosing object), and an
  accessor's absolute slot index, so slot reads and writes no longer walk
  the class chain (Tier 1 items 1 and 4; with the cache, comparing selectors
  by identity, item 2, matters only on a miss and was not needed). Only
  sends that find a method are cached; a #doesNotUnderstand: takes the full
  lookup. Cleared after a collection (objects move), a commit (identities
  are forwarded), a write to a method or mixin (`store_slot`), and
  `Method>>header:`. Like psoup's, it is not cleared when an element of a
  mixin's method array is written: that array is not frozen, and a program
  that changes it in place on a mixin in use would see a stale method, as
  on psoup (the mirror builders make new arrays and commit them). Gain: 2x to 6x on its own.
- **SmallInteger fast paths** for common selectors 0 to 13 (`+ - * // \\
  << >> & | < > <= >= =`): computed in place when both operands are
  SmallIntegers and the native would answer; overflow, a zero divisor, a
  shift out of range (and, conservatively, `>>` of a negative) take the
  send. Each fast path is used only after checking, through the lookup, that
  SmallInteger's method for that selector is the expected native, so an
  image that redefines one keeps its definition. Gain: up to 3x more on
  arithmetic (MethodFibonacci 9.9 to 28).
- **Lazy errors**: `ok_or_else` on the interpreter's paths, and the
  indirect-local instructions no longer build an error (with the method's
  selector as a `String`) on every execution.
- **Fewer allocations per send**: a native's arguments are not copied unless
  it fails or needs a frame; inserting an absent receiver no longer calls
  memmove.
- **Bytecode in the frame**: `Method.bytecode` is an `Rc<[u8]>`, and a frame
  keeps its method's, so an instruction fetch does not look the method up
  (a few percent). A frame keeps the code it began with if `Method>>bytecode:`
  later changes an unfrozen method's.
- **Release profile**: fat LTO, one codegen unit, `panic = "abort"`.

What the profile shows now: the instruction loop itself, then malloc and
free (an object's body is its own `Vec`, closures copy their captured values
into one, activations are allocated for closures' defining frames), then the
send path. The next steps are Tier 2's object model and Tier 3's inline
caches; closures (ClosureFibonacci, 5x) gain most from the first.

## 6. Dispatch, first pass (after Tier 2 Step 0)

Native, runs per second (Step 0 numbers from
`EURASIA_TIER2_PLAN_2026-11-19.md` section 5; noise about 5% to 10%):

| Benchmark | after Step 0 | now | psoup | now slower by |
|---|---:|---:|---:|---:|
| ClosureDefFibonacci | 16.4 | 20.0 | 50.7 | 2.5x |
| ClosureFibonacci | 24.8 | 31.1 | 89.3 | 2.9x |
| DeltaBlue | 64.7 | 77.7 | 187.2 | 2.4x |
| MethodFibonacci | 29.1 | 38.3 | 89.3 | 2.3x |
| NLRImmediate | 355.2 | 410.1 | 1157.0 | 2.8x |
| NLRLoop | 80.8 | 97.8 | 238.5 | 2.4x |
| ParserCombinators | 4.9 | 5.8 | 21.5 | 3.7x |
| Richards | 70.4 | 85.3 | 198.2 | 2.3x |
| SlotRead | 27.2 | 34.2 | 92.1 | 2.7x |
| SlotWrite | 21.4 | 26.2 | 53.5 | 2.0x |
| Splay | 109.3 | 117.9 | 274.7 | 2.3x |

What changed:

- **`step` is inlined into the event loop** (`#[inline(always)]`). It was a
  call per instruction with a 496-byte stack frame and twelve saved
  registers. This alone gave 20% to 28%.
- **A frame keeps its method's literals and mixin**, so a send, a literal
  push and an outer or implicit-receiver send do not look the method up.
  They are forwarded with the frame on a commit, and reloaded for every
  frame whenever the lookup cache is cleared (collections, commits, writes
  to methods and mixins), so they never go stale. The flush now happens
  after the change it follows (after the frames are forwarded in a
  collection, after the write in `store_slot`).
- **A lookup cache entry holds the method's header** (now `Copy`), so
  activating a native or an accessor does not look the method up. Neutral
  within noise; kept because it is no more code than what it replaced.
- **One comparison per safepoint**: the event loop compares the allocation
  count with the count at which a collection or checkpoint can next be due,
  and checks in full only then; anything that changes that sets it to 0.
  Safepoints are where they were, so collections and checkpoints happen at
  the same points (the replay tests and GC stress agree). A few percent.

Tried and dropped: caching each method's bytecode, literals and mixin in
the lookup cache entry as well (a larger entry, and a reference count
change on every hit, was 5% to 10% slower than the lookup it saved).

Where it stands: about 56 to 98 million bytecodes a second (Richards 67M,
MethodFibonacci 98M, Splay 56M), 10 to 15 ns each, most of it sends and
returns. The rest of the gap is the shape of a safe-Rust interpreter: the
operand stack and the frames are `Vec`s, so every push checks capacity and
every frame access goes through `frames.last()`; frames are 104-byte
structs pushed and popped by copy; the instruction pointer lives in the
frame, not in a register; errors make every `Result` large.

Options from here:

1. **Pre-decoded code with per-site inline caches** (one to two weeks):
   each method's bytecode decoded once into operands and cache cells, so
   an instruction needs no decoding, and a send checks the receiver's class
   against its own site's entry. Estimate 1.3x to 1.6x.
2. **Keep the interpreter's state in locals** (days, and can come first):
   the instruction pointer, the current code and the frame's base in local
   variables in the loop, written back only at sends, returns and
   safepoints. Estimate 1.2x to 1.4x.
3. **Allow `unsafe` in the interpreter's core** (the crate denies it now):
   a raw operand stack and frames without bounds or capacity checks, as
   psoup has. Estimate 1.5x to 2x; it changes the project's safety stance,
   so it is a decision, not an optimization.
4. **A baseline compiler** (Tier 3 proper; months): the only route past
   psoup, as NS2JS shows.

## 7. Dispatch, second pass: the interpreter's state in locals

Native, runs per second (section 6's numbers before; noise about 5% to
10%):

| Benchmark | section 6 | now | psoup | now slower by |
|---|---:|---:|---:|---:|
| ClosureDefFibonacci | 20.0 | 24.2 | 50.7 | 2.1x |
| ClosureFibonacci | 31.1 | 40.0 | 89.3 | 2.2x |
| DeltaBlue | 77.7 | 79.4 | 187.2 | 2.4x |
| MethodFibonacci | 38.3 | 55.8 | 89.3 | 1.6x |
| NLRImmediate | 410.1 | 478.5 | 1157.0 | 2.4x |
| NLRLoop | 97.8 | 138.3 | 238.5 | 1.7x |
| ParserCombinators | 5.8 | 6.2 | 21.5 | 3.5x |
| Richards | 85.3 | 84.0 | 198.2 | 2.4x |
| SlotRead | 34.2 | 42.1 | 92.1 | 2.2x |
| SlotWrite | 26.2 | 35.1 | 53.5 | 1.5x |
| Splay | 117.9 | 119.4 | 274.7 | 2.3x |

What changed (`Vm::run_simple`):

- **A loop with its state in locals.** The instruction pointer, the code,
  the frame's base, locals and receiver, and the operand stack's buffer,
  length and capacity are local variables. The simple instructions
  (pushes, stores, branches, literals, SmallInteger arithmetic) run there;
  any other instruction, and anything out of the ordinary in a simple one
  (an index out of range, a non-Boolean condition, no room on the stack),
  writes the state back and goes through `step` unchanged, so errors and
  every complex instruction behave exactly as before.
- **It does not leave the loop at a send.** After `step` runs a send or a
  return, the loop reloads its state from the frame now on top and goes
  on; it returns to the event loop only when that has something to do (no
  frame left, a collection or checkpoint that can be due, the interrupt
  poll). Safepoints are where they were: no simple instruction allocates,
  so nothing can come due between two of them, the allocation count is
  compared after every `step`, and the interrupt countdown counts every
  instruction. This, more than the locals themselves, is the gain.
- **Tried and reverted: unchecked accesses in that loop.** With `unsafe`
  allowed in `interpreter.rs` only, the code and the operand stack were
  read and written through raw pointers, each access after a
  `debug_assert!` of what makes it sound (so a debug build checked them
  all; a debug-build kernel-test run gave output identical to release).
  Measured against the same loop with ordinary indexing, it made no
  difference on any benchmark (within 1% to 2%): the bounds and capacity
  checks are well-predicted branches, and the time is elsewhere (below).
  So the crate is back to denying `unsafe` everywhere; it should come back
  only with a change whose measured gain needs it.
Tried and dropped: forcing `send`, `send_by_literal` and `activate_with`
inline into the loop (`#[inline(always)]`) was 10% to 20% slower; the
larger loop costs more than the calls.

Where the time goes now (Richards, Time Profiler with line tables, by
function): the loop 28%, `step` (now mostly the sends it decodes) 13%,
activation 11%, the lookup-cache probe and send 13%, heap access 6%, the
rest spread thin. No single line is above 3%. Richards and DeltaBlue, the
most send-heavy, did not move in this pass: their cost is the send path
itself (call and return overhead of `send` and `activate_with`, the cache
probe, pushing and popping 104-byte frames). Pre-decoded code with per-site
inline caches (section 6, option 1) is what addresses that.

How to profile by line: build with
`CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`, run `dsymutil` on the
binary, record with `xcrun xctrace record --template 'Time Profiler'
--launch -- eurasia base.eus Richards`, export the `time-profile` table
with `xcrun xctrace export`, and symbolize the leaf addresses with
`atos -i` (inlined frames), taking the innermost Eurasia line.

## 8. Per-site inline caches: tried, slower, reverted

Each method's bytecode became a `Code` holding, besides the bytes, one
cache cell per send instruction (numbered once when the method is made),
each entry stamped with an epoch that the interpreter advanced wherever it
clears the global lookup cache. A send checked its own site's cell (epoch,
receiver class, selector) before the global cache, and filled it on a
miss.

It was 3% to 9% slower on ten of the eleven benchmarks (Richards 84.4 to
81.2, MethodFibonacci 55.2 to 51.8, SlotRead 42.0 to 38.2; Splay 120.0 to
124.5, within noise). The global cache already hits, and cheaply; a site
check adds work (recording the instruction's index on every instruction,
a table lookup per send, copying a 64-byte entry) without removing any.
So lookup is not where a send's time goes, and it is reverted.

What the measurements now say, after sections 6 to 8:

- Lookup (the global cache) is cheap and is not worth more work.
- Unchecked accesses are not worth `unsafe` (section 7).
- The cost of a send is spread over its whole path: the calls themselves
  (`send`, `activate_with` and `local_return` are not inlined, and
  inlining them was slower), pushing and popping a 104-byte `Frame`, and
  filling the new frame's locals. Shrinking the frame (indices as `u32`,
  the two optional references without their `Option` tags) and merging
  the activation of an ordinary method into the loop might give another
  10% to 30%.
- Beyond that, closing the remaining 2x to psoup, and going past it, takes
  a different execution model: a baseline compiler (section 3, Tier 3,
  item 11), not further interpreter tuning.

## 9. Probe: slots inline with the header (Tier 2's premise), no gain

Before spending weeks on Tier 2's arena, a probe tested its premise for
running code: that reaching a slot through the object and then its
separate slot vector costs a dependent cache miss. `Body::Regular` held a
small vector instead of a `Vec`: up to 8 slots inline in the object, next
to its header, more in a vector; `basicNew` built small instances inline
without allocating. Reverted after measuring (it was never committed).

Against the committed build (b711010), native, runs per second: every
benchmark within 1% (Richards 84.4 to 83.8, SlotRead 42.0 to 41.5,
DeltaBlue 80.1 to 79.8, MethodFibonacci 55.2 to 55.3), except Splay, 120.0
to 125.1 (4%, about the noise). So the extra indirection costs nothing
measurable here; these benchmarks' objects stay in cache. Splay's
remaining malloc is mostly the collector's own (`collect_with` rebuilding
the object vector and its forwarding table), which is what the arena's
sliding collector would remove: worth perhaps 10% on allocation-heavy code.

So Tier 2 is not worth its two to three weeks for speed on these
benchmarks. It may still be for large heaps (the IDE's), where objects do
not stay in cache; that needs a measurement on such a heap, not these
benchmarks. For speed in general, what is left is Tier 3's baseline
compiler.

## 10. On a large heap, the object layout does matter

Section 9's benchmarks keep their objects in cache. `EurasiaHeapBench.ns`
measures a large heap instead: it builds a million four-slot nodes, each
allocated next to a filler Array so the nodes are scattered as long-lived
objects are in a big image, and walks them by their accessors; it also
walks a thousand nodes, which stay in cache, for the same number of visits
(10 million each). Packaged and run like the benchmarks (entry
`EurasiaHeapBench.ns`, modules Kernel, Collections, Actors, Runtime).

Today an object is a 120-byte `Object` (32-byte header, 88-byte `Body`, as
large as its largest variant, `Method`), and a Regular object's slots are
a separate allocation besides: a node is about 170 bytes in two places.
Section 9's probe made every `Body` larger still, which is why it showed
nothing. A fairer probe, `eurasia-perf/compact-objects-probe.patch`
(applies to eurasia b711010; never committed): up to four slots inline in
the `Body`, and the large, rare variants (Method, Mixin, Class,
Metaclass, Activation, Promise) boxed, so a node is one 104-byte object
with its slots inside it.

| | committed | compact probe |
|---|---:|---:|
| walk 1,000,000 scattered nodes, 10 times | 1770 ms | 1200 ms |
| walk 1,000 nodes in cache, 10,000 times | 1188 ms | 1190 ms |
| build the 1,000,000 nodes | 955 ms | 842 ms |

- On a big heap, the walk is 1.5x faster with the slots in the object, and
  as fast as the walk in cache: the separate slot allocation is the whole
  of the large-heap penalty here.
- The benchmarks barely move (Splay 120 to 129, Richards 84.4 to 81.7,
  NLRImmediate 477 to 438, the rest within 3%); the probe's boxed
  activations cost the NLR benchmarks something that the arena would not.

So Tier 2 is worth doing for large heaps, which is where the IDE lives:
code that touches many long-lived objects (the IDE's presenters, the
compiler's trees, the mirror and class structures) pays this penalty on
every slot read. The arena would do better than the probe (a four-slot
node in 56 bytes instead of 104, and no boxed variants), and also removes
the collector's own allocation (section 9).

## 11. Tier 2 done: the arena

The heap is now one arena, `EURASIA_ARENA_DESIGN_2026-11-19.md` (section
10 has the numbers): on a large heap, walking objects is 1.5x faster and no
slower than in cache; allocation-heavy code is 15% to 30% faster; the other
benchmarks are within noise but for non-local returns (5% to 7% slower).
