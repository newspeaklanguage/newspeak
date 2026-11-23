# Eurasia: objects in one arena (Tier 2), design

**Date:** 2026-11-19
**Status:** Steps 1 and 2 done (sections 8 and 10), uncommitted.
**Why:** `EURASIA_PERFORMANCE_2026-11-19.md` section 10: on a large heap,
reading a slot through an object and then its separately allocated slot
vector costs 1.5x on code that walks many objects. A compiler later wants
the same thing: an object it can address as a base and a fixed offset.
**Plan:** `EURASIA_TIER2_PLAN_2026-11-19.md`, Steps 1 and 2.

## 1. Layout

The heap is one `Vec<u64>`, the arena. An object is three header words
and then its contents, in consecutive words:

| word | holds |
|---|---|
| 0 | the class (a `Value`) |
| 1 | the allocation sequence number (identity, hash, order; as now) |
| 2 | format (5 bits), flags (5 bits), space (22 bits), size (32 bits) |
| 3.. | the contents: `size` Values, or `size` bytes packed into words |

- A reference `Value` is the object's word offset in the arena (the
  tagged encoding already allows it: `value.rs`, "the object's slot in an
  arena"). Offsets are the same on native and wasm32: words are `u64` on
  every target, as Values are.
- **Space:** `Program` is the largest 22-bit value; `Actor(n)` is `n`, so
  up to about four million actors. **Size:** up to 2^32 fields or bytes.
- Every object's size is fixed at allocation (Newspeak has no growing in
  place), so it is exactly as many words as it needs. An object with no
  contents (nil, true, false, most classes' instances of fieldless
  classes) is three words.

## 2. Formats

| format | contents | today |
|---|---|---|
| Regular | `size` slots | `Body::Regular` |
| Array, WeakArray | `size` elements | `Body::Array`, `Body::WeakArray` |
| Ephemeron | key, value, finalizer | `Body::Ephemeron` |
| Bytes, String | `size` bytes, packed | `Body::Bytes`, `Body::String` |
| LargePositive, LargeNegative | the magnitude's bytes | `Body::LargeInteger` |
| Float | the IEEE bits, one word | `Body::Float` |
| Method | header (a SmallInteger), literals, mixin, selector, source, library, bytecode (a Bytes object) | `Body::Method` |
| Mixin | name, methods, enclosing mixin, slot names, slot count (SmallInteger), class mixin, library | `Body::Mixin` |
| Class, Metaclass | mixin, superclass, enclosing object, name, this class, library | `Body::Class`, `Body::Metaclass` |
| Closure | defining activation, initial ip and argument count (SmallIntegers), then the copied values | `Body::Closure` |
| Activation | frame serial or nil, method, receiver, closure, then, if detached, sender, bci and the temps | `Body::Activation` |
| FarRef | actor (SmallInteger), target | `Body::FarRef` |
| Promise | state (SmallInteger), value, owner, waiters (an Array), queue (an Array) | `Body::Promise` |

- The program objects become pointer objects whose fields are Values in
  fixed positions; what is not a reference today (a method's header, a
  closure's initial ip) is a SmallInteger there. The collector, the
  snapshot writer and every walk over references then treat every pointer
  format alike, except WeakArray and Ephemeron, which keep their rules.
- **Bytecode** is a Bytes object the method refers to. The interpreter's
  per-frame `Rc<[u8]>` (section 3 of the performance doc) moves to a side
  table keyed by the method, filled on first activation and cleared with
  the lookup cache, so instruction fetch is as fast as now.
- **A promise's waiters and queue** grow over time, so they are Arrays the
  promise refers to, replaced by a larger one when full (doubling). These
  are allocations the VM makes today without counting them (a `Vec`
  growing); in the arena they are counted. Open: whether to count them
  (simplest; it changes allocation counts on promise operations, and so
  when collections and checkpoints fall, from what this version records
  today) or to allocate them uncounted. Decided in Step 2, before any
  recording format depends on it.

## 3. Changes of shape

- **Commit's reshape** (an instance gains or loses slots when its class
  changes) cannot happen in place when it grows. The instance moves: a new
  object of the new size at the end of the arena with the same sequence
  number, class, flags and space, and every reference to the old one is
  rewritten, as the collector rewrites references when it slides, and as
  commit already does for its identity forwarding. Identity, hash and
  order are unchanged. The old copy is garbage.
- **Becoming a different format** does not happen today (`store_slot`
  writes fields in place), and stays so.

## 4. The collector

The same algorithm and semantics as now (`gc.rs`): mark from the roots,
apply the weak and ephemeron rules, then slide survivors down in
allocation order, so sequence numbers, identity order and hashes are
unchanged. The forwarding table maps old word offsets to new ones (a
side `Vec` indexed by object, or the header's class word reused as a
forwarding pointer during the slide). It no longer allocates a new object
vector, and a survivor is moved by one copy of its words.

A very large object (a multi-megabyte ByteArray) is copied whenever it
slides. If that shows up, a large-object space can come later; it does
not change the model.

## 5. Snapshots

The snapshot format (`docs/SNAPSHOT_FORMAT.md`) does not change. The
writer reads objects through the heap's API; the reader builds the arena.
Images, checkpoints and replay logs from before load as they do now.

## 6. The heap's API (Step 1)

Step 1 changes no representation: it makes every user of object contents
go through `Heap` methods, so that Step 2 can change what is behind them.
After Step 1, only `object.rs`, `gc.rs` and the snapshot reader and writer
see `Body`.

- **Allocation stays as it is**: `allocate(class, space, Body)`. `Body`
  becomes only a description of an object to make (the snapshot reader
  and the builder already use it so); in Step 2, `allocate` lays it out
  in the arena. The 50 allocation sites do not change.
- **Reading and writing** go through:
  - `format(v) -> Option<Format>`: a small `Copy` enum, for dispatch where
    code matches on `Body` today;
  - `flags`, `set_flags`, `space`, `seq`, `class` of an object;
  - `fields(v) -> Option<&[Value]>` and `fields_mut`: the Values of any
    pointer format, in the order of section 2 (the order
    `natives::readable_fields` already defines for contract objects);
  - `bytes(v) -> Option<&[u8]>` and `bytes_mut`; `float(v)`;
    `large_integer(v)`;
  - typed views for the program objects, `MethodRef`, `MixinRef`,
    `BehaviorRef`, `ClosureRef`, `ActivationRef`, `PromiseRef`, whose
    getters (`m.literals()`, `m.header()`, `c.copied()`) replace the
    fields read today (`m.literals`), and setters on `Heap` for the
    writes.
- **Slices in Step 2.** `fields` returns a slice of the arena's words as
  Values, and `bytes` a slice of them as bytes. With the crate denying
  `unsafe`, that needs `Value` to be `#[repr(transparent)]` and the
  `bytemuck` crate's safe casts (`cast_slice`), whose `unsafe` is in
  `bytemuck` itself. The alternative, getters that copy one field at a time
  and `Vec<u8>` copies for bytes, is slower where it matters (selector
  comparison, string natives). Proposed: `bytemuck`.

## 7. Steps and gates

1. **Step 1a:** the API on `Heap`, over today's `Body`, with unit tests.
2. **Step 1b:** the interpreter and the natives through it.
3. **Step 1c:** the builder, the snapshot crate (its reader and writer
   may keep `Body`) and the tests through it.
4. **Step 2:** the arena behind the API; the collector; reshape by moving;
   the bytecode side table; the snapshot reader and writer.
5. **Measure:** `scripts/benchmarks.sh`, `EurasiaHeapBench.ns`, and an IDE
   session on Eurasia.

Each step: `scripts/check.sh`, kernel tests (also with `GC_STRESS=64`),
reflection, replay and web tests, and a debug-build kernel run; Step 2
also checks that the committed test images and recorded replay logs load
and replay unchanged.

## 8. Step 1: done

Every reader and writer of object contents outside `object.rs`, `gc.rs`
and the snapshot reader and writer goes through `Heap`'s API: about 250
sites in the interpreter and natives, the builder and the tests. `Body`
remains only as the description `allocate` takes.

- The program objects' views (`MethodRef`, `MixinRef`, `BehaviorRef`,
  `ClosureRef`, `ActivationRef`, `PromiseRef`) replaced `&Method` and the
  others; field reads became getters (`m.literals()`), about 90 of them
  converted mechanically from the compiler's E0615 errors.
- Writes are setters on `Heap`: `set_method_field`, `set_method_header`,
  `set_method_bytecode`, `set_mixin_field`, `set_mixin_slot_count`,
  `set_this_class`, `set_activation_frame`, `detach_activation`,
  `attach_activation`, `set_closure_copied`, `set_promise`,
  `push_promise_waiter`, `push_promise_queue`, `take_promise_lists`,
  `reshape`, `set_ephemeron_field`, and the flags and class.
- Walks over the heap use `Heap::objects()`, not object indices, so they
  hold when references become word offsets.
- Hot paths kept one lookup: `regular_slots` and `regular_slots_mut` for
  the accessors and `store_slot`, `array_elements_mut` for indirect locals.
- One escape remains for Step 2: `activation_record_mut`, for the
  Simulator's natives on a detached activation, which can resize its temps
  (`ActivationSizePut`); in the arena the temps become their own Array.
- The builder no longer grows a mixin's method array in place; it installs
  a longer one.

Gates: `check.sh`, kernel tests (also with `GC_STRESS=64`), reflection,
replay and web tests, and a debug-build kernel run identical to release.
The benchmarks are unchanged (all eleven within 1%).

Decisions Step 2 needs (section 2 and section 6): the `bytemuck`
dependency for slices of the arena, and whether a promise's growing lists
count as allocations.

## 9. Decisions (2026-11-19)

- **No `unsafe`, so bytes live in their own space.** The arena is a
  `Vec<Value>` (header words stored as raw bits), so a pointer object's
  fields are a `&[Value]` slice without a cast. A byte object (String,
  ByteArray, LargeInteger) keeps its header and size in the arena; its
  bytes are in a separate `Vec<u8>`, and its one content word is the
  offset of its bytes there (a SmallInteger). The collector compacts both
  spaces. A byte object's contents are therefore not next to its header:
  one more step to reach them, which the measurement (section 10 of the
  performance doc) says does not matter; the gain is in pointer objects.
  This replaces section 6's `bytemuck` proposal and section 1's "bytes
  packed into words".
- **A promise's lists are counted allocations.** Waiters and the queue are
  Arrays the promise refers to (nil when empty), replaced by a longer one
  on each addition. Allocation counts, and so collection and checkpoint
  points, differ from the current version's; compatibility with it does
  not matter.
- **No compatibility with the current version is needed** (images,
  checkpoints, replay logs). The snapshot format stays as it is for now
  only because that is less work.
- **Bytecode stays out of the arena:** a method's content word is an
  index (a SmallInteger) into the heap's table of `Rc<[u8]>` codes, which
  the collector compacts with the methods; the interpreter keeps fetching
  through its frame's `Rc`, as now.
- **A detached activation's temps are an Array** it refers to, so
  `ActivationSizePut` replaces the Array instead of resizing the object.
- **Method headers are two SmallIntegers** (kind, access, argument and
  local counts; native and slot), so every pointer format's contents are
  Values the collector can scan uniformly. Only Float (raw bits) and the
  byte formats' offset word are not references.

## 10. Step 2: done

The heap is the arena of sections 1, 2 and 9. `Heap` holds the words
(`Vec<Value>`), the byte space (`Vec<u8>`) and the code table
(`Vec<Rc<[u8]>>`); an object is three header words (class, sequence
number, and format, flags, space and size packed in one word) and its
contents. No `unsafe`.

- **Allocation** lays a `Body` description out at the end of the arena
  without intermediate vectors; `allocate_closure`, `allocate_regular` and
  `allocate_array` skip the description for the hot cases (`PUSH_CLOSURE`,
  `basicNew`).
- **The collector** marks (the same weak and ephemeron rules) into a bit
  per word, then is a compressor: a bit per live word and, per 64-word
  block, the live words before it, so an object's new offset is a block
  count plus a popcount. Survivors slide down in place; the byte space and
  the code table are compacted with them.
- **Reshape** writes in place when the size is unchanged; otherwise the
  instance moves to the end of the arena with its sequence number, flags
  and space, its old place becomes a filler that walks skip and the next
  collection drops, and commit forwards references to it with its other
  identity changes. The snapshot writer orders each space by sequence
  number, since a moved object is out of arena order.
- **Promise lists and detached temps** are Arrays (counted allocations).
  The Simulator's natives on a detached activation use setters; resizing
  its temps installs a new Array.
- **Snapshot format 8**: a promise record's waiters and queue, and a
  detached activation's temps, are references to Arrays. The packager
  (`EurasiaPackager.ns`) writes version 8; older images are refused.

Measured (native, runs per second; noise about 5%):

| | before the arena | arena |
|---|---:|---:|
| walk 1,000,000 scattered nodes, 10 times | 1770 ms | 1194 ms |
| walk 1,000 nodes in cache, 10,000 times | 1188 ms | 1193 ms |
| build the 1,000,000 nodes | 955 ms | 729 ms |
| Splay | 120.0 | 138.4 |
| Richards | 84.4 | 83.2 |
| DeltaBlue | 80.1 | 78.4 |
| ParserCombinators | 6.2 | 6.2 |
| SlotRead / SlotWrite | 42.0 / 35.1 | 40.8 / 36.0 |
| MethodFibonacci | 55.2 | 54.3 |
| ClosureFibonacci / ClosureDefFibonacci | 39.8 / 23.9 | 38.6 / 23.0 |
| NLRImmediate / NLRLoop | 477.5 / 136.3 | 443.5 / 129.3 |

On a large heap, walking objects is 1.5x faster and as fast as in cache;
allocation-heavy code (Splay, building the nodes) is 15% to 30% faster;
the in-cache benchmarks are within noise, except the non-local-return
ones, 5% to 7% slower (activations and collections cost a little more).
On wasm, likewise: the large-heap walk equals the in-cache one.

Two things found on the way: building each object's contents in a
temporary vector before copying them into the arena cost a malloc and a
free per allocation (ClosureDefFibonacci was 30% slower until removed);
and the content size test on every object the collector walks was worth
a bitmask.

Gates: `check.sh`, kernel tests (also with `GC_STRESS=64`), reflection,
replay, genesis (reproducible) and web tests, a debug-build kernel run
identical to release, and unit tests of a reshape that moves.
