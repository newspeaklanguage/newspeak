# Eastasia: a high-performance native Newspeak VM, design

**Date:** 2026-11-23
**Status:** Draft for discussion. Sections marked **Decided** record Gilad's
decisions of 2026-11-23; everything else is a proposal. Nothing is
implemented.
**Context:** Eurasia (`NEW_VM_IMPLEMENTATION_PLAN_2026-11-17.md`,
`EURASIA_COMPILER_DESIGN_2026-11-19.md`, the arena and nursery designs,
`EURASIA_M7_SNAPSHOTS_REPLAY_DESIGN_2026-11-18.md`), the kernel contract
(`VM_KERNEL_CONTRACT_DESIGN_2026-11-09.md`,
`VM_KERNEL_OPERATIONS_2026-11-10.md`, `formal-semantics/kernel-semantics.tex`),
`BYTECODES_V5_SPEC_2026-07-13.md` and `eurasia/docs/SNAPSHOT_FORMAT.md`.

## 1. What Eastasia is

**Decided.**

- **A new VM**, not Eurasia's native build grown up. It shares Eurasia's
  contract: the snapshot format, V5 bytecode, the kernel operations and
  natives, and the formal semantics.
- **Native only.** It is not for the browser, and WebAssembly is not a
  concern. Eurasia remains the browser VM.
- **Primarily for interactive applications**, though general purpose. So it
  needs a foreign function interface, first on macOS, and a GUI (section
  10).
- **Written in Rust, the optimizing compiler included.** The compiler runs
  while the program runs and its speed matters. A second reason: a compiler
  in Newspeak would allocate in an actor's heap at times that depend on
  tiering, which would make compilation observable to the program. A Rust
  compiler on its own thread touches no actor heap.
- **Images are portable** between Eurasia and Eastasia.
- **The technique is Strongtalk's**, restated for Newspeak and for present
  hardware: an interpreter that gathers type feedback, and an adaptive
  optimizing compiler that inlines on that feedback and deoptimizes when it
  was wrong.

**Proposed: the two VMs also agree on everything a program can observe**
(section 3), so that a replay log recorded on one replays on the other, a
Croquet session can mix browser and native replicas, and Eurasia can serve
as the test oracle for Eastasia's optimizer. Section 3 revises the contract
so that this costs almost nothing.

## 2. What the optimizer may assume

**Decided** (Gilad's corrections, 2026-11-23). This section is the ground
rule for every optimization below.

- **Only local variables are statically bound.** Everything else is a send.
- **A lexical send is dynamically bound.** Mixin nesting fixes the *level*
  of an implicit-receiver or outer send for a program version. The lookup
  then runs on the enclosing object at that level, whose class may be a
  subclass of the lexically visible one and may override the member.
- **Imports are not a concept the VM has.** What exists is slots. Imports
  conventionally use immutable slots, but that is a convention.
- **Immutable slots are not constants.** A reflective store can change one,
  and that is not a program change.
- **Nested classes are firmer**: a nested class changes only by a reflective
  program change. But the accessor is a send to the enclosing object, and
  class-hierarchy inheritance lets a subclass of the outer class override
  the nested class.

Consequences for the design:

- Every binding beyond a local is a **speculation under a guard**, never a
  fact. The guard for an outer send is on the **enclosing object's class**,
  since that is what its target depends on.
- **Slot values are loaded, not folded.** A getter inlines to a load, and
  feedback on the class of what was loaded does the rest. Because nothing
  is folded, a reflective slot store needs no hook into compiled code.
  Folding a particular slot of a particular object can be added later for a
  site a profile singles out; it would need an identity guard on the holder
  and a dependency the reflective store invalidates.

## 3. The contract, revised for two VMs

Two things the present contract makes observable are expensive for an
optimizing VM to reproduce: the identity hash as an allocation sequence
number, and weak clearing tied to the collector's schedule. With those two
revised, agreement between the VMs is nearly free, because the rest
(arithmetic, floats, strings, large integers, insertion-ordered
collections) is shared Rust code or already contract.

These revisions change Eurasia and `kernel-semantics.tex` too.

### 3.1 Identity hash on first request

**Decided. Done in Eurasia** (branch `contract-v9`, not yet merged).

- Today: `identityHash(o) = h(seq(o))`, and every object carries its
  sequence number. Every allocation the VM makes on the program's behalf
  (messages, argument arrays, activation handles) is numbered, so a second
  VM must make exactly the same hidden allocations in the same order, and
  an optimizer that elides an allocation must still spend its number.
- Revised: an object has no hash until one is asked for. The first request
  takes the next value of a **per-actor hash counter** and stores it; `h`
  stays as it is. The order of first requests is determined by the program,
  so the hash is the same on both VMs, at any tier, in replay.
- A snapshot stores the hash of each object that has one, and each actor's
  counter.
- The optimizer may then elide allocations freely.
- The number is `2^61 + actor * 2^40 + count`. An image older than format
  version 9 keeps each object's sequence number as its hash number (they
  are below `2^61`), so its hashed collections stay valid.
- **A class is numbered when it is made**, from the same counter. That is
  how classes "keep sequence numbers" (3.3) with no second counter and no
  extra field.
- **To settle for parallel actors:** two actors may ask first for the hash
  of an object they share (a value, a program object). Which one numbers it
  is then a race. Proposed: the first request for an object outside the
  asking actor's heap is a logged input, like a message delivery (section
  8). Eurasia runs one actor at a time and has no race.

### 3.2 Weak clearing as logged input

**Decided** (confirmed 2026-11-24). This reverses M7's decision not to log
clearings. **Built in both VMs, 2026-11-24** (Eurasia: branch
`contract-v9`); see "As built" below, which fixes *where* clearing may
happen more than the bullets here say: only at clearing points.
**Clearing points confirmed by Gilad, 2026-11-24.** For replicated Croquet
model code the rule below stands (no weak references); clearing points
would allow dropping it later, given a contract-fixed budget, exact
clearing at every point and a per-actor clock. Not built.

- Today: collections fall on an allocation schedule that checkpoints save,
  so replay clears at the same points. That fixes the collector's schedule
  and forbids clearing from a concurrent or incremental collection.
- Revised: when a weak reference clears or an ephemeron fires is an
  **input**, recorded in the replay log. A replaying VM applies the log: it
  clears what the log says, when the log says. That is always sound,
  because the object is unreachable in the replay exactly as it was in the
  recording.
- The log must name the weak object. Weak arrays and ephemerons are few, so
  they take a number from a per-actor counter at creation, as classes do.
- Croquet model code must not observe weak references, the same rule
  Croquet imposes in JavaScript. Replicas have no shared log.
- The collector is then free: its schedule, its generations and whether it
  runs concurrently are invisible.

**As built.**

- **Clearing points.** A weak reference clears, and an ephemeron is
  mourned, only at a clearing point:
  - an explicit collection (`vm garbageCollect`);
  - the first safepoint at which the allocation counter has advanced by
    the **budget** the clearing point before announced.
- **What is logged** at each clearing point is one input event: the
  elements cleared (the WeakArray's hash number and the index), the
  ephemerons mourned (the hash number), and the budget to the next
  scheduled point. The recording VM chooses all three. A log's header has
  the budget the recording began with; a checkpoint has the clock.
- **Why points, and not any moment.** The log sits at the host boundary and
  is consumed in the order the VM meets it, so a replay must know *where*
  the next clearing is before it gets there. The allocation counter is the
  clock that both VMs already share (3.4). The cost: a collection between
  two clearing points may reclaim memory but not clear. A VM that wants to
  clear often announces a small budget; there is no lower limit.
- **In a replay** the VM asks the host at each clearing point, clears what
  the log says, and collects without clearing anything more. An object the
  recording's collector had not yet found dead stays reachable through its
  weak reference in both runs, so the two heaps are the same graph.
- **Weak objects are numbered when made**, from their actor's hash counter,
  as classes are. A reader numbers those of an older image.
- **Only a clearing point moves the clearing clock.** A checkpoint's
  collection, or any the VM makes for itself, does not. (It did: the first
  cross-VM replay under stress diverged at a checkpoint for that reason.)
- **Population queries no longer collect** (3.3): `allInstancesOf:`,
  `mixinApplicationsOf:` and `subclassesOf:` answer from the strong walk
  alone. They are therefore not clearing points, and a program can no
  longer rely on a query to clear weak references.
- **`Vm::collect_garbage`**, the embedder's call, clears and tells no
  host. A recorded run must not use it.
- **The log format is version 3.** An older log does not say what was
  cleared and is refused.
- **Checked** by `eastasia/scripts/agree.sh`: recordings of the kernel
  tests made on each VM with a clearing point every 997 or 1,499
  allocations replay on the other, which uses its own schedule, from the
  start and from a checkpoint; and on Eastasia with further collections of
  its own every 311 allocations. With the logged clears ignored, the replay
  diverges.
- **In the semantics** since 2026-11-24: `kernel-semantics.tex` (the
  allocation clock and its tick table, hash numbers, the canonical walk,
  clearing points with rules Clear-Scheduled and Clear-Explicit) and
  `gc-semantics.tex` (a closing subsection on what the kernel layer
  narrows). Not mechanized in SpecTec. The natives' tick counts are
  section 13 of `VM_KERNEL_OPERATIONS_2026-11-10.md`; the count for
  detaching frames is not yet a formula.
- **Not done:** a minor collection that keeps weak references, so a
  replay's clearing-point collections are full ones; the first hash of a
  shared object under parallel actors (3.1).

### 3.3 Population queries

**Decided.**

- **Classes keep sequence numbers**, assigned at creation (their hash
  numbers, 3.1). `mixinApplicationsOf:` and `subclassesOf:` answer in that
  order. With several actors the order is by actor, then by creation; it
  was by creation across actors (confirmed 2026-11-24).
- **`allInstancesOf:` answers in a canonical traversal order**: the order a
  walk from the roots reaches the instances, roots in role order and each
  object's references in slot order. The object graph determines it, so
  every VM agrees. This replaces allocation order in `eq:all-instances-of`.
- **Population queries answer strongly reachable objects only.** An object
  reachable only through an uncleared weak reference does not answer.
- The walk does not follow a weak array's elements or an ephemeron's key;
  it follows an ephemeron's value and finalizer at the ephemeron.
- **The roots beyond the roles** (confirmed 2026-11-24; to write into the
  semantics). Eurasia walks the roles, then the operand stack and frames, the actors' message
  loops and mailboxes, callbacks held by the host, and last the VM's own
  selector strings. An optimizing VM must present the same activations and
  temporaries, including values its code no longer needs, so every send
  site needs a full scope descriptor (7.4). That is the price of agreeing
  on reachability, and the debugger asks for it anyway.

Two things follow in Eastasia. An object the optimizer elided is still an
instance, so a query first brings the whole cohort to a safepoint and
materializes what optimized frames hold virtually; `commit:` needs the same
safepoint. And the query's walk is single-threaded and ordered, which is
acceptable for a reflective operation.

### 3.4 What else must change to match

**Decided as proposed: depth-first order, the logical allocation clock,
optional sections. The order and the sections are done in Eurasia**
(format version 9, `eurasia/docs/SNAPSHOT_FORMAT.md` on the branch).

- **Snapshot node order.** Nodes are written in sequence order today. With
  no sequence numbers, the writer uses the canonical traversal order of
  3.3, so the same heap still gives the same bytes on both VMs.
  - The order is what a VM *writes*, not a condition a reader checks. An
    image in another order (the packager's) is valid and loads.
  - **Proposed: the traversal is depth first**, in preorder. A loader lays
    objects out in file order, and Eurasia's full collection keeps that
    order for the life of the image, so the file order is the heap's
    locality. Depth first puts an object next to what it refers to first;
    breadth first separates parents from children. To measure on the IDE
    image against today's allocation order.
  - As built: the file's order follows every edge in the file, weak ones
    too, so it is defined by the file alone. `allInstancesOf:` uses the
    strong walk of 3.3. The two orders differ only where weak edges are.
  - Every save already walks what the roots reach (a snapshot collects
    into a copy first), so the order costs no extra pass if the save's own
    walk is the canonical one. The sort by sequence number at save and at
    load goes, and so does a byte or so per object of sequence delta.
- **A clock for checkpoints inside a turn.** The allocation counter was that
  clock. Proposed: keep a count of *logical* allocations for this purpose
  only. It is not stored in headers. An elided allocation still ticks it,
  which costs an add. Both VMs must then agree on the count, which brings
  back a weaker form of the hidden-allocation coupling of 3.1. The
  alternative is to checkpoint only at turn boundaries and host events,
  which need no clock. **Decided: the logical count.** Eurasia's
  allocation counter is already that count and stays as it is. What ticks
  it must now be written into the semantics as a list, since Eastasia has
  to tick for the same events.
- **The VM's own allocations do not tick it** (built 2026-11-24, both
  VMs). Found by running the IDE on Eastasia: the name string an alien
  send calls with was allocated when the lookup cache was filled, so the
  clock depended on cache behaviour, which differs between the VMs, and on
  Eastasia between runs, since its cache is indexed by addresses. Such a
  string, and a selector the VM sends itself, are now made off the clock.
  The rule for the list: an allocation ticks only if the program's
  semantics makes it, never a cache.
- **Optional sections.** A snapshot may carry a section a VM does not
  understand and skips (section 9, the inlining database). Today every
  section kind must be known.
- A **format version bump** for all of this: version 9. Its reader still
  reads version 8, which the Newspeak packager writes.

## 4. Strongtalk's techniques, and what becomes of each

| Strongtalk | Eastasia |
|---|---|
| Send bytecodes carry inline caches; the interpreter rewrites them | Bytecode is frozen and shared, so feedback lives in a side vector per method (section 6) |
| Type feedback from inline caches drives the compiler; static types are not used | The same. The typechecker's annotations are not consulted |
| Invocation counters; the recompilee is found by walking up the callers | The same, plus loop counters and on-stack replacement (section 7.5) |
| Inlining of methods and of blocks | The same. Block inlining is where most of the gain is |
| Customization by receiver class | Customization by *lineage* (section 5.3), since a nested class has one class object per enclosing instance |
| Uncommon traps and deoptimization through scope descriptors | The same (section 7.4) |
| Inline caches patched into the code | Caches in data. Patching code is expensive under W^X and needs cache flushes on ARM |
| Mixins in the VM's class model | Already Newspeak's model |
| Inlining database | Feedback carried in the snapshot (section 9) |
| Scavenging new space, card marking, compacting old space | The same per actor (section 5.4) |
| Compilation on the running thread | A compiler thread; actors keep running interpreted meanwhile |

## 5. The object model and memory

### 5.1 Values and references

- A value is one 64-bit word, as in the contract: low bit 0 is a 63-bit
  SmallInteger, low bit 1 a reference.
- **Proposed: a reference is a tagged address**, not an arena offset as in
  Eurasia. A field access is then one instruction (`[ref + offset - 1]`) on
  both ARM64 and x86-64. The snapshot holds node numbers, so this is
  invisible outside the VM. The cost is that the object layer of the
  runtime is `unsafe` Rust; it should be one module with a small interface.
- Floats stay boxed in the contract. **Open, deferred:** immediate floats
  would change the value encoding for both VMs. Unboxing inside optimized
  code needs no contract change and comes first.

### 5.2 Headers

Eurasia's header is three words: class, sequence number, and format, flags,
space and size. With 3.1 the sequence number goes.

**Proposed: two words.**

| word | holds |
|---|---|
| 0 | lineage id (section 5.3), class id, format, flags |
| 1 | the size of an indexable object; the hash number, or zero for none |

As built (stage 2): 24 bits each for the lineage id and the class id; 32
bits of size and a 32-bit hash field. A hash number is 62 bits, so the
field holds the common case, the count from the object's own actor, and
otherwise an index into a cohort table of full numbers (objects numbered
by another actor, or kept from an image older than version 9).

- A guard compares part of word 0 with a constant: one load, no load of the
  class object.
- A class id indexes a table of class objects. As built, the table is the
  cohort's, not an actor's: actors share objects, and whoever holds one
  must be able to find its class.
- One word is possible later (the hash kept beside the object only once it
  is asked for, the size only for indexable formats). Measure first.

### 5.3 Lineages

Each instance of an outer class has its own class objects for its nested
classes. Two such classes have the same mixins applied in the same order,
so they have the same methods, the same lookup results and the same slot
layout. They differ only in their enclosing objects.

- A **lineage** is that shared part: the sequence of mixins from a class up
  to the root. Lineages are interned in the program space and shared by
  every actor of a cohort.
- **Inline caches and guards test the lineage, not the class.** A site that
  sees the nested classes of a hundred enclosing instances sees one lineage.
- **Compiled code is customized by lineage** and holds no reference into
  any actor's heap, so one copy serves every enclosing instance and every
  actor.
- **An outer send** loads the receiver's class, then the enclosing object
  for the method's mixin application, then tests *that* object's lineage.
  Each class keeps its chain's enclosing objects in a flat vector, and the
  application's position in the chain is a constant for a lineage, so this
  is three loads and a compare. A hit binds the send to a known method.
- A program change that alters a mixin gives its applications new lineages.

This is the answer to ParserCombinators in section 18 of the compiler
design: many receiver classes, one enclosing lineage.

### 5.4 Heaps and collection

- **One heap per actor**, as in the semantics, collected independently.
  **One program space per cohort** for methods, mixins, lineages and
  compiled code; it changes only at `commit:`.
- **A nursery per actor**, allocated by bumping a pointer, sized to fit the
  second-level cache. A scavenge copies survivors; objects are promoted
  after surviving.
- **An old space** that is marked and compacted. With 3.2 its marking may
  later run concurrently.
- **A card-marking write barrier**: an unconditional byte store.
- **A large-object space** for objects too big to copy.
- **Precise roots.** Interpreter frames hold only values. Compiled frames
  have a stack map per call site.

**As built (stage 3, 2026-11-24; `eastasia-core/src/gc.rs` and the memory
layer of `object.rs`).**

- **Chunks.** Memory comes in chunks of 256 KB, aligned, so an object's
  chunk is its address with the low bits cleared. A chunk's header says
  whose it is and whether it is young, old or a large object's, and holds
  the collector's side tables. The header is 2.8% of the chunk.
- **A space** (an actor's, or the program's) is a nursery of young chunks,
  old chunks and large objects. Allocation bumps a pointer in the nursery.
  An object over 16 KB is large: it has a chunk of its own, is old from the
  start and is never moved.
- **A minor collection** copies the young objects that the roots and the
  old objects reach into the old chunks of their own space and empties the
  nursery. **An object is promoted the first time it survives.** Aging in a
  survivor space is a tuning matter, not built.
- **The write barrier** marks the card (512 bytes) of the object written,
  not of the slot: one byte store, the same for old and young objects. It
  is in the one function through which the interpreter and the natives
  write a field. A start table finds the first object of a marked card.
- **A full collection** marks, then slides the survivors down over the dead
  in address order, old objects first and the nursery's survivors after
  them. Where each object went is computed from a live bitmap and a count
  per card in the chunk header.
  - The mark is a header bit whose meaning flips at each full collection,
    so no pass clears marks.
  - A chunk in which everything is marked and before which nothing died is
    not walked. If that holds for every old chunk, only the nursery and the
    old objects with marked cards are scanned for references to update.
- **Memory goes back to the system**: chunks a full collection empties, a
  dead large object's chunk, and the part of a nursery the program did not
  use since the last collection.
- **The class table and the lineages do not keep classes or mixins alive.**
  A class's id and a lineage's id are freed when the class or a mixin dies,
  and reused.
- **Deviations from the list above, all deferred:**
  - Every space of the cohort is collected together, with the program
    stopped. Collecting one actor's heap alone waits for parallel actors
    (section 8).
  - The nursery is not sized to the cache. When to collect is still the
    interpreter's decision, forked from Eurasia: after as many allocations
    as there were live objects, a million at least. The nursery grows by a
    chunk whenever it is full. Each collection also flushes the
    interpreter's lookup cache and rebuilds its root list, so small
    nurseries wait for the interpreter work of section 6.
  - Marking is not concurrent.
- **Determinism.** What a collection keeps, and when a full one is due,
  must not depend on how memory is laid out, or a replay from a checkpoint
  would clear weak references at other points than the recording did. A
  checkpoint follows a full collection and a loaded image is sealed (all
  old, nothing dead); from there both depend only on what the program
  allocates and writes. `scripts/collector.sh` checks it.
- **Reflective queries forced full collections** until 3.2 was built:
  `allInstancesOf:`, `mixinApplicationsOf:` and `subclassesOf:` each
  collected first, 11,000 times in the kernel tests. They now walk and do
  not collect (3.2, "As built").

### 5.5 Stacks

- Each actor has its own stack, allocated by the VM. Interpreted and
  compiled frames both live on it; the machine's stack pointer points into
  it while Newspeak code runs, and the runtime switches to the thread's own
  stack when called.
- An actor is therefore not tied to a thread, a stack can be walked and
  checkpointed without the thread's cooperation, and return addresses are
  data the VM may rewrite (section 7.4).

## 6. The interpreter

- A V5 interpreter in Rust, sharing Eurasia's decoder and natives.
- **It gathers feedback.** Each method has a side vector with an entry per
  send site: the lineages seen and their targets, up to a small number,
  then megamorphic. The vector is per actor, so actors on different threads
  do not contend. The same entries are the interpreter's inline caches.
- **Counters** per method and per loop back edge.
- It is the fallback for everything: cold code, the debugger, detached
  activations, `continueAt:with:`, simulation roots, and frames the
  optimizer has given up on.
- **As built (2026-11-24; `eastasia-core/src/feedback.rs` and the send
  path of `interpreter.rs`).**
  - **A send site** is made the first time a send records something. It
    holds up to four cases: the receiver's lineage, the method, its header,
    an accessor's slot index, and where the receiver comes from. A fifth
    lineage makes the site megamorphic; its four cases stay.
  - **The site is the inline cache.** The inner loop tests the receiver's
    lineage, read from its header, against the site's cases. A miss goes to
    the lookup cache, which is now keyed by lineage too, and what that
    finds is recorded at the site.
  - **An outer or implicit-receiver send to an enclosing object** records
    the path, not the object: per level, how many superclasses up the
    mixin's application is, and the lineage the enclosing object must have
    (5.3). One case then serves every enclosing instance. Each case also
    remembers the last receiver's class id and the object found for it, so
    a repeated receiver costs one compare. Paths deeper than four levels
    are not recorded.
  - **Not recorded at a site** (the lookup cache serves them, and the site
    is flagged): `doesNotUnderstand:`, a method that is still young, a
    receiver whose class has no lineage.
  - **Counters:** activations per method, and loop turns per method, not
    yet per loop. Nothing reads them yet.
  - **Feedback lives with the method's code**, in the heap's code table,
    whose indices are now stable for a method's life. It is one per
    cohort, not yet per actor: there is one thread.
  - **Upkeep.** A minor collection leaves feedback alone: it names only old
    methods, and a lineage id that dies is not reused until feedback has
    been cleaned. A full collection in which an old object moved or died
    follows the methods and drops dead cases. A change to the program
    advances an epoch, and feedback of an earlier epoch is discarded when
    next used.
  - **The lookup cache survives minor collections** (its entries follow
    what moved). It is still flushed by a full collection.
  - **Measured, in runs per second** (release builds, `EurasiaBenchmarkApp`;
    Eurasia's native build is its interpreter):

    | benchmark | Eurasia | Eastasia before | Eastasia now |
    |---|---|---|---|
    | ClosureDefFibonacci | 25.0 | 19.6 | 23.5 | 176.4 |
    | ClosureFibonacci | 37.1 | 36.7 | 39.4 | 351.6 |
    | DeltaBlue | 102.8 | 94.8 | 103.7 | 226.7 |
    | MethodFibonacci | 51.3 | 46.4 | 50.4 | 484.5 |
    | NLRImmediate | 619.0 | 485.5 | 579.0 | 3322.0 |
    | NLRLoop | 147.0 | 132.4 | 145.1 | 1296.0 |
    | ParserCombinators | 7.8 | 6.9 | 7.7 | 23.0 |
    | Richards | 110.4 | 106.8 | 119.4 | 393.0 |
    | SlotRead | 72.2 | 68.5 | 66.7 | 1386.0 |
    | SlotWrite | 59.6 | 54.1 | 55.1 | 986.0 |
    | Splay | 155.3 | 146.8 | 170.0 | 339.3 |

    "Before" was built without Eurasia's release profile (link-time
    optimization, one code generation unit), which Eastasia's workspace
    lacked; part of the gain is that. On this suite the sites are 1,856
    with one lineage, 117 with several and 12 megamorphic.
  - **The interpreter is no faster than Eurasia's**, and slower where
    slots are read and written and closures made. It is the same loop over
    the same frames; feedback is for the compiler. What is slower has not
    been found: there is no instruction-level profile yet.
  - **Nursery size does not matter to it.** Scheduling a collection every
    30,000 to 400,000 allocations instead of every million changed no
    benchmark but Splay (down as the nursery shrinks) and cut memory held
    from 163 MB to 64 MB at the smallest. The default is still Eurasia's
    rule; `Vm::set_nursery_budget` (`EASTASIA_NURSERY`) sets it.
- **Open:** whether a baseline compiler is needed between the interpreter
  and the optimizer. Strongtalk had none. The lesson of the IDE on Eurasia
  (compiler design, section 19) is that event-driven programs spend much of
  their time in code that is warm but not hot. Decide from warm-up
  measurements, after section 9's database is in.

## 7. The optimizing compiler

### 7.1 Pipeline

1. V5 bytecode and the feedback vector become a graph in static single
   assignment form whose operations are still sends.
2. **Inlining**, driven by feedback: accessors, methods, and blocks passed to
   inlined methods. A block inlined at its only use is never allocated, and
   a non-local return from it is a jump.
3. **Guards.** Each speculation is a lineage test; the failing branch is an
   uncommon trap (7.4), not a slow path, so the code after it may assume
   the test held.
4. **Classical optimization** on the result: SmallInteger arithmetic with
   overflow checks, removal of repeated guards, removal of allocations that
   do not escape (closures, activation handles, floats).
5. Lowering to the back end, which emits machine code and its metadata:
   stack maps, scope descriptors and dependencies.

### 7.0 As built: the first cut (2026-11-24)

`eastasia-core/src/jit.rs`, and the runtime at "The compiler's runtime" in
`interpreter.rs`. Off unless `EASTASIA_JIT=n` (compile a method at its nth
activation or loop turn).

- **Compiled code runs over the interpreter's frames**, as Eurasia's
  baseline compiler does (its design, section 2). It uses the VM's operand
  stack and the frame the interpreter pushed, in the interpreter's layout.
  Wherever it calls out, the machine state is the interpreter's. **This is
  not yet the compiler of 7.1 and 7.4**: no values live in registers across
  a call, there are no scope descriptors, and there is no graph of our own.
  It is the first step that could be checked against everything section 3
  demands, and inlining can be built on it. **Confirmed** (Gilad,
  2026-11-24) as the base to build on.
- **What follows from that choice.** Collections, checkpoints inside a
  turn, population queries, the debugger and replay need nothing new.
  Leaving compiled code is a return to the interpreter's loop, which goes
  on at the frame's instruction: that is the uncommon trap. Every reachable
  instruction is an entry, so the loop enters a compiled method wherever
  the top frame is; a loop that becomes hot is entered at its next turn.
- **In line:** pushes, pops, stores, literals, branches on booleans,
  SmallInteger `+ - < > <= >= =` behind tag and overflow tests, and
  **accessor sends** where the site's feedback has one lineage: a test of
  the receiver's header against the lineage, then the slot read or written
  (with the card mark).
- **Method sends and returns in line** (added later the same day; Gilad
  confirmed the interpreter's frames as the base). Where a site's feedback
  has one lineage and it ran an ordinary method:
  - the code tests the receiver's lineage, then pushes the method's frame
    itself, field for field the frame the interpreter would push (the
    serial number included, so checkpoints agree), and calls the method's
    code directly;
  - a return writes the result where the receiver was, pops the frame and
    returns to the calling code. Where something holds the frame's
    activation, the code first marks the activation as returned, as the
    interpreter does (fourth step);
  - the callee's code address, method, literals and mixin come from a
    table the runtime keeps by code index, so a method can call itself and
    methods compiled later. The table holds nothing alive: after each
    collection its entries follow what moved, and those of dead methods
    are cleared;
  - the send falls back to the helper when the callee is not compiled yet,
    has more than 16 locals, or there is no room (frames, operand stack,
    or 10,000 nested compiled calls on the machine's stack).
- **Sites with several lineages, and some natives** (third step, same
  day). A send site is compiled from all the cases its feedback holds (up
  to four): the code tests the receiver's lineage against each in turn,
  and each case has its own action:
  - a getter or setter, a method that answers its receiver, or an ordinary
    method, as above;
  - the natives `at:`, `at:put:` and `size` on an Array (a test of the
    header, a bounds test, the card mark for a store), `==`, and
    `bitAnd:`, `bitOr:`, `bitXor:` of two SmallIntegers;
  - a receiver no case fits, or an action that meets what it does not
    cover (an index out of range, a frozen array, a byte array), goes to
    the helper, which does what the interpreter does.
  Sites the interpreter marked megamorphic still get their recorded cases.
- **Closures** (fourth step, same day):
  - `value`, `value:` and so on, where the site's feedback says the
    receiver is a closure. The code tests that the closure takes that many
    arguments and that its method's code is compiled, pushes the closure's
    frame, copies the closure's captured values onto the stack as locals,
    and calls the method's code at the closure's first instruction;
  - indirect locals (the boxed variables a closure shares with its
    method): a test that the box is an Array, a bounds test, and the card
    mark for a store;
  - **a non-local return** is still done by the interpreter, but the code
    it lands in goes on compiled. After a call in line comes back saying
    the callee left compiled code, the caller asks the runtime one
    question: is my frame on top, at the instruction after the send, with
    the stack as deep as I expect, and nothing due (a safepoint, a program
    change, stale lineages)? If so it goes on; otherwise it leaves too;
  - a closure's activation now counts toward its method's threshold.
    Before, a method that ran once and whose closure ran a million times
    was never compiled.
- **Allocation** (fifth step, same day). Compiled code allocates young
  objects itself:
  - the register block holds the nursery's next free address and the end
    of its chunk, and **an allowance**: how many objects may be allocated
    before something falls due at the allocation clock (a collection, a
    checkpoint). Code allocates in line only within the allowance, so a
    safepoint is still taken at exactly the allocation the interpreter
    would take it at; past the allowance the helper allocates;
  - whenever the runtime gets control (the helper, a return to it), it
    first takes over what the code allocated: the chunk's fill, the
    clock, the object counts. The runtime hands the room out again only
    when it lets compiled code go on;
  - the code writes every word of an object, header included. The first
    header word of a fresh activation, closure and Array is in the
    register block, refreshed after each collection (the mark bit and
    the class's ids are in it);
  - **closure creation**: the frame's activation, if nothing asked for
    it before, then the closure with its captured values;
  - **`basicNew`**: a table of 256 classes by address gives the header
    and slot count of a class whose instances are plain objects. A class
    not in it is entered by the runtime on the way to the helper, once it
    has had an instance; the table is emptied after each collection and
    each program change;
  - **`new:`** on the Array class, up to 1024 elements.
- **The non-local return** (sixth step, 2026-11-25). The code of a
  closure's `^` does what the interpreter does, itself:
  - it finds the home method's activation, from the closure outward
    through the activations that made it;
  - it walks the frames below its own for the one with that activation's
    serial number. A dead home, a frame of `ensure:` on the way, or one a
    return cannot pass (a simulation root, callback dispatch) sends it to
    the helper, which makes the upcall as before;
  - it tells the activations of the frames it pops that they are gone,
    puts the result where the home's receiver was, and returns a status
    of its own (*unwound*) to the code that called it;
  - code that gets *unwound* back from a call in line compares the top
    frame with its own: equal, and it goes on after the send as after an
    ordinary return; else its frame is gone and it passes the status on.
    No call to the runtime in either case. The runtime treats *unwound*
    as it treats a return in line.
- **Sends to enclosing objects** (seventh step, same day). A site whose
  feedback says the send runs with an object enclosing the frame's
  receiver (5.3) is compiled like any other, with the way out in the
  code: at each level, the object's class (its class id, then the class
  table, whose address is in the register block), a fixed number of
  superclass links, that class's enclosing object, and a test of its
  lineage. Then the getter, setter or method runs with the object found,
  as for a receiver on the stack. No memo: the walk is a few loads. A
  lineage that does not match goes to the helper.
- **Comparison of objects** (with the seventh step). The `==` calls
  that went to the helper were sends of `=` and the other selectors
  whose instruction has a SmallInteger path in line: when the operands
  were not SmallIntegers, that path went straight to the helper and
  never looked at the site's feedback. It now goes on to the site's
  cases (for most classes `=` is the identity native), and to the helper
  only after them.
- **Sites that learn after their method is compiled** (eighth step,
  2026-11-25). Two things, which only work together:
  - *Compiling again.* When a send from compiled code reaches the
    interpreter and its site records a lineage it had not seen (or
    becomes megamorphic), the method's code is marked stale. Each later
    call from that code to the helper counts; at 100 (or the compile
    threshold, if that is more) the method is compiled again from what
    its sites now know, at most four times. The new code replaces the
    old in the table of targets, so callers in line reach it at once;
    the helper sends the frame it was called for back to the loop, which
    enters the new code at the frame's instruction. Other frames in the
    old code finish there. Nothing else is discarded.
  - *A table for megamorphic sites.* A site that has seen more lineages
    than it has cases gets a number when its method is compiled (a new
    one at each compilation). After the cases, the code looks up (site
    number, receiver's lineage) in one table of 8192 entries, direct
    mapped, whose address is in the register block. An entry says what
    the send runs: a getter or setter and its slot, or a method by the
    index of its code and its count of locals; and, for a send that runs
    with the object one level out, the superclass links and that
    object's lineage. A hit does in line what a case would. A miss goes
    to the helper, and the interpreter, which records nothing more at a
    megamorphic site, writes the entry. The table holds no reference; it
    is cleared whenever compiled code is discarded.
  Giving every site a number, so that no recompilation is needed, was
  tried and measured: it works, but the lookup's code in every send made
  call-heavy methods 3 to 6 percent slower, wherever the code was put.
- **Arithmetic and comparison the first cut left out** (ninth step,
  2026-11-25). The profile's "`<` at a site with no feedback" was a
  misreading: instruction 178 is `*`. A common send of two SmallIntegers
  never reaches a site in the interpreter, so it records nothing, and
  the compiler took only `+`, `-` and the comparisons in line; `*`,
  `//`, `\\`, `<<`, `>>`, `&` and `|` each called the helper. All
  fourteen are now in line, with the interpreter's conditions: a result
  that is not a SmallInteger, a zero divisor, a shift out of range and
  (here only) a divisor of -1 go to the site's cases or the helper. A
  unit test runs the compiled code for each of the seven on 625 pairs of
  edge values against the interpreter's rule. Two more cases at sites:
  the comparison natives and `=` of a Float with a Float (the `<` and
  `>` calls were these), and `quo:` and `rem:` of two SmallIntegers.
- **`size` and `at:` of a String or ByteArray** (tenth step,
  2026-11-25). The two cases that took an Array in line now take these
  too: the size is the number of bytes, and `at:` answers the byte as a
  SmallInteger, under the same check of the index.
- **Array literals** (eleventh step, 2026-11-25). The two instructions
  that make an Array, of nils or of the operands on top, write it in the
  nursery as `new:` does; its size is in the instruction, so the stores
  are straight-line code. No room, or no allowance: the helper.
- **String concatenation** (twelfth step, 2026-11-25). `,` of a String
  with a String, when the result is at most 1024 bytes: the fresh
  String's header (which the register block now holds, as it does an
  Array's) and size are written in the nursery, and a small function of
  the runtime, called directly, copies the two bodies and zeroes what
  is left of the last word. Longer results, no room, no allowance: the
  helper.
- **`numArgs` and `valueWithArguments:`** (thirteenth step,
  2026-11-25). `numArgs` of a closure reads the count from the closure.
  `valueWithArguments:` is the code of `value:` with the arguments
  taken from an Array: the operand must be an Array whose size is the
  closure's count; its elements are copied onto the stack where
  arguments go, then the copied values, and the closure's compiled body
  is called. Anything else, or a body not compiled: the operands are
  put back and the helper runs the send.
- **Through one helper:** every other instruction: sends to receivers no
  case fits, other natives, a non-local
  return that meets `ensure:` or cannot complete. The helper runs it as the interpreter would, on the
  interpreter's own fast path, then runs a compiled callee natively, and
  tells the compiled code whether it may go on.
- **Nothing compiled refers to the heap.** Literals, the receiver, nil,
  true and false are read through the frame and a small block of registers
  the runtime refreshes. Lineage ids are in the code as constants.
- **Invalidation** is of everything at once: a program change, or a full
  collection that gives lineage ids back. Code is unmapped when no compiled
  frame is left. While lineages in headers are stale, compiled code is not
  entered.
- **The clock.** A safepoint that falls due inside compiled code is taken
  where the interpreter would take it: the helper sends the code back to
  the loop before the next instruction.
- **Checked** (`scripts/agree.sh`, section "the compiler"): the kernel
  tests' outcomes; Eurasia's recordings replayed compiled, from the start,
  from a checkpoint and under collector stress with the heap verified; a
  recording made compiled, replayed on Eurasia; the IDE session; and, with
  `JIT_GATE=1`, replay with every method compiled at its first activation.
- **Measured**, runs per second, threshold 100:

  | benchmark | interpreted | accessors | method sends | several lineages, natives | closures | allocation | non-local return |
  |---|---|---|---|---|---|---|---|
  | ClosureDefFibonacci | 23.5 | 24.0 | 29.0 | 28.8 | 63.5 | 179.4 |
  | ClosureFibonacci | 39.9 | 39.7 | 39.1 | 39.6 | 337.6 | 353.6 |
  | DeltaBlue | 101.3 | 106.2 | 143.4 | 195.6 | 217.3 | 233.0 |
  | MethodFibonacci | 50.9 | 67.3 | 482.0 | 485.5 | 458.0 | 480.0 |
  | NLRImmediate | 577.4 | 568.4 | 729.2 | 721.0 | 1045.0 | 1578.0 |
  | NLRLoop | 144.8 | 189.8 | 207.1 | 310.6 | 711.0 | 929.0 |
  | ParserCombinators | 7.5 | 7.5 | 7.6 | 8.0 | 18.1 | 22.8 |
  | Richards | 116.7 | 120.6 | 169.0 | 285.7 | 345.0 | 404.5 |
  | SlotRead | 66.7 | 1215.0 | 1421.0 | 1372.0 | 1224.0 | 1404.0 |
  | SlotWrite | 53.3 | 999.0 | 935.0 | 967.0 | 890.0 | 983.0 |
  | Splay | 161.6 | 176.8 | 210.0 | 242.5 | 270.2 | 338.3 |

  One run each; the closures column was measured while the checks were
  running on the same machine, so part of the last step's gain is that
  the machine was idle (compare MethodFibonacci and the slot benchmarks,
  which the step does not touch). Against the interpreter:
  MethodFibonacci 9.5 times, NLRLoop 9.0, ClosureFibonacci 8.8,
  ClosureDefFibonacci 7.5, NLRImmediate 5.8, Richards 3.4,
  ParserCombinators 3.1, DeltaBlue 2.2, Splay 2.1. The sixth step
  moves only the two NLR benchmarks (NLRImmediate 2.1 times the fifth
  step's figure, NLRLoop 1.4); the rest are within a run's noise.
  The seventh step, measured against the sixth with both run back to
  back on a busy machine (so not in the table): Richards 382 to 765,
  DeltaBlue 221 to 275, Splay 318 to 358, the rest unchanged; with the
  comparison of objects, DeltaBlue 392, Splay 447, ParserCombinators
  22 to 26. The eighth step against the seventh, back to back, two runs
  each: DeltaBlue 415 to 735, Splay 456 to 526, ParserCombinators 26.8
  to 34.2, the rest within a run's noise. Helper calls over the whole
  benchmark run, 105 million to 67 million (counted without the
  profile, which slows the helper; the figures below are with it).
  The ninth step against the eighth, the same way: DeltaBlue 747 to
  779, Richards 792 to 826, Splay 539 to 557, ParserCombinators 34.7 to
  35.4, the rest within a run's noise. The tenth against the ninth:
  ParserCombinators 35.1 to 43.6, the rest unchanged. The eleventh
  against the tenth: ParserCombinators 43.0 to 46.0, the rest unchanged
  (Splay varies between 525 and 590 from run to run on either build).
  The twelfth against the eleventh: Splay 534 to 938, the rest
  unchanged. Helper calls over the whole run, counted without the
  profile: 23.6 million to 12.2 million. The thirteenth against the
  twelfth: ParserCombinators 46.9 to 59.4, the rest unchanged (Splay
  904 against 936, within what it varies by).
- **What still calls the helper** (`EASTASIA_JIT_PROFILE=1` counts its
  calls by kind; measured before the third step, 128 million calls):
  closure `value` 28 million, closure creation 19 million, returns from
  frames whose activation a closure holds 10 million, non-local returns 9
  million, indirect locals 9 million; then array access and `==` 21
  million and sites with several lineages 8 million;
  getters of enclosing objects 6 million. All but two of these are now
  in line. What is left after the fifth step (104 million calls): the
  non-local return itself, 54 million; `==` at sites the compiler does
  not yet take in line, 14 million (not yet understood); getters and
  methods of enclosing objects, 15 million; megamorphic sites, 5
  million; string concatenation, comparisons the arithmetic path does
  not catch, array literals. After the sixth step, 47 million: `==`
  12 million (still not understood), getters and methods of enclosing
  objects 13 million, megamorphic sites 5 million, string concatenation
  2 million, `size` and `at:` sites that fall to the helper 4
  million. After the eighth step, 31 million, no megamorphic site among
  them: `<` at sites that never record feedback 4 million (one site
  nearly all of it) and at sites that do 2.5 million, string
  concatenation 5 million, `size` and `at:` 3 million each, array
  literals 2.5 million, integer division 2 million, `>` 2 million,
  `valueWithArguments:` and `numArgs` 1.3 million each. After the
  ninth step (the profile now names the receiver's kind and the
  instruction), 14 million against 20 million in a run of the same
  length before it: string concatenation 5 million, `size` and `at:`
  of a String 1.9 million each, array literals 1.7 million,
  `valueWithArguments:` and `numArgs` 0.8 million each, a Float's
  `asString` 0.6 million, ordinary methods of SmallInteger (which no
  case calls in line) 0.6 million. After the tenth step the String
  `size` and `at:` calls are gone, and after the eleventh the array
  literals: 11 million left, of which string concatenation 5 million,
  `valueWithArguments:` and `numArgs` 1.9 million each. After the
  twelfth, 6 million: those two, a Float's `asString` 0.9 million,
  ordinary methods of SmallInteger 0.6 million. After the thirteenth,
  2.5 million, and entries into compiled code from the interpreter's
  loop fall from 345 thousand to 70 thousand: a Float's `asString` 0.8
  million, ordinary methods of SmallInteger 0.6 million, an Array's
  `replaceFrom:to:with:startingAt:` 0.4 million, Float division and
  `asFloat` 0.2 million each.
- **A fault found on the way.** The native that replaces a method's
  bytecode left the old compiled code and its table entry in place. It
  now discards compiled code, like any other program change.
- **Program changes are now the worst cost.** The kernel tests, which
  change the program constantly, take 12 minutes at threshold 30 against
  13 seconds interpreted: every change discards all code, which is then
  compiled again. Dependencies (7.6) are the cure; a cheaper first step is
  to raise the threshold after each discard.
- **Next, in order of what the numbers say:** methods of SmallInteger
  called in line; Float division and `asFloat`; discarding
  less on a program change; then the graph and inlining of 7.1, which is where values start
  to live in registers and where a closure that does not escape need not
  be created at all.
- **Not done:** freeing the code a recompilation replaces before the
  next discard (a full region of code is in fact never unmapped, which
  recompilation makes more of); enclosing objects more than one level
  out at megamorphic sites; compiling on another thread;
  per-loop counters; on-stack replacement as such (entries at every
  instruction do its work); dependencies (7.6); compiled code inside a
  callback that the host makes during a turn.

### 7.2 The back end

**Decided: Cranelift, if feasible. Checked 2026-11-23 against
cranelift-codegen 0.138: feasible, in one particular style.** We drive
`cranelift-codegen` directly and own the code memory; `cranelift-jit` does
not handle hardened macOS processes.

What it gives:

- **Stack maps for a moving collector** ("user stack maps"): marked values
  are spilled before each call and reloaded after it. Wasmtime's copying
  collector runs on this in production.
- Tail calls, on ARM64 and x86-64.
- Frame pointers always kept, each function's stack-slot layout exported,
  and a register reserved for the VM.
- Calls with an exceptional successor (`try_call`), and opaque tags on
  call sites that survive optimization.

What it does not give, and what that fixes in our design:

- **No record of where a value lives at a guard.** There is nothing like
  LLVM's deoptimization operands. So a failed guard branches to a cold
  block that calls the runtime with the interpreter state as arguments
  (7.4). The register allocator keeps those values alive only on the cold
  path.
- **Only calls are safepoints and deoptimization points.** No guards by
  trap.
- **Inline caches in data**, which is what 7.3 already says.
- Code quality is below LLVM's at full optimization, and Cranelift does no
  inlining for us. Ours is done on our own graph, so this matters less.
- The interface changes monthly, and nobody has shipped a deoptimizing
  compiler for a dynamic language on it. This is the main risk.

Fallback if the cold-path scheme costs too much: our own back end on
`regalloc2`, where live values can be made operands of the deoptimizing
instruction. The front and middle of the compiler, where Strongtalk's
knowledge is, do not depend on the choice.

Not yet checked: running Cranelift's code on a stack the VM owns (5.5).

### 7.3 Inline caches in compiled code

A send the compiler did not inline has a cache in data beside the code: a
lineage and a target. Polymorphic sites test a few entries in line.
Nothing in the code is patched after it is emitted.

### 7.4 Deoptimization

- **Scope descriptors** record, for each point where compiled code can
  stop, the interpreter frames it stands for: which methods, at which
  bytecode, with each value in a register, a stack slot, a constant, or an
  object not yet allocated.
- **An uncommon trap** calls the runtime, which replaces the compiled frame
  with those interpreter frames, allocating what was elided. With
  Cranelift (7.2) the trap is a cold block that passes the state as
  arguments, so the descriptor says which argument is which, not which
  register.
- **Invalidation** of frames up the stack (a program change, a broken
  dependency) rewrites their return addresses to a deoptimizing stub. The
  stack is the VM's own, so this patches data, not code. To check: return
  address protection (pointer authentication, shadow stacks) where the
  platform enforces it. With Cranelift, the state of a frame that is not on
  top must be readable too: either every send is a `try_call` whose handler
  block passes the state on, or the state at a send is kept in stack slots
  whose layout Cranelift exports. To measure which costs less.
- **Activation mirrors read through the descriptors** without deoptimizing.
  An exception's search for a handler is such a read. Only a write
  (`tempOf:at:put:`, `senderOf:put:`) deoptimizes the frame.
- **Checkpoints and population queries** see optimized frames through the
  same descriptors.

### 7.5 When to compile

- A method or loop counter crossing its threshold asks for compilation. The
  compiler looks up the callers for the outermost method that would inline
  the hot one.
- Compilation runs on a compiler thread. The actor continues interpreted,
  and enters the new code at its next call, or in a running loop by
  on-stack replacement.
- An uncommon trap that fires repeatedly causes recompilation with the new
  feedback.

### 7.6 Program changes

`commit:` is frequent in the IDE: every method edit is one. Flushing all
compiled code at each, as Eurasia does, would keep an optimizing VM
permanently cold.

- **Proposed: dependencies from the start.** Compiled code records what its
  inlining relied on: that lineage L answers selector S with method M. A
  commit invalidates only the code whose dependencies it breaks.
- **To settle:** the semantics describes `reclassify:as:` and
  `slotOf:at:put:` as one-command commits. Since slots are not folded, a
  slot store invalidates nothing. A reclassification changes an object's
  header under code that may already have tested it, so it must invalidate
  the frames that hold that object's guard, in the simplest form every
  optimized frame of the actor.

## 8. Actors and processors

- An actor's heap, stack and feedback are its own, so **actors can run on
  different threads at once** with no shared mutable state but the program
  space, which is frozen between commits.
- A commit, a population query and a checkpoint bring the cohort to a
  safepoint.
- **Replay with parallel actors: log the deliveries** (Gilad's leaning,
  2026-11-23; I see no strong argument against). Eurasia runs one actor at
  a time in a fixed order, so message arrival order is determined. On
  several threads it is not, so the order of deliveries to each actor is an
  input, recorded as (receiving actor, sending actor, the sender's message
  count). The cost is a few bytes per message, only while recording, and a
  replay can still run actors in parallel: each waits for the delivery the
  log names next. Croquet model code runs in one actor, so it is
  unaffected.
- **What logging deliveries does not cover:** the operations that stop the
  cohort. A commit or a cohort-wide population query takes effect while
  other actors are in the middle of turns, and a replay must stop each at
  the same point. The logical clock of 3.4 can name the point, but stopping
  compiled code at an exact count is costly. Proposed: while recording,
  such an operation waits until every other actor is between turns, and
  the log records which turn. Not recording, it stops them at any
  safepoint.
- The first hash of a shared object is the other such input (3.1).

## 9. Snapshots and warm-up

- Eastasia reads and writes the shared format. Compiled code is never
  saved: a snapshot stays independent of the VM.
- **The inlining database.** An optional section holds feedback: for each
  hot method, the lineages its sites saw (as mixin chains, which are
  portable) and the inlining decisions taken. A restored image compiles its
  hot methods at once, on the compiler thread, instead of rediscovering
  them. Eurasia skips the section.

## 10. Interactive applications: the FFI and the GUI

### 10.1 What interactive use asks of the VM

- **Short pauses before throughput.** A frame is 8 to 16 ms. The nursery
  must scavenge in well under a millisecond, and old-space marking should
  become concurrent (3.2 allows it).
- **Fast start and fast warm-up**: loading a snapshot quickly, and the
  inlining database of section 9.
- **The UI actor runs on the main thread, driven by the Cocoa run loop**,
  as Eurasia's turns are driven by the browser's events.
- **Distribution.** Generating code on macOS needs the allow-jit
  entitlement. iOS forbids it, so if iOS is ever a target the interpreter
  must be good enough alone.

### 10.2 The foreign function interface

Proposed, macOS first:

- **Objective-C first.** A Newspeak keyword selector is an Objective-C
  selector, and the Objective-C runtime answers each method's type
  signature. An Objective-C alien forwards a message it does not
  understand, as the JavaScript alien does, and needs no declarations.
- **C** functions need declared signatures, structures passed by value, and
  callbacks. A callback is a generated thunk, which is code written at run
  time and so subject to the same rules as compiled code.
- **Lifetimes.** An alien retains its object and releases it when
  finalized. Aliens die on restore, as in the contract.
- **Replay.** A foreign call is a host operation and is logged with its
  result. Memory read through a foreign pointer is logged too.
- **Speed.** A general call path first. Later the optimizer inlines the
  marshalling at hot call sites.

### 10.3 The GUI

**Decided:** Eastasia's GUI draws on a canvas, as Glamorous Toolkit does,
with the platform's own toolkit used only for the shell.

- **The model is a retained scene tree** in the manner of SVG: paths, text,
  images, groups, transforms and clips. Hopscotch gets a binding to that
  tree, beside its bindings to HTML5 and to Brazil.
- **Layout, hit testing, text editing and scrolling are Newspeak code** over
  the tree. This is the workload a fast VM is for.
- **The shell is AppKit, through the Objective-C bridge**: windows, menus,
  dialogs, the clipboard, and keyboard and input-method events.
- **The first renderer on macOS is CoreGraphics with CoreText**, through
  the FFI: no new dependency, and it exercises the FFI. A portable renderer
  on the graphics processor can replace it later behind the same tree; the
  candidates are to be assessed then.
- **To build ourselves:** text editing with input methods, accessibility,
  and scrolling. These are the costly parts of this route.

### 10.4 Documents and code editing

**Decided** (Gilad, 2026-11-23):

- **Emmanuel replaces the HTML in Ampleforth**, very soon.
- **Emmanuel then replaces CodeMirror** as the code editor.

So the IDE's ties to HTML (Ampleforth's editable HTML, CodeMirror, the
browser's editing events under the Emmanuel live editor) reduce to one: how
Emmanuel's presenters and its edit layer reach the screen and the keyboard.
Emmanuel's edit layer is specified apart from the DOM, and its blocks
render through presenters, so its native form is those presenters over the
scene tree, with carets, selection and key events supplied by the canvas
binding in place of the browser.

### 10.5 Order of work

1. On Eurasia, in the browser, now: Emmanuel in Ampleforth, then Emmanuel
   as the code editor. Both are planned regardless of Eastasia.
2. On Eurasia, in the browser: the scene tree, backed by SVG or a canvas
   element, and Hopscotch's binding to it. The IDE can be tried on it long
   before Eastasia runs.
3. On Eastasia: the Objective-C bridge, the AppKit shell, and the
   CoreGraphics renderer behind the same tree.

## 11. Testing

- **Eurasia is the oracle.** The same image and the same replay log, run on
  both, must give the same outputs and byte-identical checkpoints. This is
  the strongest test an optimizer can have, and it is the practical reason
  for section 3.
- Eurasia's gates carry over: every method compiled at its first
  activation; collection at every allocation; and, new here, deoptimization
  at every point that allows it.
- The kernel tests, the typechecker tests and the benchmark suite, as now.

## 12. Shared code

Eastasia and Eurasia should share crates, not fork them: the snapshot
reader and writer, the bytecode decoder, large integers, the float library,
the pure parts of the natives, the natives catalog and the replay log
format. Agreement on these is then by construction.

## 13. Stages

1. **The contract revision** (section 3) in the semantics, in Eurasia and
   in the snapshot format; the shared crates extracted.
   - Done on Eurasia's branch `contract-v9` (worktree
     `dev/web/eurasia-contract`, uncommitted): hash on first request,
     classes numbered at creation, canonical order for images and for
     `allInstancesOf:`, optional sections, format version 9 reading 8. The
     unit, kernel, reflection, web and replay tests pass.
   - Left: `kernel-semantics.tex`; weak clearing as logged input (3.2, not
     needed until the two VMs replay each other's logs); the packager
     writing version 9; the IDE image measured for load time and locality;
     the shared crates.
2. **A running VM**: object model, loader, interpreter with feedback,
   natives, one actor. It passes the kernel tests and agrees with Eurasia.
   - **Running, 2026-11-24**, in its own workspace, `dev/web/eastasia`
     (Eurasia's main branch is not to change yet; the workspace depends on
     the `contract-v9` worktree for the crates it shares).
   - Its own: tagged-address values, two-word headers with class id and
     lineage, a space per actor, the class table and the lineages.
   - Forked from Eurasia (decided 2026-11-24: fork, do not put Eurasia's
     heap behind a trait): the natives, the interpreter, replay, the image
     builder, the host and the command-line program. Eastasia's heap offers
     the interface Eurasia's has, so `natives.rs`, `replay.rs` and
     `builder.rs` are byte-for-byte copies; the interpreter is a copy with
     the wasm compiler's hooks cut out. The snapshot reader and writer,
     the bytecode decoder, large integers, roles and the host interface
     are used from Eurasia's crates, not copied.
   - `scripts/agree.sh` checks agreement with Eurasia: genesis writes the
     same base image byte for byte; the 620 kernel tests have the same
     outcomes and messages; a log recorded on either VM, with checkpoints,
     replays on the other from its start and from a checkpoint.
   - The kernel tests take 13 s on Eastasia and 21 s on Eurasia's
     interpreter (one run each, release builds).
   - **Feedback and lineage caches: done 2026-11-24** (section 6, "As
     built"). `scripts/agree.sh` and `scripts/collector.sh` pass with them;
     the heap check now covers feedback.
   - **Not yet:** frames are Eurasia's, not on a stack the VM owns; one
     thread; feedback is per cohort, not per actor. Snapshots and checkpoints are written
     by converting the heap to Eurasia's and using its collector and
     writer.
3. **Memory**: the generational collector, the barrier, checkpoints and
   replay.
   - **The collector is built, 2026-11-24** (section 5.4, "As built"):
     nursery, promotion, card marking, large objects, sliding compaction.
   - The kernel tests took 13.5 s and peaked at 105 MB resident (Eurasia:
     21 s and 99 MB; the stand-in collector it replaces: 13.3 s and 215 MB).
     Of the 13.5 s, 8.2 s were the 11,324 full collections that the tests'
     reflective queries force: 4.0 s marking, 4.2 s compacting. With
     feedback (section 6) they take 14.7 s: each of those collections now
     also walks the send sites, which adds a second in all.
   - `scripts/collector.sh`: the kernel tests with a collection every
     5003, 997 and 101 allocations (up to 23,000 minor and 19,000 full
     collections) have the same outcomes, with the heap checked before and
     after every collection (`EASTASIA_GC_VERIFY`); a recording made under
     stress replays under the same stress from its start and from three
     checkpoints.
   - `scripts/agree.sh` still passes: genesis byte for byte, the kernel
     tests, replay in both directions.
   - **Left in this stage:** checkpoints and snapshots written from
     Eastasia's own heap (they are still converted to Eurasia's); weak
     clearing as logged input (3.2), without which the two VMs agree only
     on programs that do not observe weak references between explicit
     collections. (The weak clearing log is since built, 3.2.)
   - **The IDE image runs** (2026-11-24), by replay: a session recorded in
     a browser on Eurasia's wasm build (the IDE started, classes browsed,
     two test suites run in it; 1,344 top-level events, four checkpoints)
     replays on Eastasia from the start and from each checkpoint, reaching
     Eurasia's digests, also with the heap verified and with extra
     collections. `scripts/agree.sh` replays `target/ide/session.eurl`
     when it is there. Eastasia has no host with a browser, so it has not
     run the IDE live.
4. **The compiler, first cut**: the back-end decision, the graph, guards and
   uncommon traps, inline caches, sends not inlined. MethodFibonacci and
   Richards.
   - **Begun 2026-11-24** (7.0, "As built"): Cranelift drives real machine
     code on Apple silicon; compiled code agrees with the interpreter and
     with Eurasia on every check; accessor sends, method sends and
     returns, sites with several lineages, some natives, closure
     calls and allocation are in line. MethodFibonacci is 9.4 times the
     interpreter, ClosureFibonacci 8.9, Richards 3.5. No graph of our own yet.
5. **Inlining**: methods and blocks, lineage customization, outer sends,
   on-stack replacement, invalidation by dependency.
6. **Then**: allocation removal, float unboxing, the inlining database,
   actors on several threads.

The FFI can start after stage 2, and the GUI work of 10.5 runs alongside
all of these, its first two steps on Eurasia.

## 14. Open questions

- **Settle:** the root order of the canonical walk (3.3), and the list of
  events that tick the logical clock (3.4), in the semantics.
- **Settle:** cohort-wide operations and the first hash of a shared object
  under recording with parallel actors (section 8).
- **Check:** Cranelift's code on a VM-owned stack, and the cost of passing
  interpreter state on cold paths (7.2). The first cut (7.0) sidesteps
  both: Newspeak frames are the interpreter's, in VM memory, and the
  machine's stack holds only the nesting of compiled calls.
- **Confirmed** (Gilad, 2026-11-24): compiled code over the interpreter's
  frames as the base for the optimizer (7.0).
- **Deferred:** immediate floats; a baseline compiler; a one-word header.
- **Benchmarks for interactive use.** The suite measures throughput. An
  interactive VM is judged by frame times and pauses: typing in an Emmanuel
  document, scrolling, opening a browser. These probes need defining.
- **The portable renderer** (10.3), and when a second platform matters.
- **Accessibility and input methods** on the canvas (10.3): how much, and
  when.
