# New VM: implementation plan

**Date:** 2026-11-17
**Status:** Accepted 2026-11-17 (decisions in section 9). M0 in progress.
**Specification it implements:** `VM_KERNEL_CONTRACT_DESIGN_2026-11-09.md` (the
contract and its decisions), `VM_KERNEL_OPERATIONS_2026-11-10.md` (the
operation list), `formal-semantics/kernel-semantics.tex` (section 13, the
rules), and `BYTECODES_V5_SPEC_2026-07-13.md` (the instruction set, refined
as the contract allows).

---

## 1. Shape of the work

Three pieces, built together from the first milestone:

1. **The VM**, in Rust: object model, per-actor heaps, V5 interpreter,
   natives, kernel operations, host interface. One code base for native and
   WASM.
2. **The packager**, in Newspeak, running on today's system (V4 on psoup):
   compiles sources with `Newspeak2V5BytecodeCompilation`, builds the new
   VM's object graph (hybrid layouts, roles, native methods), and writes it in
   the new snapshot format. This is the bootstrap the design doc chose
   (section 7): no converter, no port of psoup.
3. **The kernel module for the new VM**, forked from `KernelForPrimordialSoup`:
   the same classes, but every `primitive:` pragma removed. The packager marks
   the methods that become natives from a table (section 4), so natives are
   bestowed by the image builder, which holds full authority, and never
   appear in source.

After the new VM can run its own compiler, the packager runs on the new VM
and psoup leaves the loop.

## 2. Architecture

### 2.1 Crates

| Crate | Contents |
|---|---|
| `nsvm-core` | Values, object model, heaps and GC, the program space, the V5 interpreter, natives, kernel operations, roles, failure path. No I/O, no host types; `#![no_std]`-friendly so it builds for wasm32 unchanged. |
| `nsvm-snapshot` | Reading and writing the snapshot format (section 3). |
| `nsvm-host` | The host-interface trait: calls, callbacks, timers, the event-loop hook (`finishTurn:`), clocks, entropy, output. |
| `nsvm-native` | Command-line VM for macOS and Linux: loads a snapshot, runs to `exit:`. Later the C FFI. |
| `nsvm-web` | wasm32 build with the JS host: call-based alien operations, expats, callbacks. |
| `nsvm-replay` | Later (M7): input/output log, checkpoints, divergence detection. |

### 2.2 Values

- **64-bit tagged words on every target**, including wasm32. SmallInteger
  range is then the same everywhere, which bit-identical replay and Croquet
  need; psoup's word-sized SmallIntegers differ between wasm32 and native.
- Immediates: SmallInteger (63-bit) and object references. Floats are boxed,
  as in psoup, with canonical NaN (decided).
- `nil`, `true`, `false` are objects whose identities are roles.

### 2.3 Heaps and the program space

Following the formal semantics (decided: it takes precedence over psoup):

- **One heap per actor**, holding its objects, class objects, activations and
  closures. Collection is per actor and needs no cross-actor coordination.
- **One program space per cohort** for installed methods and mixins. They are
  frozen, so all actors share them without locks. Commit (section 6 of the
  operation list) is the only writer.
- **Object references are indices, not pointers.** Each heap is an arena; a
  reference is (space, offset). This keeps the Rust safe without a tracing
  borrow scheme, makes relocation explicit, and is what a snapshot stores
  anyway. Allocation order is the identity order; each object header carries
  its allocation sequence number, which is the identity hash (decided:
  deterministic), so moving collection does not change it.
- **Collector:** start with a per-actor copying collector (Cheney), with weak
  arrays and ephemerons handled as the GC layer of the semantics specifies.
  Each collection's clearings are logged as input once replay exists (M7;
  the logging decision is still open). *Decided by M7 (2026-11-18): not
  logged; collections run on an allocation schedule that checkpoints save,
  so replay clears at the same points.*

### 2.4 Interpreter

- V5 bytecode exactly as specified, with these refinements (allowed by the
  contract): method headers carry a *kind* (ordinary, native, getter, setter,
  return-self) and a native identity instead of a primitive number; the
  `pushClosure` arity is a 4-bit nibble everywhere (fixing upstream's 3-bit
  decode); the short branch-false range decodes as branch-false.
- Frames live on a Rust-managed stack (a `Vec` of words per actor). Activations
  are **handles**, reified on demand (hidden layout, decided), so the frame
  representation stays the VM's business.
- Sends go through a global lookup cache keyed by (class, selector), flushed
  by commit. Inline fast paths for SmallInteger arithmetic, comparisons and
  `at:`/`at:put:`/`size` on the common-send opcodes come in M8, guarded by
  "the method found is still the bestowed native".
- Interrupt and resource checks at activation and backward branches, as V5
  specifies. Every bound (heap, stack depth, callback depth, handle table)
  produces `exhausted:` through the failure path, never a crash.

### 2.5 Natives

- A Rust `enum Native` is the catalog of one kernel version. Each variant has
  its arity, scope (local or cohort), effect class and a function returning
  `Answer | TailSend | Fail(reason)`, exactly the three outcomes of rules
  Native-Answer, Native-Tail and Native-Fail.
- `Fail` allocates an instance of the failure exception class (a role) and
  sends it `signal`. There are no fallback bodies.
- Cohort natives (the kernel operations) are methods of the VM-mirror class;
  holding the mirror is holding them.

### 2.6 Host interface

- Native: a Rust trait implemented by the CLI host (files, clocks, stdout).
- Web: JS imports for the call-based alien operations (`at:`, `at:put:`,
  `call:withArguments:`, `newWithArguments:` …). Exact marshalling, no
  operand stack. Callbacks enter through one exported function, push a
  boundary frame, and never drain the queue (decided). Nesting is bounded.

## 3. Snapshot format

A new format, versioned, modelled on PrimordialFuel's cluster graph (psoup:
magic `0x1984`, version 0, a 516-line C++ loader, serializer in Newspeak).

- Header: magic, **kernel version, bytecode version**, word size (always 64).
  A VM refuses a mismatch with a clear message (design doc section 7).
- Sections: roles; program space (mixins and methods, already frozen); one
  heap per actor, with paused stacks once M7 exists.
- Objects are written in allocation order, so load preserves identity order
  and identity hashes.
- No VM-private fields (class ids, caches) are stored; the loader rebuilds
  them.

The format is specified in a short document before code (M0), and the
packager and the Rust reader are tested against each other.

## 4. Natives table and the kernel fork

The packager holds a table mapping (class, selector) to a native name, built
from section 3 of the operation list (75 value natives) plus the kernel
operations on the VM-mirror class. For each entry it installs a Method whose
kind is native, with no bytecode. A method in the table that is missing from
the kernel, or a kernel method left without a body, is a packaging error.

The kernel fork starts from `KernelForPrimordialSoup.ns` and changes:
- primitive pragmas removed; bodies that were fallbacks deleted, except
  `Integer>>/`, which becomes an ordinary method (operation list 3.1);
- `Number>>=` answers false for non-numbers (decided);
- activation and closure internals go through the activation-mirror
  operations instead of public `Activation` methods;
- the four marker primitives become roles.

## 5. Testing

1. **Unit tests in Rust**, per instruction and per native, including each
   failure reason.
2. **Snapshot round trip**: packager writes, Rust reads, Rust writes, bytes
   compared.
3. **Differential tests against psoup**: the same test sources, V4 on psoup
   and V5 on the new VM, compared by output. The first target is the kernel
   test suites (`KernelTests`, `CollectionsTesting`, …) run headless by
   Minitest. Differences must be explained by a decided semantic change
   (for example `Number>>=`), each listed in an expected-differences file.
4. **Semantics conformance**: the SpecTec native-method regressions as Rust
   tests over the same three-entry test catalog; more as the transcription
   grows.
5. **Resource limits**: each bound is exercised and must produce its defined
   failure (the 2026-11-09 triage found corruption at three of them in psoup).

## 6. Milestones

| | Milestone | Done when |
|---|---|---|
| M0 | Toolchain, repository, crate skeleton, CI; snapshot format document | `cargo test` passes on native and wasm32; format reviewed. |
| M1 | **First light**: packager emits a minimal image (a tiny kernel subset); the VM loads it and runs sends, SmallInteger natives, the failure path, `print:` and `exit:` | `3 + 4` prints `7`; `3 + nil` raises through the failure class. |
| M2 | Full kernel: closures, non-local return, `ensure:`/`on:do:` roles, DNU, collections, strings | Kernel test suites pass differentially against psoup. |
| M3 | Collector: copying GC, weak arrays, ephemerons, deterministic identity hash | Kernel weak tests pass; stress test with collection on every allocation. |
| M4 | Actors: ports, turns, spawn from a mixin, the message loop, `finishTurn:` | Actor test suites pass. |
| M5 | Web host: wasm32 build, call-based JS FFI, expats, callbacks | A Hopscotch demo (CounterApp) runs in the browser. |
| M6 | Reflection: `commit:` with layout maps, activation operations, pause and stack replacement; the Simulator over natives | The mirror and atomic-install test suites pass; the IDE boots. |
| M7 | Snapshots, restore, replay log, checkpoints, divergence detection | Save and restore with paused stacks; replay of a recorded IDE session reproduces its outputs. **Met 2026-11-18** (`EURASIA_M7_SNAPSHOTS_REPLAY_DESIGN_2026-11-18.md` section 6). |
| M8 | Performance: inline fast paths, then measure against psoup | Benchmarks within an agreed factor of psoup (the design doc's efficiency question). |

The packager is self-hosted (runs on the new VM) after M6.

**Progress (2026-11-17):** M0 and M1 done. M1a: the Rust loader and
interpreter core. M1b: `EurasiaPackager.ns` compiles `EurasiaFirstLight.ns`
with the V5 compiler on psoup and writes a snapshot that Eurasia runs
(`eurasia/scripts/first-light-from-source.sh`). Findings: accessor slot
indices are relative to their mixin (the semantics' `(C, j)`), because
methods are shared through mixins; psoup builds images by running the
program, which cannot work for V5 on psoup, so the packager builds classes
statically, and **how a module-structured kernel (nested classes, slot
initializers, `packageUsing:`) is instantiated on Eurasia is an open design
question** for M2.

**Progress (2026-11-17, later): M2 done.** Genesis
(`EURASIA_GENESIS_KERNEL_PLAN_2026-11-17.md`) builds the base image from the
kernel fork, Eurasia creates classes at run time, and psoup's `KernelTests`
and `AccessModifierTesting` (353 tests) give the same outcome on both VMs
(`eurasia/scripts/kernel-tests.sh`; differences would be listed in
`eurasia/docs/EXPECTED_DIFFERENCES.md`, and there are none). `KernelWeakTests`
belongs to M3.

**Progress (2026-11-17, later): M3 under way, its tests passing.**
`eurasia-core/src/gc.rs` collects all garbage at safepoints (between
instructions, and in `vm garbageCollect`), as `gc-semantics.tex`'s
GC-Collect with the whole garbage set: survivors keep their allocation order
and sequence numbers (identity order and identity hash unchanged, no identity
reused), WeakArray elements are cleared, and ephemerons follow the weak-map
fixed point, a dead ephemeron's key, value and finalizer becoming nil as in
psoup (finalizers are not run). A collection is due after as many
allocations as there are live objects (at least 2^20). A snapshot is a
collection into a copy with only the roles as roots. `KernelWeakTests` joins
the differential tests: all 377 tests agree with psoup, and a negative
control (collection disabled) turns 13 of them red. The stress test runs the
base image with a collection after every allocation (`genesis.sh`) and the
suites with one every 64 allocations (`GC_STRESS=64 scripts/kernel-tests.sh`,
about a minute), with the same outcomes; after every allocation the suites
would take far too long, since every collection is a full one. When collection
happens is deterministic for a given execution (it depends only on the
allocation count). **Decided 2026-11-17: replay logs weak-array clearing.**
That alone does not make collection timing unobservable: the population
queries (`allInstancesOf:`, `mixinApplicationsOf:`) also see it
(`eq:gc-all-instances-effect`). Proposed, for when the queries arrive (M6):
each query first runs a full collection, so it reports exactly the live
instances, in allocation order, whatever collections came before; timing is
then observable only through weak containers, which replay logs. Until that
is settled, scheduling stays deterministic. A generational
or incremental collector is an M8 question.

**Progress (2026-11-17, later): M4 in part.** Images now run as psoup's do:
genesis builds the platform (`EurasiaRuntime.ns`: psoup's public kernel,
collections and actors modules over the kernel fork) and the actors module's
message loop, which becomes the MessageLoop role; the VM delivers the
arguments as the startup message, every turn ends with `finish:` naming the
next timer, and the VM waits for it. Eventual sends compile to V5's
instruction 239 (`messageLoop eventualSendTo:selector:arguments:`); a bug in
the shared bytecode pipeline (`ClosureRewriter2>>messageNode:` in
`primordialsoup/newspeak/NewspeakBytecodeCompilation.ns` dropped the
eventual flag, harmless for V4, which lowers eventual sends earlier) had made
every V5 eventual send an ordinary one. psoup's actors module is packaged
unchanged: the packager strips its primitive pragmas and the natives table
installs `classOf:`, `currentMonotonicNanos`, `finish:` and `exit:` on its
methods by class name. Unlike the kernel's helpers, which go through the VM
mirror, that gives two non-kernel classes natives by name; the packager is
trusted, but this should become a capability passed to the module. An
unhandled exception goes to the message loop (the application's handler of
last resort, or a trace and exit), as in psoup; pausing the actor comes with
the debugger (M6). `ActorsTesting` joins the differential tests: all 445
tests agree, also under GC stress. Still to do for M4: ports, `spawn:` from a
mixin with a heap per actor, and far references between VMs.

**Progress (2026-11-18): M4 actors done; ports remain.** Following
`EURASIA_ACTORS_DESIGN_2026-11-17.md`:
- **VM actors.** Every actor, from `Actor named:` or `vm spawn: mixin`, is a
  VM actor in one arena, with its own heap, mailbox and clone of the
  platform template. The VM schedules them round robin.
- **Crossing actors.** References cross only through the VM: far
  references (Φ), and promise records (Π) with Route-Pending queues.
- **The library.** psoup's actors module is forked
  (`eurasia/kernel/fork-actors.py`).
- **Tests.** 444 of 445 differential tests agree; `testPipelining` is an
  expected difference. The base image checks `spawn:`, isolation, far
  references coming home, and an actor's state surviving collection, also
  with a collection after every allocation.

Still open:
- ports and the serializer: decided 2026-11-18 to be one VM-level serializer in the snapshot format, versioned, with deployment as a snapshot rooted at the app (`EURASIA_ACTORS_DESIGN_2026-11-17.md` section 10); built when a cohort-to-cohort user needs it, after the web host;
- pausing an actor (M6);
- snapshots of more than one actor;
- per-actor state in the shared kernel (for instance the symbol table).

**Progress (2026-11-18): M6 met its done-criterion.**
- **The mirror suites agree with psoup.** `MirrorTesting`,
  `MirrorBuilderTesting` and `ActivationMirrorTesting` run in the
  differential kernel tests, and every test agrees, also under GC stress.
  `AtomicInstallTesting` is configured for Squeak and runs on neither VM;
  psoup's installer is covered by `MirrorBuilderTesting`.
- **The IDE boots in the browser.** Browsing, evaluation and the debugger
  were checked by hand.
- **The work, in six steps** (`EURASIA_M6_REFLECTION_DESIGN_2026-11-18.md`
  section 8):
  1. program objects built in Newspeak, and the compiler on Eurasia;
  2. the mirrors fork;
  3. `vm commit:`;
  4. activations and upstream's V5 Simulator;
  5. broken threads outliving their turn (psoup's model; pausing waits for a
     debugger in another actor);
  6. the IDE.
- **Not done:** saving and deployment from the IDE (the serializer is a
  stand-in), `vm pause:` and stack replacement across actors, and the rest
  of the operation list's activation and object operations.

**Progress (2026-11-18): M5 done.** The web host's steps:
1. The wasm32 VM runs an image under a JavaScript host: load, turns, timers
   through the host's event loop, output. **Done.**
2. The call-based JS FFI (`Alien` natives and marshalling, operation list
   section 10). **Done:** psoup's `JSTesting` passes on wasm (under Node
   and in a browser), except one test of psoup's internal error text
   (`eurasia/docs/EXPECTED_DIFFERENCES.md`).
3. Expats and callbacks, with synchronous re-entry. **Done:** the rules of
   the contract design's section 4 (boundary, exceptions, non-local
   return, nesting, sub-steps, idle callbacks), checked by
   `EurasiaHostTesting.ns` on wasm, under Node and in a browser.
4. CounterApp. **Done:** it runs in a browser. Increment, decrement and
   reset work, with no console errors. psoup's Hopscotch, graphics, fonts,
   text, ducts, voice-controller and AI-access modules are packaged
   unchanged:
   - `EurasiaWebRuntime.ns` builds their platform over Eurasia's;
   - `EurasiaCounterApp.ns` is the genesis entry;
   - the genesis packager now compiles lazy slots.

   `eurasia/scripts/web-tests.sh` builds the image. Checking it needs a
   browser, because Hopscotch needs a DOM.

Not done in M5: the vendor libraries psoup's page loads for larger apps
(CodeMirror, JSZip, isomorphic-git) are not on Eurasia's page yet;
`vm expat:`, `expat release` and reclaiming host handles are open, as are
ports and the serializer.

Step 1 details:
- `eurasia-web` exports a non-blocking run (`eurasia_start`,
  `eurasia_resume`). The VM answers `Completion::Waiting` when nothing can
  run before the next timer and the host cannot block (`Host::blocks`).
- `eurasia/web/eurasia.mjs` is the loader, for browsers and Node.
- `eurasia/scripts/web-tests.sh` checks that the base image prints exactly
  what it prints natively, and that all 445 kernel tests have the same
  outcomes (they wait for timers about 30 times).
- In a browser, both images give the same results.

**Decided 2026-11-17: genesis, then full snapshots.** psoup runs the program
when it builds an image because it is *deploying an application*: it
establishes dependencies by sending the imports to a manifest. Eurasia's
images are full heap snapshots, code and state. Only the first image is
built specially:
1. A **genesis packager** (EurasiaPackager grown up) builds, statically, the
   classes and objects needed before any code runs: the kernel classes, the
   failure class, the VM mirror, roles and natives.
2. At first boot Eurasia runs a **genesis entry** in Newspeak that does the
   rest of the kernel's initialization, then **saves the whole heap**. That
   snapshot is the base image every later run starts from.
3. After that, apps are deployed on Eurasia itself with the manifest
   technique psoup uses, once the compiler runs on Eurasia (M6). Until then
   apps are packaged from psoup, as in M1b.

Consequence: saving an idle heap (no paused stacks) moves from M7 to M2/M3.
Paused stacks, restore with aliens, and replay stay in M7.

**Principle (decided 2026-11-17): images are build artifacts, always
recreatable from source.** Eurasia must never reach the Smalltalk situation
where an image lives on for years because rebuilding it from source is too
hard.
1. *Every base image is genesis output only.* Anything it contains is produced
   from source: by the genesis packager (its own source and
   `eurasia/kernel/natives.tsv`) or by the genesis entry, which is Newspeak.
   No state set up by hand in an image and saved.
2. *Builds are reproducible.* Allocation order, identity hashes and the
   snapshot format are deterministic, so building twice gives byte-identical
   images; `eurasia/scripts/genesis.sh` checks this on every run (verified
   2026-11-17 for both the genesis and the base image). A snapshot saves
   only what the roles reach (M3), so the image does not depend on the
   arguments genesis ran with; the check builds the second image to a
   different path.
3. *Self-hosting uses a seed, not a lineage.* Once Eurasia compiles itself
   (M6), the packager runs in a pinned stage-0 image that is used only to run
   the compiler: the build compiles everything from source with it (stage 1),
   rebuilds with stage 1 (stage 2), and requires stage 1 and stage 2 to be
   byte-identical. The seed can always be rebuilt from source, so it is never
   precious.
4. *Genesis runs routinely,* as part of the regular checks, so building from
   source cannot rot unnoticed.

## 7. Risks

- **Kernel fork drift.** Two kernels evolve in parallel until psoup retires.
  Mitigation: the fork is mechanical at first (pragmas out, table in), and the
  differential tests catch divergence.
- **Hidden psoup behaviour** the image relies on (callback argument order,
  draining the queue in callbacks, explicit `class` sends). The decided
  semantic changes are deliberate; the rest surface as differential
  failures.
- **Performance** with index-based references and a Rust-managed stack.
  Measured at M2 on simple benchmarks, before the design is set in stone.
- **Upstream V5 bugs** carried into the compiler or the Simulator; the
  refinements in 2.4 fix the known ones.

## 8. What this plan does not do yet

A JIT, a native C FFI beyond file I/O, Croquet integration, and VM identity
and succession (still open in the design doc).

## 9. Decisions (2026-11-17)

1. **Name: Eurasia.** The code lives in a new repository,
   `dev/web/eurasia`; the packager and the kernel fork live in this
   repository, beside the V5 compiler. Crate names below use the `eurasia-`
   prefix in place of `nsvm-`.
2. **Toolchain:** update Rust to the latest stable and add the wasm32 target.
3. **64-bit words on every target**, wasm32 included.

The original questions, for the record:


1. **Where the code lives.** Recommendation: a new repository beside the
   others, `dev/web/nsvm` (name open), with the packager and the kernel fork
   in this repository, where the V5 compiler already is.
2. **Toolchain update.** The installed Rust is 1.67 (January 2023) and has no
   wasm32 target. M0 needs `rustup update` and
   `rustup target add wasm32-unknown-unknown`, which change the user-wide
   toolchain in `~/.rustup`.
3. **64-bit words on wasm32** (section 2.2). Recommended for determinism; it
   costs memory on the web.
4. **Name** of the VM and its repository.
