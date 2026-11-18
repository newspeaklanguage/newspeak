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
  the logging decision is still open).

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
| M7 | Snapshots, restore, replay log, checkpoints, divergence detection | Save and restore with paused stacks; replay of a recorded IDE session reproduces its outputs. |
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
