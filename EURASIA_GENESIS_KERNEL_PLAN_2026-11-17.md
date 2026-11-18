# Eurasia genesis kernel: plan

**Date:** 2026-11-17
**Status:** Plan for review; the VM-side activation operations (step 2) are
being implemented, since every option below needs them.
**Context:** `NEW_VM_IMPLEMENTATION_PLAN_2026-11-17.md`, "Decided: genesis,
then full snapshots". A genesis packager builds the minimum statically; a
genesis entry finishes initialization in Newspeak on Eurasia and saves the
base image.

## 1. What psoup's kernel needs from the VM

`KernelForPrimordialSoup.ns` is one module with 39 nested classes and three
module slots (`messageLoop`, `symbolTable`, `symbolTableUsed`). 130 of its
methods have primitive pragmas:

| Group | Methods | Eurasia |
|---|---|---|
| Numbers, strings, arrays, closures, `_Object` (`==`, `class`, `hash`), `Class>>basicNew` | 98 | Value natives, done (`natives.rs`). |
| Module-level private helpers: `slotOf:at:`, `slotOf:at:put:`, `classOf:`, `is:identicalTo:`, `identityHashOf:`, `instantiate:`, `isCanonical:`, `setCanonical:`, `object:perform:with:`, `currentActivation`, `definingActivationOf:`, `currentMonotonicNanos`, `garbageCollect`, `print:` | 14 | Natives installed on the **kernel module's own private methods**. The internal kernel is the trusted base; this is the kernel holding the VM-mirror capability, as in psoup. |
| `Activation`: `sender`, `sender:`, `method`, `method:`, `closure`, `closure:`, `receiver`, `receiver:`, `bci`, `bci:`, `tempAt:`, `tempAt:put:`, `size`, `size:` | 15 | Activation natives over live frames (section 2). |
| `Exception>>jumpTo:`, `Exception>>finish:` | 2 | `jumpTo:` serves the Simulator only; `finish:` ends a turn (actors, M4). |

Beyond primitives, the kernel depends on psoup in four ways:

1. **Primitive numbers as markers.** `invokeNextHandler` recognizes `on:do:`
   frames by `method primitive = 116`, `isUnwindContext` uses 113, the
   simulation root 142, the dispatch boundary 168. The fork compares method
   identity instead (`activation method == onDoMethod`); the genesis packager
   fills kernel module slots with those method objects (it knows them; they
   are also roles).
2. **psoup layouts.** `superclassOf:`, `mixinOf:`, `nameOf:`, `methodsOf:` …
   read class objects with `slotOf:at:` at psoup's indices. In Eurasia the
   contract layouts differ (snapshot format section 5), so these accessors
   change in the fork; `slotOf:at:` on a contract object reads its contract
   fields in format order.
3. **The object store.** psoup's `buildObjectStoreWithApplication:` answers
   the VM's object store. In Eurasia that is the role table: the genesis
   entry assigns any role that only exists after initialization with
   `vm setRole:to:`; the packager assigns the rest.
4. **`_Object`'s superclass "fixed to nil by magic".** The genesis packager
   gives `_Object` no superclass; nested classes with no superclass clause
   default to `_Object`.

## 2. Activations over live frames

psoup's exceptions walk `sender` links, read and write handler temps, and
return to an earlier frame by **rewriting the current frame's sender**
(`terminateTo:`) and then returning. Eurasia keeps frames on a Rust stack, so
these become natives over activation handles:

- `sender`: the handle of the frame below, or nil at the bottom; a dead
  activation's sender is nil.
- `method`, `receiver`, `closure`: from the handle.
- `tempAt: i` / `tempAt: i put: v`: one-based over arguments, then copied
  values and locals, then the frame's operand stack, as in psoup; `size` is
  that count. Index checks fail with `outOfRange`.
- `sender: a`: **restricted** to making a live frame's sender a live frame
  further down the same stack. The frames in between are retired (their
  handles die) and their stack contents removed, so a later return from the
  frame lands in `a`. This is exactly what `terminateTo:` needs. Any other
  use (a dead target, a frame above, another stack) fails with `wrongKind`.
- `bci:`, `method:`, `closure:`, `receiver:`, `size:` on a live frame are not
  needed by the exception code and are deferred to M6 (debugger), where the
  formal semantics' stack replacement is the model.

## 3. The fork

`EurasiaKernel.ns` in the newspeak repository starts as a copy of
`KernelForPrimordialSoup.ns`, then:

1. primitive pragmas removed (the V5 compiler rejects them; natives are the
   packager's table, never source);
2. marker tests replaced by identity with module slots `onDoMethod`,
   `ensureMethod`, `simulationRootMethod`, `dispatchMethod`;
3. layout accessors rewritten for Eurasia's contract layouts;
4. `Activation>>terminateTo:` becomes `sender:: previousContext`: the VM
   retires the frames in between (psoup's version zaps each one itself with
   `sender: nil`, `bci: nil`, `size: 0`, which Eurasia does not offer);
5. `messageLoop unhandledException:from:` replaced, until actors (M4), by a
   kernel method that prints the exception and exits through a module slot
   `vm` holding the VM mirror (filled by the genesis entry);
6. a genesis entry, `main: vm args: args` on the module: store `vm`, build
   what genesis needs, set the entry role to the application, and save the
   base image to `args at: 1`.

## 4. The genesis packager

`EurasiaPackager` generalized:

- natives as data: a table file `(class, selector, native)` in the eurasia
  repository, checked against `natives::catalog()` by a Rust test, so the
  packager and the VM cannot disagree;
- the kernel module's own methods may be natives (section 1);
- module slots filled at packaging time: the cached nested-class slots (as in
  M1b), the marker methods, and `symbolTable` (a WeakArray of the image's
  canonical strings);
- roles from kernel class names (`_Array` is Array, and so on), the common
  selectors from the compiler (checked, as in M1b), and `Entry` = the kernel
  module instance, whose `main:args:` is the genesis entry.

## 5. Order of work

1. Activation natives over live frames, with tests built in Rust,
   including `terminateTo:`-style returns and `ensure:` unwinding written in
   bytecode against them (VM only).
2. The natives table as data, and the module-level natives.
3. The fork, steps 1–4, and the packager changes.
4. The genesis entry and the base image; a kernel smoke test (arithmetic,
   collections, strings, `printString`, an exception caught by `on:do:`, an
   `ensure:` block run on a non-local return).
5. Differential tests against psoup: the kernel test suites, with
   `eurasia/docs/EXPECTED_DIFFERENCES.md` explaining every difference.

## 6. Decisions (2026-11-17)

1. **The kernel's privileged helpers go through the VM mirror**, not natives
   on the kernel module's private methods. One path for all authority (every
   privileged operation is a send to `vm`), attenuable later. The genesis
   packager fills the kernel module's `vm` slot with the VM mirror. Cost: one
   extra send on those helpers; it matters only for identity-keyed
   collections, and the guarded fast paths (design doc 8.4) can remove it.
   Section 1's "natives installed on the kernel module's own private methods"
   is superseded: those methods become ordinary methods sending to `vm`.
2. **Until actors (M4), an unhandled exception prints and exits**, with a
   stack trace (each frame's receiver class and selector, by walking `sender`
   links) where feasible.
