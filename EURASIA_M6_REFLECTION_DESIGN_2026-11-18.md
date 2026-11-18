# Eurasia M6: reflection, the debugger and the IDE

**Date:** 2026-11-18
**Status:** Decided 2026-11-18 (section 7). Implementation under way.
**Context:** `NEW_VM_IMPLEMENTATION_PLAN_2026-11-17.md` (M6),
`VM_KERNEL_OPERATIONS_2026-11-10.md` sections 4–7,
`VM_KERNEL_CONTRACT_DESIGN_2026-11-09.md`,
`formal-semantics/reflection-semantics.tex`.

## 1. What M6 must deliver

The plan: "`commit:` with layout maps, activation operations, pause and
stack replacement; the Simulator over natives". Done when the mirror and
atomic-install test suites pass and the IDE boots.

The suites, all psoup's or the IDE's and all run on psoup today:

| Suite | Lines | Exercises |
|---|---|---|
| `MirrorTesting` | 772 | Reading the program: class, mixin, method and object mirrors |
| `MirrorBuilderTesting` | 911 | Building and installing classes from source |
| `AtomicInstallTesting` | 750 | Installing changes atomically, with instance migration |
| `ActivationMirrorTesting` | 1723 | Activations, stepping, the debugger |

As in M2–M4, they run differentially: on psoup through a reference runner,
and on Eurasia from a genesis image, every difference explained.

## 2. Where Eurasia stands

- **Reading program objects already works.** Methods, mixins and classes
  are VM object kinds with contract fields. The kernel's accessors on them
  (`_methods`, `_enclosingMixin` and so on) answer those fields, and
  `vm slotOf:at:` reads them in format order.
- **Building them does not.** `InstanceMixin new` or `Method new` answers
  an ordinary object, which `vm applyMixin:superclass:enclosingObject:`
  refuses, since it needs a real mixin. Today every program object is made
  by the genesis packager on psoup.
- **Some activation operations exist** (natives 100–110): the current
  activation, sender and `sender:`, method, receiver, closure, temps,
  size, pc, and a closure's defining activation. Missing are
  `continueAt:with:`, closure construction, `newActivationFor:…`, pc and
  depth writes, and `markUncontinuable:`.
- **None of the rest exists:** `commit:`, `allInstancesOf:`,
  `mixinApplicationsOf:`, `reclassify:as:`, `programVersion`, natives as
  objects, pause, stack images and stack replacement.
- **The compiler does not run on Eurasia.** The V5 compiler
  (`Newspeak2V5BytecodeCompilation`) runs on psoup inside the packager.

## 3. What psoup's mirrors need

All of psoup's reflection primitives are in one module,
`MirrorsForPrimordialSoup.ns` (3,289 lines). `ActivationMirrors.ns`,
`AtomicInstaller.ns` and `Debugging.ns` in the newspeak checkout use
none. The primitives:

| psoup | Use | Eurasia |
|---|---|---|
| 34 `basicNew`, 35/36 `slotOf:at:(put:)`, 85 `classOf:`, 86 identity, 87 hash, 126 `isCanonical:` | Objects | Have them (natives 111–118). |
| 96 `allInstances` | Populations | `vm allInstancesOf:` (operation list section 4). |
| 98 `elementsForwardIdentity` (become) | Installing | `vm commit:` (section 6). |
| 133 `currentActivation`, 71, 73, 70, 77, 78 | Activations and closures | Have 100–110; add `initialPcOf:`, `copiedOf:`, `copiedOf:at:put:`. |
| 69 `Closure class new` | The Simulator makes closures | `vm closureIn:pc:numArgs:copied:`. |
| 95 `Activation jump` | Continuing at an activation | `vm continueAt:with:`. |
| 141 `doPrimitiveWithArgs`, 142 `simulationRoot` | The Simulator running a native, and its root frame | `vm runNative: method receiver: r arguments: a` (the "Simulator over natives") and the simulation-root role (27, which the VM already honours for non-local return). |

psoup's Simulator (inside `MirrorsForPrimordialSoup`) interprets **V4**
bytecode. Eurasia runs **V5**. The newspeak checkout already has a V5
decoder (`V5BytecodeSimulation.ns`, written for the JS platform's
debugger), whose Simulator subclass is not written yet.

## 4. Proposal

### 4.1 Program objects built in Newspeak

`Method new`, `InstanceMixin new` and `ClassMixin new` answer real program
objects of the VM's kinds, with every contract field nil. Their setters
write the contract fields, with the kind checks the VM needs (a method's
bytecode must be a ByteArray and decode, its header a SmallInteger, and
so on). Objects stay mutable until installed, and installing freezes them.
`vm applyMixin:` accepts an unfrozen mixin, as builders apply mixins before
installing.

This keeps psoup's builder code unchanged: it already makes these objects
with `new` and sets their fields. The packager's mapping from psoup's
method layout (header word, literals, bytecode) to Eurasia's becomes a
kernel concern instead.

### 4.2 The mirrors module: a fork

`kernel/fork-mirrors.py` derives `EurasiaMirrors.ns` from
`MirrorsForPrimordialSoup.ns`, as the kernel and actors forks do, with
every edit checked:
- the primitives become VM-mirror operations;
- installing builds a change set for `vm commit:` instead of a become;
- the V4 Simulator is replaced by a V5 one: `V5BytecodeSimulation`'s
  decoder plus a Simulator subclass, running natives with
  `vm runNative:receiver:arguments:`.

The ten-odd places that know psoup's object layout become contract-field
accesses.

### 4.3 `vm commit:`

As the operation list specifies:
- forwarding pairs, each old program object taking the new one's identity;
- layout maps, which the VM applies to every instance in every actor's
  heap (new slots nil);
- object commands (`changeObjectClass`, `writeObjectSlot`).

All or nothing. It also bumps the program version and drops the lookup
caches.

**Forwarding** is a heap-wide rewrite of references, one pass over the
arena like the collector's compaction. The arena makes that cheap and
needs no object table. psoup's general become is not offered: only
commit's forwarding of program objects, plus the instance replacement
that layout maps do. psoup's library migrates instances itself by becoming
them. The operation list moves that into the VM, because one actor cannot
reach another's instances.

### 4.4 Activations, pausing and stack replacement

- The missing operations of section 5 of the operation list are added.
- `vm pause:` keeps a turn's frames on its actor, which then runs nothing
  until it is resumed or its stack is replaced.
- An **unhandled exception pauses its actor** (decided 2026-11-10), instead
  of printing a trace and going on. That changes what the base image and
  the test runners see, so their handlers of last resort (which stay) are
  what tests rely on.
- Stack images: an immutable copy of a paused actor's frames, for the
  debugger. Replacing a stack installs frames built from one.

### 4.5 The compiler on Eurasia, and the IDE

- **The compiler.** With 4.1 the V5 compiler runs on Eurasia unchanged,
  producing Eurasia methods directly. A first check compiles a class from
  source at run time and runs it.
- **The IDE.** It is packaged like CounterApp: psoup's modules unchanged
  over a web runtime with mirrors, the compiler and the debugger. Its page
  also loads psoup's vendor libraries (CodeMirror, JSZip, isomorphic-git).
  "Boots" means the IDE opens, browses classes and evaluates an
  expression; saving and the debugger are checked by hand as far as they
  go.

## 5. Questions

1. **Program objects (4.1):** `new` answers real, mutable program objects
   until installation freezes them. The alternative: builders make ordinary
   objects, which `commit:` converts. That keeps the VM's kinds immutable,
   but `applyMixin:` before installing, which psoup's builders rely on,
   would then need a conversion too. **Recommended: real objects.**
2. **A forked mirrors module (4.2)**, rather than a new Eurasia-only one.
   **Recommended: the fork,** for psoup parity, as with the kernel and
   actors.
3. **No general become (4.3):** only `commit:`'s forwarding. Anything else
   in the IDE that becomes objects would have to be rewritten. I have not
   yet found any other use.
4. **A Newspeak V5 Simulator (4.2),** extending `V5BytecodeSimulation`, as
   the plan's "Simulator over natives" says. The alternative is a VM
   single-step operation: simpler, but the semantics' debugger is the
   Simulator.
5. **Unhandled exceptions pause the actor (4.4),** as decided on
   2026-11-10. Taking that up in M6 means the base image's trace-and-exit
   becomes pause-and-report. Confirm that is wanted now, rather than with
   the debugger UI.

## 6. Order of work

1. Program objects built in Newspeak (4.1); the V5 compiler compiling and
   running a class on Eurasia.
2. The mirrors fork, reading side: `MirrorTesting` agrees with psoup.
3. `vm commit:` with forwarding and layout maps:
   `MirrorBuilderTesting` and `AtomicInstallTesting` agree.
4. The activation operations and the V5 Simulator:
   `ActivationMirrorTesting` agrees.
5. Pause, stack images and stack replacement.
6. The IDE boots in the browser.

## 7. Decisions (2026-11-18)

1. **All five recommendations of section 5 are accepted:**
   - real program objects from `new`, mutable until installed;
   - a forked mirrors module;
   - no general become;
   - a Newspeak V5 Simulator;
   - unhandled exceptions pause the actor.
2. **The V5 Simulator comes from upstream.** rmacnak/primordialsoup's
   `newspeak/Mirrors.ns` (head `e7a7ece`, 2026-09-26) is psoup's mirrors
   module for V5. It has the V5 `InstructionStream`, `Printer` and
   `Simulator` (with `doPrimitive:`), and the `Thread` machinery the
   debugger runs on. Its `Simulator` is unchanged since the extract the
   newspeak checkout holds (`upstream-V5Simulator-338f0bb3.ns.txt`, which
   is current: no commit to `Mirrors.ns` follows 338f0bb3).
   - **The fork's base stays `MirrorsForPrimordialSoup.ns`,** whose API the
     IDE and the test suites use. The fork replaces its V4 Simulator with
     upstream's V5 one, adapted to Eurasia's operations.
   - **Upstream's decoder bug is fixed in the fork.** Upstream still decodes
     bytes 48–63 as `popJumpTrue:` instead of the short `popJumpFalse:`;
     `V5BytecodeSimulation.ns` already fixes it.
   - **Licensing.** Upstream's Newspeak sources are under the Apache
     License 2.0 (Copyright 2008, the Newspeak project authors), as psoup's
     are. Eurasia's LICENSE acknowledges the fork as it does the kernel and
     actors forks.

## 8. Progress

**Step 1 (2026-11-18): program objects built in Newspeak; the compiler
runs on Eurasia.**
- **Real program objects.** `Method new`, `InstanceMixin new` and
  `ClassMixin new` answer the VM's kinds, with every field nil. Roles 38
  and 39 name the mixin classes. Setters write the contract fields of an
  unfrozen one, and a mixin's slot count follows its slot names.
- **Headers and bytecode.** `Method>>header`, `header:`, `bytecode` and
  `bytecode:` are natives 149–152. `header:` reads psoup's header word:
  primitive 256 + i is a getter of the mixin's own slot i, 512 + i its
  setter, 1023 answers the receiver, any other nonzero one a Eurasia
  native. So psoup's compiler and its `Method newGetterForSlot:…` helpers
  work unchanged, given mixin-relative indices.
- **One packager change.** A module whose header names another module as
  its superclass is built on the root, as psoup's runtimes build it; its
  user applies the real superclass with `mixinApply:`.
- **Checked by `eurasia/scripts/reflection-tests.sh`.** On Eurasia,
  `EurasiaCompilerProbe.ns` compiles a class from source with psoup's
  compiler (`Newspeak2V5BytecodeCompilation` over `NewspeakCompilation`).
  It builds the mixins as the packager does, applies them and runs the
  class: slots, accessors, the factory and the class side. It also runs
  under GC stress.

**Step 2 (2026-11-18): the mirrors fork; `MirrorTesting` agrees except
`evaluate:`.**
- **The fork.** `eurasia/kernel/fork-mirrors.py` derives `EurasiaMirrors.ns`
  from `MirrorsForPrimordialSoup.ns` with few edits:
  - the module's name;
  - a class's mixin and superclass are contract fields 1 and 2;
  - its methods are its mixin's;
  - an instance's size is the slots its mixins declare;
  - the compiler is the V5 one.

  The primitive methods map to natives by the natives table: the existing
  object operations, plus new natives 153–157 (`allInstancesOf:`, which
  collects first, and four closure accessors).
- **Most of the parity comes from the kernel.** Its mixins answer psoup's
  mixin fields from the library field:
  - `_headerSource`, `_accessModifier`, `_nestedMixins` and
    `_primaryFactorySelector`, with their setters;
  - a class-side mixin's `_instanceMixin`.

  `_slots` holds psoup's `{name. isMutable. accessModifier}` triples, which
  the VM only counts.
- **The packager now keeps what the mirrors read:**
  - method sources;
  - psoup's `MethodMetadata` for lazy-slot methods;
  - header sources;
  - slot triples;
  - psoup's class-side mixin names (`'X class'`).

  Images grow with the sources (the base image from 104 KB to 271 KB).
- **`EurasiaReflectiveRuntime.ns`** adds `mirrors` to the base platform,
  over a namespace of the compiler's modules.
- **The result.** `MirrorTesting` joins the differential kernel tests. 48 of
  its 51 tests agree with psoup, also under GC stress. The three
  `evaluate:` tests wait for step 4's Simulator and are listed in
  `eurasia/docs/EXPECTED_DIFFERENCES.md`.

**Step 3 (2026-11-18): `vm commit:`; `MirrorBuilderTesting` agrees except
`evaluate:`.**
- **`vm commit: {old objects. new objects. layout maps}`** (native 158)
  installs atomically, all or nothing:
  - Each layout map `{old class. new class. for each new slot, the old
    slot's index or 0}` reshapes every instance of the old class in place,
    so its identity, flags and actor stay.
  - Each old object's references then go to the new one, in one pass over
    the arena and the VM's roots. Running frames keep their methods.
  - The new methods, mixins and classes are frozen.
  - The program version goes up (`vm programVersion`, 161).
  - There is no general become.
- **Class queries.** `vm mixinApplicationsOf:` and `vm subclassesOf:`
  (159–160) replace psoup's weak sets. Like `allInstancesOf:`, they collect
  first. Without that, the installer re-applied classes that forwarding had
  just made garbage.
- **Root classes.** `applyMixin:` takes a nil superclass, for root classes.
- **The installer, in the fork.** It builds layout maps instead of copying
  instances, and installs with one `commit:`. It synthesizes slot accessors
  per mixin, with mixin-relative indices.
- **The result.** psoup's `MirrorBuilderTesting` joins the differential
  tests. 51 of its 54 tests agree, also under GC stress; the three
  `evaluate:` ones wait for step 4.
- **`AtomicInstallTesting` is not a target after all.** It is configured
  for Squeak (`MirrorsForSqueak`, `platform squeak`), so it runs on neither
  psoup nor Eurasia; `MirrorBuilderTesting` covers psoup's installer.

**Step 4 (2026-11-18): activations and the V5 Simulator; all three mirror
suites agree with psoup.**
- **Detached activations.** `Activation new` makes an activation that holds
  its own state (sender, bci, temps), as psoup's heap activations do. psoup's
  setters (`method:`, `closure:`, `receiver:`, `bci:`, `size:`, `sender:`)
  work on it (natives 162–167), and the existing activation natives read it.
- **Three VM operations for threads:**
  - `vm resumeActivation: top` (171) turns a detached chain, whose bottom's
    sender is the current frame, into frames, and continues at its top.
  - `vm continueAt: a with: v` (170) jumps to a live activation, whose
    pending send answers `v`.
  - The frames `continueAt:` cuts off are **detached**, not killed, as
    psoup's heap activations survive a jump: a broken thread's stack stays
    inspectable and resumable.
- **For the Simulator:**
  - `vm runNative:receiver:arguments:` (172) runs a native or accessor
    method without a frame. It answers the result, the failure to signal,
    or the send or closure activation the native asks for.
  - `newClosureIn:initialBCI:numArgs:numCopied:` (173) makes a closure.
- **Simulation roots** (psoup's primitive 142) are methods carrying a flag
  bit (bit 4, snapshot format 5), set and tested by `vm markSimulationRoot:`
  and `vm isSimulationRoot:` (168–169). The VM's non-local return stops at
  them, and the kernel routes a simulated thread's exceptions to them.
- **Return-self is primitive 1023** in psoup's header word, and setters
  512–1022, inside psoup's `Method>>primitive` mask, so the Simulator never
  mistakes a return-self method for bytecode.
- **The fork's V5 Simulator.** Its decoder is `V5BytecodeSimulation`'s. The
  Simulator is upstream's, with `tryPrimitive:` taking the method, so that:
  - the current activation, the closure `value…` natives, perform and the
    two jumps are simulated;
  - anything else runs through `runNative`.

  The V4 selector scan and instruction sizes are replaced by V5 ones.
- **The result.** psoup's `ActivationMirrorTesting` joins the differential
  tests, and all 73 tests agree. Four fail on both VMs: they expect `[^2]`,
  but the pretty-printed test file has `[ ^2 ]`. With it, every test of the
  three mirror suites agrees with psoup, including the `evaluate:` tests.
- **Two bugs found by the suite:**
  - The Simulator hung re-signalling its own jump to the simulation root,
    until the jumps were simulated.
  - `runNative` stored only into ordinary objects, until the interpreter's
    slot store was factored out for both.
