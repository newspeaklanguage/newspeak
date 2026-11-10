# psoup primitives classified for the VM kernel

**Date:** 2026-11-09
**Status:** Draft. Input to section 3 of `VM_KERNEL_CONTRACT_DESIGN_2026-11-09.md`.
**Source:** the primitive table in `primordialsoup/vm/primitives.cc` (branch
`extraRevs` @ `86f0ec9`): 161 entries, numbers 1–169 plus 200. Call sites are
the `:literalmessage: primitive: N` pragmas in `primordialsoup/newspeak/*.ns`.
"Unused" means no pragma names the number; it does not rule out use by
number elsewhere (for example the Simulator's `doPrimitive:` escape).

## Legend

**Category** (design doc section 3): *pure*, *heap*, *control*, *reflective*,
*turn*, *input*, *resource*, plus **output**, a category this pass shows the
design doc needs. Output covers effects that only send data out (printing,
writing files, sending to a port). Replay need not record outputs, but it must
divert or suppress them.

**Disposition** in the new VM:

- **N — native method.** Installed on a kernel class at bootstrap by the VM
  mirror holder (design doc section 8). On a hot path, so its cost matters.
- **K — kernel operation.** A message to the VM mirror, or to a capability
  attenuated from it. Not on a hot path.
- **R — role.** Today a "marker" primitive that always fails and only lets
  the VM or the library recognise a method by its number. In the new VM the
  mirror holder tells the VM which method object plays the role (ensure,
  on:do:, simulation root, dispatch boundary); nothing is keyed by number.
- **L — library.** Can be written in Newspeak on top of other operations.
  Keep it native only if measurement says so.
- **H — host interface.** Becomes ordinary calls through the FFI (the JS
  bridge on WASM, a C FFI natively), made from Newspeak libraries. Not kernel
  operations. The kernel provides only the FFI itself (design doc 4.5).
- **D — drop.** Unused by the current sources, or obsolete in the new VM.

## Table

| Nos. | Primitives | Used by | Category | Disp. | Notes |
|---|---|---|---|---|---|
| 1–3 | add, subtract, multiply | `Integer`, `Float`, `Number` `+ - *` | pure | N | The hottest operations in the system. psoup has no inline SmallInteger fast path: every `+` is a full send. Candidate for a guarded inline fast path (design doc 8.4). |
| 4–8 | divide, div, mod, quo, rem | `Number`, `Integer` | pure | N | Division by zero must raise a named exception rather than fall back. |
| 9–13 | `= < > <= >=` | `Number` | pure | N | Same fast-path candidate as 1–3. |
| 14, 15 | asInteger, asDouble | `Number` | pure | N | |
| 16–20 | bitAnd, bitOr, bitXor, shift left, shift right | `Integer` | pure | N | |
| 21, 22, 125 | floor, ceiling, rounded | `Float` | pure | N | |
| 23–25, 30–33, 131 | sin, cos, tan, exp, ln, log, sqrt, pow | `Float` | pure | N | Not on hot paths, but cheap as natives and awkward in Newspeak. |
| 26–29 | asin, acos, atan, atan2 | unused | pure | D or N | `Float` has no methods for them. Add the methods or drop. |
| 108–111 | float to string (fixed, exponential, precision), number to string | `Float`, `Number` | pure | N | Uses the bundled double-conversion library. |
| 132 | parse float | `Float class` | pure | N | Same library. |
| 34 | basicNew | `Class`, the kernel, PrimordialFuel | heap | N | Allocation. |
| 38–41 | Array new/at/at:put:/size | `_Array` | heap | N | Hot. Bounds failure must raise a named exception. |
| 42–45 | WeakArray new/at/at:put:/size | `WeakArray` | heap | N | Weak semantics come from the GC layer of the formal semantics. |
| 46–49 | ByteArray new/at/at:put:/size | `ByteArray` | heap | N | |
| 51, 53 | String at, size | `String` | heap | N | (52 is unassigned.) |
| 50, 121 | copy a byte range as ByteArray / as String | `ByteArray`, `String` | heap | N | |
| 79–81 | replaceFrom:to:with:startingAt: (bytes, array), Array copyFrom:to: | `ByteArray`, `_Array` | heap | N | 81 could be L (new + replace). |
| 122–124 | ByteArray withAll:, String with:, String withAll: | class side | heap | N | 123 could be L. |
| 54, 114, 115 | String hash, `=`, `,` | `String` | pure | N | |
| 117–120 | startsWith, endsWith, indexOf, lastIndexOf | `ByteArray`, `String` | pure | L→N | Could be Newspeak; keep native if measurement says so. |
| 35, 36 | instVarAt:, instVarAt:put: | kernel, PrimordialFuel, mirrors | reflective | K | Slot access without going through accessors: mirror authority, not a public method. |
| 37 | instVarSize | unused | reflective | D | Mirrors get it from the class layout. |
| 85 | class | `_Object>>class`, mirrors | heap | N | Today `x class` with an explicit receiver raises (see memory); the native serves the implicit form. |
| 86 | `==` | `_Object`, kernel | pure | N | Hottest identity test; also an inline fast-path candidate. |
| 87 | identityHash | `_Object`, kernel | resource | N | Nondeterministic unless defined from allocation order (ledger). |
| 126, 127 | isCanonical, markCanonical | kernel, PrimordialFuel, mirrors | heap | K | Value-object canonicalisation; mirror authority, not public. |
| 55–67, 140 | Activation sender/bci/method/closure/receiver, tempAt:, size and their setters | `Activation` | reflective | K | Activation access. The formal semantics already specifies the reads and the edits (`writeActivationLocal`, `changeActivationContinuation` …). Should require the activation mirror's rights rather than being public `Activation` methods. |
| 68 | Activation new | `Activation class` | reflective | K | Used by the Simulator to build frames. |
| 69 | Closure new | the Simulator | reflective | K | |
| 70, 71, 73, 75, 77, 78 | Closure numCopied, definingActivation, initialBci, numArgs, copiedAt:, copiedAt:put: | mirrors, PrimordialFuel, `Closure>>numArgs` | reflective | K (75: N) | `numArgs` is ordinary public protocol; the rest are mirror operations. |
| 72, 74, 76 | Closure definingActivation:, initialBci:, numArgs: | unused | reflective | D | |
| 89 | perform:withArguments: | kernel | control | N | Reflective send; the Simulator recognises it. |
| 90–94 | Closure value, value:, value:value:, value:value:value:, valueWithArguments: | `Closure` | control | N | Hot. The Simulator must recognise these methods (it reifies the frames). |
| 95 | Activation jump | `Exception>>jumpTo:`, mirrors | control | K | Resuming an activation; the formal semantics' `continueAtActivation`. |
| 113 | ensure: (marker) | `Closure>>ensure:` | control | R | The VM's unwind search recognises the method. |
| 116 | on:do: (marker) | `Closure>>on:do:` | control | R | Recognised by the exception handler search. |
| 133 | currentActivation | kernel, mirrors | control | K | `currentActivationQuery` in the formal semantics. |
| 141 | doPrimitive:withArgs: | the Simulator | control | D | The Simulator's escape to "run primitive N for real". In the new VM the Simulator calls the native method object directly. |
| 142 | simulation root (marker) | mirrors (`Thread`) | control | R | |
| 168 | dispatch boundary (marker) | `MessageLoop` dispatch methods | turn | R | Added 2026-11-09 (H4). |
| 200 | quickReturnSelf | set by `PrimordialSoupTracer` | control | D | An encoding of a trivial method. In the new VM, trivial methods (return self, getters, setters) are a method kind chosen by the compiler, not a primitive. The 256/512 accessor flags in method headers are the same thing. |
| 96 | allInstances | mirrors | reflective | K | Order must be deterministic for replay (ledger). Mixin-applications query needed too (formal semantics). |
| 98 | elementsForwardIdentity (bulk become) | mirrors | reflective | K | The basis of atomic install. Safepoint only. |
| 134 | adoptInstance (reclassification) | PrimordialFuel | reflective | K | `changeObjectClass` in the formal semantics. |
| 104 | flushCache | unused | reflective | D | The new VM invalidates its caches itself on every reflective commit. |
| 105 | collectGarbage | kernel | resource | K | |
| 99 | operatingSystem | `Platform` | input | K | Constant for a run; record it for replay anyway. |
| 100, 101 | monotonic clock, UTC clock | actors (`WhenReactor`), kernel; 101 unused | input | K | Recorded on record, replayed. |
| 102 | print | kernel | output | K | |
| 103 | halt | `_Object>>halt` | control | K | Enters the debugger or stops the VM. |
| 107 | exit | `MessageLoop` | turn | K | |
| 128, 130 | write file, read file | compiler apps | output, input | H | Host I/O for the native VM; read is input, write is output. In the new VM these are FFI calls in a library, not operations. |
| 135–138 | open port, close port, spawn, send | `Port` | turn | K | Actors. Spawn takes a serialised snapshot (`rawSpawn: bytes`), which ties into snapshot semantics (design doc 6). |
| 139 | finish: | `MessageLoop`, `Exception` | turn | K | Ends the turn. |
| 143, 144 | await signal, cancel signal wait | Zircon | input | D | Fuchsia, which is not a target. The one idea worth keeping: the message loop must be able to wait on host events. That is the turn layer's job, not a primitive per OS. |
| 145–153, 165 | Zircon handles, channels, VMOs, status strings | Zircon | input/output | D | Fuchsia, which is not a target. These exist only because psoup has no general FFI, so each system call became a primitive. In the new VM, any such calls are ordinary FFI calls. |
| 154–158, 160–164, 166, 167, 169 | JS bridge: push value/alien/expat, pop, peek alien, perform get/set/delete/call/new/instanceof/has, alien table size | `Alien` | input/output | H | The JS host binding. See below. |
| 159 | peekExpat | unused | — | D | |

## Counts

| Disposition | Count | |
|---|---|---|
| N — native method | 76 | arithmetic, floats, strings, arrays, allocation, identity, `class`, closures, perform (80 if asin–atan2 are kept) |
| K — kernel operation | 42 | activations, closure internals, slot access, canonical marks, populations, become, reclassify, clocks, GC, actors, print, halt, exit |
| R — role | 4 | ensure, on:do:, simulation root, dispatch boundary |
| H — host interface | 15 | file I/O 2, JS bridge 13 (to become FFI calls) |
| D — drop | 24 | Fuchsia 12; asin–atan2 (unless methods are added), instVarSize, three closure setters, doPrimitive, flushCache, peekExpat, quickReturnSelf |
| **Total** | **161** | |

(Several rows could go either way; the counts are approximate by design.)

## Observations

1. **The portable kernel is small.** Without host entries and the drops, it
   is 122 operations, of which 76 are plain value, collection and
   closure operations that become native methods. The reflective and
   effectful kernel proper (the K rows) is 42.
2. **Native methods carry the performance; the mirror carries the
   authority.** Every hot primitive is an N, so the bestowed-native design
   keeps today's speed. Everything going through the VM mirror proper is
   reflective or effectful and not hot.
3. **The four markers should become roles.** They exist only so the VM and
   the Simulator can recognise particular methods by number. Handing the VM
   the method objects at bootstrap removes the numbering entirely, which is
   what the V5 port plan already does for the NS2JS Simulator.
4. **Activation and closure internals are public methods today.** Anyone can
   send `sender:` or `tempAt:put:` to an activation they get hold of. In the
   new VM they belong behind the activation mirror's rights
   (`editActivation`, `controlContinuation`), as in the formal semantics.
   That is a behaviour change for the existing debugger and exception code.
5. **The JS bridge should not be a stack machine.** Thirteen primitives
   operate a shared JS operand stack (push, pop, then perform). Both the
   round-3 bug and the operand-stack leak came from that design. A host
   interface with one *call* operation taking the receiver, selector and an
   argument array, and returning a result or a host exception, makes the
   operand discipline impossible to get wrong. The same shape serves a
   native FFI. With a general FFI there are no OS-specific operations: the
   Fuchsia primitives (and file I/O) exist only because psoup lacks one.
6. **Trivial-method primitives are compiler encodings.** `quickReturnSelf`
   (200) and the getter/setter header flags (256/512) are optimisations of
   method shape, not operations. The new VM's method format should have a
   method-kind field for them.
7. **Design doc correction:** section 3 needs an *output* category, separate
   from input, for effects that send data out. Replay must suppress or divert
   them but need not record them.
8. **Missing from today's table:** an identity-preserving mixin-applications
   query (required by the formal semantics), a kernel/bytecode version query
   (design doc 7), snapshot save/restore (design doc 6), and the
   native-installation operation itself (design doc 8).
