# VM kernel operations

**Date:** 2026-11-10
**Status:** Draft for review. The step 2 deliverable of
`VM_KERNEL_CONTRACT_DESIGN_2026-11-09.md` section 11. Selector names are
proposals; where the current kernel already has a selector, it is kept.
**Inputs:** the design doc (sections 2, 3 and 8 agreed), the classification
`VM_KERNEL_PRIMITIVE_CLASSIFICATION_2026-11-09.md`, psoup `extraRevs`
@ `86f0ec9` (`vm/primitives.cc`, `vm/object.h`, `newspeak/*.ns`), and the
reflective commands and queries of `formal-semantics/reflection-semantics.tex`.

---

## 0. Conventions

**One mechanism.** Every VM operation is a **native method**: a method object
whose kind is *native* and which names an entry in the VM's native catalog
(section 8 of the design doc). Natives differ only in the class they are
installed on:

- **Value natives** (section 3) are installed on kernel classes (`Integer`,
  `Array`, `Closure` …). Anyone can send them; they carry no authority.
- **Kernel operations** (sections 4–9) are installed on the VM mirror class.
  Only holders of the VM mirror can send them. Starting all-or-nothing
  (decided); an attenuated mirror is a class carrying a subset of these
  natives. The *Right* column names the formal-semantics right
  (`reflection-semantics.tex`, eq. `mirror-targets-rights`) that an
  attenuated mirror would need.

Below, `vm` is the VM mirror and `a`, `c`, `o`, `m` are an activation, a
class, an object and a method.

**Outcomes.** A native is total. It does exactly one of:

1. **answers** a value;
2. **tail-sends** a defined message, written `↪ x addFromInteger: self` (the
   send's result is the native's result; no frame of the native remains);
3. **fails**: the VM allocates an instance of the **failure exception
   class** (a role, section 2) carrying the native's name, receiver,
   arguments and one of the reasons below, and sends it `signal`. This is the
   semantics' `runtimeError` → `reifyError` → `signal` path
   (`kernel-semantics.tex`, rule Native-Fail): reification runs no user code,
   and the class's `signal` method chooses the specific exception.

| Reason | Meaning |
|---|---|
| `#wrongKind: i` | Argument *i* (0 = receiver) is not of an acceptable kind. |
| `#outOfRange: i` | Argument *i* is an index or size outside its range. |
| `#zeroDivide` | Division or modulus by zero. |
| `#arity` | Wrong number of arguments for a closure or `perform:`. |
| `#notInstantiable` | The class's format cannot be instantiated this way. |
| `#dead` | An activation that has returned, or an alien or expat that has ended or did not survive a restore. |
| `#notAtSafepoint` | A reflective commit requested where it cannot be made atomic. |
| `#exhausted: r` | A resource limit: `#memory`, `#stack`, `#nesting`, `#handles`. |
| `#host: e` | The host raised; `e` is the host exception as an alien. |
| `#unsupported` | Not provided on this host (for example a file system in a browser). |

**Category** is the effect class of the agreed design doc section 3: pure,
heap, control, reflective, turn, input, output, resource. It decides replay
treatment: *input* and *output* are logged; *output* is also suppressed or
diverted during replay and compared against the log for divergence.

**psoup** gives the primitive numbers each row replaces, so every row can be
traced back to the classification.

## 1. Program and heaps

*Decided 2026-11-10:* where psoup and the formal semantics differ, the formal
semantics wins. Layouts are a **hybrid**, replacing the earlier "all hidden"
decision: immutable data has its layout in the contract, and live control
state is hidden.

The model is the formal semantics' (`actor-semantics.tex` eq.
`actor-configuration`, `newspeak-semantics.tex` eq. `heap-records`):

- **One program per VM cohort**, shared by all its actors: the installed
  methods and mixins, with stable identities (the semantics' `i_f`, `M`).
  Installed program objects are immutable, so sharing them across actor
  heaps is safe.
- **One heap per actor**, holding that actor's class objects, ordinary
  objects, activations and closures. Another actor's objects are reachable
  only as far references.

| Kind | Layout | Mutability | Lives in |
|---|---|---|---|
| Method | **contract** | Frozen once installed | the shared program |
| Mixin | **contract** | Frozen once installed | the shared program |
| Class, metaclass | **contract** | Read-only; changed only by commit | the owning actor's heap |
| Message | **contract** | Immutable; built by the VM | heap |
| Activation, Closure | **hidden**: handles, section 5 operations | Through section 5 only | heap |
| Ephemeron, WeakArray | **hidden**: natives | Through natives | heap |
| Array, ByteArray, String, numbers | no fields: natives | | heap (immediates: none) |

**Contract fields** (names are proposals):
- *Method*: header (V5, versioned: kind — ordinary, native, getter, setter,
  return-self; argument and temp counts; native identity for kind native;
  slot index for getter and setter), literals, bytecode, mixin, selector,
  access, source.
- *Mixin*: name, methods (an Array), enclosing mixin, slot declarations
  (names, in order; the VM derives instance layouts from them).
- *Class*: mixin, superclass, enclosing object, name; *metaclass*: its
  class.
- *Message*: selector, arguments.
- Each of Method, Mixin and Class also has one **library field** that the
  VM never reads. The mirror library keeps its richer information there
  (the semantics' factory descriptor `q` and provenance `χ`, nested class
  declarations, typing data), so it can grow without a contract change.
- Everything else the VM needs (class ids, final layouts, lookup caches,
  JIT data) is VM-private and outside the layout. psoup's `classid`,
  `format` and `subclasses` fields leave the contract; `subclasses` is
  replaced by `mixinApplicationsOf:` (section 4).

**Life cycle of program objects.** The mirror library builds new methods,
mixins and classes as ordinary objects in its own actor's heap: allocation
plus ordinary slot writes, as today. Until committed they are mutable and
mean nothing to the VM. `commit:` (section 6) validates them, installs them,
and **freezes** them; methods and mixins move into the shared program. A
write to a frozen object fails with `#wrongKind: 1`, so psoup's stale-cache
problem (in-place writes served stale lookups until the next GC) cannot
happen. psoup's canonical mark (126, 127) is the freezing mechanism.

**Other rules:**
- *Slots* are identified as in the semantics, by application-qualified slot
  identity `(C, j)`. `slotOf:at:` takes an index into the object's final
  layout. Changing a class's slots migrates its instances in every heap by a
  layout map (section 6).
- *Method literals are values* (numbers, strings, symbols, arrays of values,
  installed program objects), because methods are shared by every actor.
  psoup allows arbitrary objects as literals.
- *Become exists only inside `commit:`*, for methods, mixins and classes.
  There is no general become: the semantics has none, and across heaps it
  cannot be implemented.

## 2. Roles

Objects the VM must recognise. Set once, at bootstrap, by
`vm bootstrapRoles: aRecord` (category reflective, right primitive), which
replaces psoup's object store (`ObjectStore::Layout`) and its marker
primitives. Changing a role later is not supported in the first version.

| Role | psoup | Used for |
|---|---|---|
| `nil`, `true`, `false` | object store | |
| Kernel classes: SmallInteger, MediumInteger, LargeInteger, Float, String, ByteArray, Array, WeakArray, Ephemeron, Closure, Activation, Method, Message, Alien, Expat | object store | Allocation of literals and results, `class` of immediates. Alien and Expat are new (section 10). |
| The message loop | object store | Receives turns. |
| `doesNotUnderstand:` | object store | Lookup failure. |
| `nonBooleanReceiver:` | object store | Inlined conditionals given a non-Boolean. |
| `cannotReturn:` | object store | Non-local return to a dead home, or across a callback boundary. |
| `aboutToReturnThrough:` | object store | Unwinding through an `ensure:` frame. |
| `unusedBytecode` | object store | Becomes a failure (`#wrongKind: 0` on the method) rather than an upcall. |
| `dispatchMessage:port:`, `dispatchSignal` | object store | Turn entry points. |
| **Failure exception class** | new | Every native failure (section 0). The VM instantiates it with the failure data and sends `signal`; its `signal` raises the specific exception. |
| **Restore role** | new | Sent once after a snapshot is restored into a new host (design doc section 6, rule 3). |
| **Finalize role** | new | Runs an Ephemeron's finalizer. A logged input (design doc section 5). |
| `Closure>>ensure:` method | 113 | Unwind search. |
| `Closure>>on:do:` method | 116 | Handler search. |
| Simulation root method | 142 | Bottom frame of a simulated thread. |
| Callback dispatch methods | 168 | The callback boundary frame (design doc 4.2). |
| V5 special selectors | object store | The bytecode set's table of selectors with short sends. |

## 3. Value natives

On kernel classes, public, no authority. All are pure or heap, so none is
logged.

### 3.1 Numbers

Integer natives handle every integer representation (Small, Medium, Large);
the representation classes are the VM's business. For mixed arithmetic,
"↪" gives the tail send for an argument the native does not handle.

| Selector (receiver) | psoup | Result | Otherwise |
|---|---|---|---|
| `Integer>> + - *` | 1–3 | Integer | ↪ `x addFromInteger: self` (resp. `subtractFromInteger:`, `multiplyFromInteger:`) |
| `Float>> + - *` | 1–3 | Float | ↪ `x addFromFloat: self` (resp. …) |
| `Number>> + - * /` (other kinds of Number) | 1–4 | Number | ↪ `other addFromNumber: self` (resp. …) |
| `Integer>> /` | 4 | — | **Not a native.** An ordinary method: non-Integer → `other divideFromNumber: self`; zero → fail; otherwise `//` if exact, else `Fraction numerator:denominator:`. psoup's fallback here was real code, which the no-fallback rule moves into Newspeak. Not hot. |
| `Number>> // \\ quo: rem:` | 5–8 | Integer or Float | `#wrongKind: 1`; `#zeroDivide` |
| `Number>> = ` | 9 | Boolean | A non-number answers `false` (decided 2026-11-10; psoup fails). |
| `Number>> < > <= >=` | 10–13 | Boolean | Fraction argument ↪ the reversed comparison (`other >= self` for `<` …); otherwise `#wrongKind: 1` |
| `Number>> asInteger`, `asFloat` | 14, 15 | Integer, Float | `asInteger` of NaN or infinity: `#outOfRange: 0` |
| `Integer>> bitAnd: bitOr: bitXor: & \|` | 16–18 | Integer | `#wrongKind: 1` |
| `Integer>> << >>` | 19, 20 | Integer | `#wrongKind: 1`; a shift that would exhaust memory: `#exhausted: #memory` |
| `Float>> floor ceiling rounded` | 21, 22, 125 | Integer | NaN or infinity: `#outOfRange: 0` |
| `Float>> sin cos tan exp ln log sqrt` | 23–25, 30–33 | Float | (IEEE results, no failure) |
| `Float>> pow:` | 131 | Float | `#wrongKind: 1` |
| `Float>> arcSin arcCos arcTan arcTan:` | 26–29 | Float | Only if the methods are added (classification: D or N). |
| `Float>> asStringFixed: asStringExponential: asStringPrecision:` | 108–110 | String | `#outOfRange: 1` |
| `Number>> asString` | 111 | String | |
| `Float class>> parse:` | 132 | Float | `#wrongKind: 1` (not a float literal) |

**Determinism (decided 2026-11-10).** Float results are bit-identical across
hosts, for replay and for Croquet: the VM canonicalises NaN bit patterns, and
the transcendental functions come from one bundled implementation, not the
host's `libm` or JS `Math`.

### 3.2 Identity and class

| Selector | psoup | Result | Notes |
|---|---|---|---|
| `Object>> ==` | 86 | Boolean | Inline fast-path candidate. |
| `Object>> class` | 85 | Behavior | |
| `Object>> identityHash`, `hash` | 87 | SmallInteger | **Deterministic** (decided 2026-11-10): a function of the object's allocation position in its actor's heap; for program entities, of their creation order in the program. Never logged. Two actors' objects may share a hash. |

### 3.3 Allocation and indexed objects

| Selector | psoup | Result | Failure |
|---|---|---|---|
| `Class>> basicNew` | 34 | instance | `#notInstantiable` |
| `Array class>> new:`, `ByteArray class>> new:`, `WeakArray class>> new:` | 38, 46, 42 | instance | `#wrongKind: 1`, `#outOfRange: 1`, `#exhausted: #memory` |
| `at:`, `at:put:`, `size` on Array, ByteArray, WeakArray | 39–41, 47–49, 43–45 | element / argument / SmallInteger | `#wrongKind: 1`, `#outOfRange: 1`; ByteArray `at:put:` of a non-byte: `#outOfRange: 2` |
| `String>> at:`, `size` | 51, 53 | SmallInteger (a byte) / SmallInteger | `#outOfRange: 1` |
| `ByteArray>> copyFrom:to:` and `copyByteArrayFrom:to:` on both | 50 | ByteArray | `#outOfRange: 1/2` |
| `copyStringFrom:to:`, `String>> copyFrom:to:` | 121 | String | `#outOfRange: 1/2` |
| `Array>> copyFrom:to:` | 81 | Array | `#outOfRange: 1/2` |
| `replaceFrom:to:with:startingAt:` on ByteArray, Array | 79, 80 | receiver | `#wrongKind: 3`, `#outOfRange: 1/2/4` |
| `ByteArray class>> withAll:`, `String class>> with:`, `withAll:` | 122–124 | instance | `#wrongKind: 1`. The native accepts both ByteArray and String arguments, which removes psoup's convert-and-retry fallbacks (`withAllAgain:`). |

### 3.4 Strings

| Selector | psoup | Result | Failure |
|---|---|---|---|
| `String>> hash` | 54 | SmallInteger | |
| `String>> =` | 114 | Boolean | (non-String answers false) |
| `String>> ,` | 115 | String | `#wrongKind: 1` |
| `startsWith:`, `endsWith:` on String, ByteArray | 117, 118 | Boolean | `#wrongKind: 1` |
| `indexOf:startingAt:`, `lastIndexOf:startingAt:` on String, ByteArray | 119, 120 | SmallInteger (0 if absent) | `#wrongKind: 1`, `#outOfRange: 2` |

Classification marks 117–120 as L→N: native unless measurement says the
Newspeak version is fast enough.

### 3.5 Closures and sends

| Selector | psoup | Result | Failure |
|---|---|---|---|
| `Closure>> value`, `value:`, `value:value:`, `value:value:value:` | 90–93 | closure result | `#arity` |
| `Closure>> valueWithArguments:` | 94 | closure result | `#wrongKind: 1`, `#arity` |
| `Closure>> numArgs` | 75 | SmallInteger | |
| `Object>> perform:withArguments:` | 89 | send result | `#wrongKind: 1/2`; DNU is the normal DNU, not a failure |

The Simulator recognises these method objects (by role or by native
identity) because it reifies their frames.

## 4. Objects and populations (kernel operations)

| Operation | psoup | Category | Right | Result | Failure |
|---|---|---|---|---|---|
| `vm slotOf: o at: i` | 35 | heap | inspect | slot value | `#outOfRange: 2` |
| `vm slotOf: o at: i put: v` | 36 | heap | editObjectSlots | `v` | `#outOfRange: 2`; frozen object (canonical, or an installed method, mixin or class): `#wrongKind: 1`. A one-command commit of `writeObjectSlot` (section 6). |
| `vm classOf: o` | 85 | heap | inspect | Behavior (the real class, whatever `class` answers) | |
| `vm is: o identicalTo: p` | 86 | pure | — | Boolean | |
| `vm identityHashOf: o` | 87 | resource | — | SmallInteger | |
| `vm isCanonical: o` | 126 | heap | inspect | Boolean | |
| `vm markCanonical: o` | 127 | heap | editObjectSlots | `o` | |
| `vm allInstancesOf: c` | 96 | reflective | inspect | Array, in allocation order | Cohort-wide, as in the semantics (`eq:all-instances-of` ranges over every actor heap). |
| `vm mixinApplicationsOf: m` | new | reflective | inspect | Array of classes, in allocation order | Cohort-wide (`eq:mixin-applications`). Required by `mixinApplicationsQuery`. |
| `vm reclassify: o as: c` | 134 | reflective | reclassifyObject | `o` | `#wrongKind: 2` if `c`'s layout is incompatible with `o`. A one-command commit of `changeObjectClass` (section 6). |

Orders are deterministic by definition (allocation or creation order), so
these queries need no log entry (design doc section 5).

## 5. Activations and closures (kernel operations)

An Activation is a handle (section 1). The reads and writes below map to the
formal semantics' activation descriptors and commands. All fail with `#dead`
on an activation that has returned.

| Operation | psoup | Category | Right | Formal semantics |
|---|---|---|---|---|
| `vm currentActivation` | 133 | control | inspect | `currentActivationQuery` |
| `vm senderOf: a` | 55 | reflective | inspect | `activationControlQuery` |
| `vm methodOf: a`, `receiverOf: a`, `closureOf: a`, `pcOf: a`, `depthOf: a`, `tempOf: a at: i` | 57, 59, 61, 63, 65, 67 | reflective | inspect | `activationDescriptorQuery` |
| `vm tempOf: a at: i put: v` | 66 | reflective | editActivation | `writeActivationLocal`, `writeActivationParameter` |
| `vm senderOf: a put: s` | 56 | reflective | editActivation | `changeActivationContinuation` |
| `vm pcOf: a put: p` | 58 | reflective | editActivation | (part of stack replacement) |
| `vm depthOf: a put: n` | 140 | reflective | editActivation | (part of stack replacement) |
| `vm markUncontinuable: a` | new | reflective | editActivation | `markActivationUncontinuable` |
| `vm continueAt: a with: v` | 95 | control | controlContinuation | `continueAtActivation` |
| `vm newActivationFor: m receiver: r closure: k pc: p` | 68 + 60, 62, 64 | reflective | editActivation | `freshFrame`; the Simulator's frames |
| `vm closureIn: a pc: p numArgs: n copied: anArray` | 69 | reflective | editActivation | |
| `vm definingActivationOf: k`, `initialPcOf: k`, `copiedOf: k` (an Array), `copiedOf: k at: i put: v` | 70, 71, 73, 77, 78 | reflective | inspect / editActivation | |

psoup's setters for `method:`, `closure:` and `receiver:` on a live
activation (60, 62, 64) become arguments of `newActivationFor:…`. Changing
them on an activation that is already running is not offered: no current
user, and the formal semantics has no command for it.

**pc.** Positions are V5 bytecode positions in the method's bytecode, never
machine addresses. A JIT maps them (formal semantics `machinePoint`).

## 6. Program change (kernel operations)

| Operation | psoup | Category | Right | Result | Failure |
|---|---|---|---|---|---|
| `vm commit: changeSet` | 98, 134 | reflective | the `requiredRight` of each command | the new program version | `#wrongKind: i` (command *i* is malformed), `#notAtSafepoint` |
| `vm programVersion` | new | reflective | inspect | SmallInteger | |
| `vm nativeMethod: name selector: s` | new | reflective | primitive | a fresh, uninstalled native Method | `#wrongKind: 1` (no such native) |
| `vm natives` | new | reflective | inspect | Array of (name, kernel version) pairs | |
| `vm applyMixin: m superclass: s enclosingObject: eo` | new | heap | — | a new class object in the caller's heap | `#wrongKind: 1/2` |

**This keeps today's install shape.** The mirror library builds fresh
methods, mixins and classes in Newspeak, validates them, and installs
everything with one kernel call. psoup's bulk become becomes `commit:`.
Reading an installed method, mixin or class is an ordinary slot read
(section 1), so no `describe:` operation is needed.

**A change set** is the formal semantics' command list Δ
(`reflection-semantics.tex` eq. `reflection-command-grammar`) after the
library has validated and prepared it:
1. **Forwarding pairs** for methods, mixins and classes: each old object
   takes the identity of its new replacement, which is frozen. Because
   installed program objects are immutable, this is exactly the semantics'
   "update the record at a stable identity". A new object with no old
   partner is simply added. Removal (`removeMethodDefinition`) is a new
   mixin whose methods array lacks the method.
2. **Layout maps** for every class whose slots changed: old slot identity to
   new slot. New slots start as `nil`, as the semantics requires; their
   initializers do not run. The library computes
   them; the VM applies them to every instance in every heap of the cohort
   (`reconcileObjectLayouts`) and keeps or drops each per-receiver
   nested-class cache entry as the library says (`reconcileNestedCaches`).
   Today the library migrates instances itself, by allocating replacements
   and adding them to the become; with a heap per actor it can no longer
   reach other actors' instances atomically, so this one part moves into the
   VM. With a single actor the result is the same as today.
3. **Object commands** (`changeObjectClass`, `writeObjectSlot`).
4. **Activation, continuation and debugger commands** (sections 5 and 7).

**The VM checks only what its own safety needs**: the contract fields hold
the right kinds, V5 bytecode decodes, literal and slot indices are in range,
literals are values, superclass chains are acyclic, layout maps cover every
changed class, and the rights are held. Everything else (`validationHolds`,
re-elaboration, conflict checks) is the library's job (design doc section 2).

**Atomicity.** All or nothing. Caches and inline fast-path guards are
invalidated, the program version increases by one, and every actor sees the
new program at its next step. Frames already running keep their code, as in
the semantics' observation table (eq. `reflection-version-observation`).

**Safepoint** (semantics: between any two steps of any actor, never inside
one). With all of a cohort's actors on one thread, the commit call is itself
a safepoint. With several threads, the VM stops every actor of the cohort at
a safepoint first. A paused actor is always at one.

**Natives** are installed like any method: the fresh Method from
`nativeMethod:selector:` goes into a new mixin's methods array, and the
mixin is committed. Nothing in source can produce one (design doc
section 8).

**Single-command shortcuts.** `vm slotOf:at:put:` and `vm reclassify:as:`
(section 4) are exactly one-command commits. They are kept as operations
because serialisation (PrimordialFuel) uses slot writes heavily.

## 7. Turns, actors and the debugger (kernel operations)

| Operation | psoup | Category | Right | Result | Notes |
|---|---|---|---|---|---|
| `vm spawn: mixin` | 137 | turn | — | far reference to the new actor's class | The semantics' `spawn(M)` (`actor-semantics.tex` eq. `create-actor`): a fresh actor with the base heap, in the same cohort and program. Replaces psoup's spawn from snapshot bytes. Starting another cohort (another process or worker) is a host start from a snapshot, not this operation. |
| `vm createPort` | 135 | turn | — | port id | |
| `vm closePort: p` | 136 | turn | — | `nil` | |
| `vm send: data to: p` | 138 | turn, output | — | `nil` | Logged as output; delivery is the receiver's input. |
| `vm finishTurn: wakeup` | 139 | turn | — | does not return | Ends the turn and returns to the host's event loop with the time of the next timer: the turn layer's one host hook for waiting on events (design doc 4.5). |
| `vm exit: code` | 107 | turn | — | does not return | |
| `vm pause: actor reason: r` | new | reflective | controlActorStack | `nil` | `pauseActor` |
| `vm stackOf: actor` | new | reflective | inspect | an immutable stack image | `actorStackQuery` |
| `vm replaceCurrentStackWith: image` | new | reflective | controlActorStack | does not return | `replaceCurrentActorStack` |
| `vm replaceStackOf: actor with: image` | new | reflective | controlActorStack | `nil` | `replacePausedActorStack` |
| `vm resume: actor` | new | reflective | controlActorStack | `nil` | `resumePausedActorAtFullSpeed` |
| `vm replaceStackOf: actor with: image andResume` | new | reflective | controlActorStack | `nil` | `replaceAndResumePausedActorStack` |

Each incoming event (message, timer, host callback with no turn on the
stack) is delivered through the dispatch roles and is a logged input.

**Unhandled exceptions pause the actor** (decided 2026-11-10, following the
semantics' `pausedTurn`, not psoup). The exception library calls `vm pause:`
on its own actor. The turn stays on the stack; deliveries still queue, but
the actor runs nothing until a debugger resumes it or replaces its stack.
The debugger, normally another actor, is told by an ordinary message and
works through a mirror. psoup instead detaches the stack into a Thread
object and lets the actor go on with other turns.

**Exception inside a callback.** A callback cannot stay paused, because the
host is waiting on it synchronously. Per the decision of 2026-11-09 (design
doc 4.2), the callback's frames are copied into a stack image for the
debugger, the callback is abandoned, and the host sees an exception. The
exception library does this with `vm abandonCallback: exception` (below);
`kernel-semantics.tex` gives the rule.

| Operation | psoup | Category | Right | Result | Notes |
|---|---|---|---|---|---|
| `vm abandonCallback: e` | new | control, output | — | does not return | Snapshots the frames above the nearest callback boundary, sends the snapshot to the actor's designated debugger, removes those frames, and makes the waiting host call fail. Fails with `#wrongKind: 0` if no callback is in progress. |

## 8. Time, environment, output (kernel operations)

| Operation | psoup | Category | Result |
|---|---|---|---|
| `vm monotonicNanos` | 100 | input | Integer |
| `vm utcNanos` | 101 | input | Integer |
| `vm randomBytes: n` | new | input | ByteArray from host entropy |
| `vm hostDescription` | 99 | input | String (replaces `operatingSystem`) |
| `vm print: aString` | 102 | output | `nil` |
| `vm halt` | 103 | control | Enters the debugger when there is one; otherwise ends the VM with a stack dump. |
| `vm versions` | new | resource | `{kernel version. bytecode version}` |

## 9. Memory, snapshots, replay (kernel operations)

| Operation | psoup | Category | Result | Notes |
|---|---|---|---|---|
| `vm collectGarbage` | 105 | resource | `nil` | Weak clearings and finalizations it causes are logged like any other (design doc section 5). |
| `vm heapStatistics` | new (169 in part) | resource | record | Sizes, counts, handle-table size. |
| `vm snapshot` | new | resource | ByteArray | Includes paused stacks (decided). Lazy slots holding aliens are reset; other aliens are written as dead (design doc section 6). |
| `vm checkpointPolicy: p` | new | resource | `nil` | Checkpoint frequency; may change during execution (decided). |
| `vm checkpointNow` | new | resource | `nil` | Mid-turn checkpoints allowed (decided). |
| `vm logPosition` | new | resource | Integer | Position in the input/output log. |

Restoring is not an operation: it starts a VM (`spawn:` for an actor, or a
host start for the whole VM), after which the restore role runs.
Replay control (stepping back, replaying to a position) is driven from
outside the replayed actor by the debugger; whether that is a kernel
operation or a host-side tool is left to the time-travel design.

## 10. Host interface: the FFI

Replaces psoup's 13 JS stack-machine primitives (154–167, 169) with a
call-based interface. These are natives on `Alien`, the host-reference
class, and on the VM mirror for the entry points. Every call is **input**
(its result) and, when it has effects, **output** too; both are logged.

| Operation | psoup | Result | Failure |
|---|---|---|---|
| `vm hostGlobal` | — | Alien for the host's global object | |
| `alien at: key` | 160 | value or Alien | `#host: e`, `#dead` |
| `alien at: key put: v` | 161 | `v` | `#host: e`, `#dead` |
| `alien removeKey: key` | 162 | Boolean | `#host: e`, `#dead` |
| `alien includesKey: key` | 167 | Boolean | `#host: e`, `#dead` |
| `alien call: key withArguments: anArray` | 163 | value or Alien | `#host: e`, `#dead`, `#exhausted: #nesting` |
| `alien callWithArguments: anArray` (the alien is a function) | 163 | value or Alien | same |
| `alien newWithArguments: anArray` | 164 | Alien | same |
| `alien isInstanceOf: anAlien` | 166 | Boolean | `#host: e`, `#dead` |
| `vm expat: aClosure` | 156 | Expat (a host-callable function) | |
| `expat release` | — | `nil` | Calls after release fail on the host side with a defined error. |

psoup's operand-stack primitives (154 push value, 155 push alien, 157 pop,
158 pop into the handle table) have no counterpart: their work is the
marshalling of arguments and results inside each call. 169 (handle-table
size) moves into `vm heapStatistics`.

**Marshalling** (exact, no operand stack): `nil`, Booleans, SmallIntegers,
Floats and Strings cross by value (host `null`/`undefined` both arrive as
`nil`; an Integer outside the host's exact range fails with `#outOfRange`).
Every other host value arrives as an Alien; an Alien passed back arrives as
its host object; an Expat arrives as its host function. Any other Newspeak
object fails with `#wrongKind`.

**Callbacks** follow design doc section 4 (decided 2026-11-09): a callback
arriving during a turn is a sub-step of that turn, runs above the boundary
role, never drains the queue, and may call an expat synchronously only from
its owning actor's turn. **Arity (decided 2026-11-10):** as in JS, extra
host arguments are dropped and missing ones arrive as `nil`. psoup today
raises on extra arguments; NS2JS already drops them.

**Native FFI.** The same operations, with `call:withArguments:` on a C
function alien plus a signature describing the C types, cover native hosts.
File I/O (128, 130) becomes a Newspeak library over it. Not specified
further here.

## 11. Cross-check against the classification

Every psoup primitive that the classification keeps appears in one row
above:

| Disposition | Count | Where |
|---|---|---|
| N (native) | 76 | Section 3, except `Integer>>/` (4), which becomes a library method. 75 natives. |
| K (kernel) | 42 | Sections 4–9. psoup's `method:`, `closure:`, `receiver:` setters (60, 62, 64) merge into `newActivationFor:…`. Bulk become (98) and `adoptInstance` (134) are replaced by `commit:` (134 also survives as the `reclassify:as:` shortcut). Spawn (137) now takes an installed mixin, not snapshot bytes. |
| R (role) | 4 | Section 2. |
| H (host) | 15 | Section 10 (JS bridge) and the native FFI note (file I/O). |
| D (drop) | 24 | Not listed. |

New operations, not in psoup: `bootstrapRoles:`, `mixinApplicationsOf:`,
`markUncontinuable:`, `commit:`, `programVersion`,
`nativeMethod:selector:`, `natives`,
`applyMixin:superclass:enclosingObject:`, the six debugger operations of
section 7, the Ephemeron natives,
`abandonCallback:`, `randomBytes:`, `versions`, `heapStatistics`, `snapshot`,
`checkpointPolicy:`, `checkpointNow`, `logPosition`, `hostGlobal`, the
call-based Alien operations, `expat:`, `release`, and the failure, restore
and finalize roles.

## 12. Decisions and open questions

**Decided 2026-11-10:**
- Population queries are cohort-wide, as in the semantics (section 4).
- An exception in a callback abandons it through `vm abandonCallback:`
  (section 7); `kernel-semantics.tex` has the rule.
- Native failure goes through the semantics' `runtimeError` path with a
  failure exception class, not a separate failure method (section 0).
- The formal semantics takes precedence over psoup: one program per cohort
  shared by all its actors, a heap per actor (section 1), and unhandled
  exceptions pause the actor (section 7).
- Identity hash is deterministic (section 3.2).
- `Number>> =` answers false for a non-number (section 3.1).
- Layouts are a hybrid (section 1): methods, mixins, classes and messages
  have contract layouts and are frozen once installed; activations, closures,
  ephemerons and weak arrays are hidden. This replaces an earlier decision
  the same day to hide all layouts.
- Callbacks drop extra host arguments and get `nil` for missing ones
  (section 10).
- Floats are bit-identical across hosts: bundled math library, canonical
  NaNs (section 3.1).

**Open:**
1. **Threads and cohorts.** A shared program means a cohort's actors share
   one address space. On the web that is one WASM instance, or several
   workers with shared memory. Actors on workers without shared memory would
   be separate cohorts, talking only through far references. Is that the
   intended model?
2. **Who may create classes.** `applyMixin:superclass:enclosingObject:` is
   needed by ordinary code (every nested class and mixin application). It
   should be reachable only through the language's own protocol, installed on
   the runtime's class-creation method, not as a public native.
