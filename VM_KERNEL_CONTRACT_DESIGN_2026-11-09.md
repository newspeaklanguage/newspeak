# VM kernel contract: design

**Date:** 2026-11-09
**Status:** Draft for discussion. Nothing here is decided unless it says so.
**Purpose:** Define the boundary between a new Newspeak VM (the planned Rust
VM) and the Newspeak code that runs on it, as a fixed set of operations reached
only through the VM mirror. This boundary is what the formal semantics
deliberately leaves open (see below). Once agreed, it becomes a new layer of
the formal semantics and the specification the new VM is built and tested
against.

Related: `formal-semantics/reflection-semantics.tex`, `formal-semantics/coverage.md`,
`VM_CRASH_TRIAGE_2026-11-09.md`, `BYTECODES_V4_V5_DIFF_2026-07-13.md`,
`CODEGEN_V5_PORT_PLAN_2026-07-14.md`, `VMMirror.ns`.

---

## 1. Where the formal semantics stands

The formal semantics specifies the **reflective behaviour programs observe**:
mirror capabilities and attenuation, inspection queries, transactional
program change, object reclassification, activation access, stack snapshots
and replacement, atomic commit at a safepoint, population queries, and weak
collections. It does not specify the VM underneath, and says so:

- `coverage.md`: *8.3–8.3.1 Platform and VM mirror — Parameterized — required
  protocols and failure boundary must be stated*; *8.5 Aliens and expats —
  Parameterized — synchronous alien callbacks and expat lifetime constraints
  remain platform obligations.*
- Rule `VM-Primitive` (`reflection-semantics.tex`, end): a VM primitive is an
  ordinary message to a mirror holding the `primitive` right, and its effect
  is an opaque `hostPrimitive(Ω, s, ō)`.
- The bootstrap basis (`front-end-semantics.tex`) leaves decoders, artifact
  loading, `primitiveStep`, allocation and host I/O as VM parameters.

**Keep as is:** the capability rule (no primitive syntax, no ambient VM
mirror, attenuation only); per-frame control images with `machinePoint` and
the Simulator refinement obligation (room for a JIT that can fall back to
interpretation, and the exact state time travel must rebuild); atomic commit
at a safepoint with pause tokens and whole-stack replacement; the population
queries; the weak-collection semantics; the artifact-validity boundary.

## 2. Two layers

1. **Mirror library** — Newspeak code. Implements the reflective protocol of
   the formal semantics: descriptors, validation, reconciliation,
   re-elaboration, transactions. Normative reference: the existing
   reflection semantics, unchanged.
2. **VM kernel** — implemented by the VM, reached only through the VM mirror.
   Small, fixed, versioned. Everything the library cannot do in Newspeak.

**Obligation:** the mirror library running on the kernel refines the
reflective rules. This keeps the VM small: the Rust VM never implements
`describeMixin`, validation, or re-elaboration; it implements the kernel.

## 3. Kernel operations by category

Each operation states its result, the exception it raises on failure, and its
**effect class**. The effect class matters for time travel (section 5) and for
efficiency (section 8).

| Class | Meaning | Examples (from today's 161 psoup primitives) |
|---|---|---|
| **pure** | A function of its arguments' values. | Integer and Float arithmetic and comparison, bit operations, float functions, number↔string conversion, string compare/concat/search/hash. |
| **heap** | Reads or writes the heap; deterministic given the heap. | `basicNew`, indexed `at:`/`at:put:`/`size` for Array, ByteArray, String, WeakArray; `instVarAt:`; copy/replace ranges; identity `==`; `class`. |
| **control** | Creates or transfers control. | Closure `value…`, `perform:`, `on:do:`, `ensure:`, non-local return, `currentActivation`, activation read/write/jump, the dispatch boundary. |
| **reflective** | Program change and populations; only at a safepoint. | Install class and method records, atomic commit of a prepared change set, `adoptInstance` (reclassification), `allInstances`, mixin applications, bulk become (`elementsForwardIdentity`), cache flush. |
| **turn** | Actors and the message loop. | Spawn, ports, send, `finish:`, await signal, exit. |
| **input** | Nondeterministic: a value enters from outside the VM. | Clocks, FFI calls (files and the JS bridge today), host callbacks and their arguments, messages from other VMs, randomness. |
| **output** | Only sends data out of the VM. Replay suppresses or diverts it. It is also recorded, and replay compares what it produces against the record to detect divergence. | Print, writing files, sending to a port, host calls made only for their effect. |
| **resource** | Observes or controls the VM's resources. | Collect garbage, identity hash, weak clearing (as observed), snapshot save. |

**Failure.** psoup's convention, where a failed primitive falls through to the
method body, is replaced by an exception from the mirror message: each
operation names its failure exception (wrong argument kind, index out of
range, host error carrying the host value, resource exhaustion).

**No fallback bodies (proposal).** The 203 primitive call sites in psoup's
sources have fallback bodies of these shapes:

| Shape | Sites | Replacement |
|---|---|---|
| `halt` (cannot fail in practice) | 104 | None. The native has no body. |
| Signal an exception (`ArgumentError`, `numArgsError:`) | 77 | The native fails with a reason. The VM sends one **failure role**, a method the mirror holder designates at bootstrap, with the native's name, receiver, arguments and reason. That method raises the specific exception. One place, not 77 copies. |
| Double dispatch for mixed arithmetic (`^x addFromInteger: self`) | 10 | Part of the native's contract: on an argument kind it does not handle, it *answers the result of a defined send* (`x addFromInteger: self`). This is a tail send, not arbitrary code. |
| Argument coercion and retry (122, 124) | 2 | The native accepts the wider argument, or the library converts before calling. |
| Marker primitives (ensure:, on:do:, dispatch boundary) | ~5 | Not fallbacks: the body *is* the implementation. They become roles (classification doc). |
| JS-bridge retry (157) | 1 | Disappears with the call-based FFI. |

So a native method is **total by contract**: it answers a value, makes its
defined tail send, or invokes the failure role. The Simulator models exactly
those three outcomes. A debugger shows a failure as a frame of the failure
role, called from the send site.

**Identity hash** is currently unspecified in the formal semantics. It must be
a kernel operation, and it is a source of nondeterminism unless it is defined
deterministically (for example from allocation order).

## 4. Host interface and synchronous callbacks

This is where every crash in the 2026-11-09 triage was. The contract states:

1. **A host call is one step of the current turn.** Arguments and results are
   values or alien handles; the operand passing is exact (the round-3 bug was
   an operand stack that leaked and duplicated arguments).
2. **A synchronous callback runs above an explicit boundary frame.**
   - An exception does not cross the boundary. It is reported at the boundary
     with the live stack (debugger), the callback is abandoned, and the host
     caller sees a host exception, which a Newspeak caller sees as a failed
     call-out. *Decided 2026-11-09:* reported at the innermost boundary, not
     propagated, because a live stack is worth more.
   - A non-local return across the boundary raises `cannotReturn:`.
   - Nesting is bounded, and exceeding the bound fails the call-out with a
     defined exception (psoup now: 64).
3. **A nested callback runs only that callback.** Other queued turns wait.
   psoup today drains the whole event queue inside a nested callback (H3),
   which breaks the formal semantics' rule that turns are atomic.
   *Decided 2026-11-09:* forbidden in the new VM, with the semantics extended
   as below.
   - *Is the semantics wrong?* Its atomicity rule is right, but it is
     incomplete: it does not model synchronous callbacks at all (coverage
     8.5). The extension: a callback entered while a turn is on the stack
     is a **sub-step of that turn**, like ordinary re-entrant calls in a
     sequential program. A callback entered with no turn on the stack is the
     start of a new turn (the event loop). No other turn starts until the
     outermost turn ends; sends made in the callback are queued.
   - *Against draining:* other turns would observe the suspended turn's
     state half-updated (the re-entrancy bugs of nested event loops). Turn
     order would depend on when the host happens to call back, which costs
     extra replay records and breaks Croquet's determinism. Drained turns can
     make call-outs that call back, so nesting grows with no bound; the
     handle-table and stack crashes of 2026-11-09 lived here. The debugger
     would show unrelated turns stacked on top of each other.
   - *For draining:* timers and other actors keep running during a
     long-lived callback, and psoup's implementation is simpler, since one
     entry point serves both the event loop and callbacks. That simplicity
     looks like the actual reason for the behaviour, not a design choice.
   - *Corner case:* a callback whose expat belongs to a different actor
     than the one whose turn is on the stack. Running it synchronously
     breaks actor isolation. Proposal: only the owning actor's turn may
     call an expat synchronously; otherwise the call becomes a message to
     the owner and the host gets no result.
   - *Risk:* existing code may depend, unknowingly, on queued work running
     during a call-out. Differential testing against psoup should check
     for it.
4. **Alien and expat lifetime.** An alien handle keeps its host object alive
   until the Newspeak alien is collected (psoup's handle table only grows
   today). An expat (Newspeak block callable from the host) has a defined
   lifetime and a defined failure when called after it ends.
5. **The same rules apply to a native FFI.** WASM/JS and native C calls differ
   only in marshalling. The FFI is the only host-specific part of the kernel:
   file I/O, OS services and the like are Newspeak libraries making FFI calls,
   never kernel operations of their own. The one host hook the turn layer
   needs is a way for the message loop to wait for host events.

## 5. Nondeterminism ledger (needed for time travel)

Time-travel debugging needs replay: every nondeterministic choice either is a
deterministic function of earlier state or is recorded as input. The ledger:

| Source | Treatment |
|---|---|
| Clocks, randomness, host I/O, host callbacks and their arguments, messages from other VMs | **input**: recorded, replayed. |
| Scheduler choice of the next turn | Recorded (or made deterministic). |
| GC timing, observable through weak clearing | The formal semantics calls this "permitted observable nondeterminism". For replay: either schedule collections deterministically (by allocation count) or record weak-clearing events. Host memory pressure must not trigger an unrecorded collection. |
| `allInstancesOf` / mixin-application order | The semantics leaves it "a platform choice". Must be deterministic (allocation order) or recorded. |
| Identity hash | Deterministic (allocation order) or recorded. |

A **checkpoint** is a snapshot (section 6); replay is checkpoint plus the
input log. *Decided 2026-11-10:*
- Checkpoints are taken during turns, not only between them, so they include
  paused stacks (consistent with section 6).
- Checkpoint frequency is a parameter. It can be adjusted, and may change
  dynamically during execution.
- Outputs are recorded as well as inputs. On replay, a produced output that
  differs from the recorded one signals divergence. (Recording a digest
  instead of the full output would keep the log small; not decided.)

## 6. Snapshots

The formal semantics has no semantics for saving and restoring a heap
(its "snapshots" are immutable stack images). Needed:

- What is saved: the store, the program version, actor states.
  *Decided 2026-11-09:* paused actor stacks are included, not only idle
  actors.
- **Two kinds of restore.** A *checkpoint* used for replay within a live
  session does not touch aliens: replay feeds recorded results from the
  input log, so the host is never asked again. Only a *restore into a new
  host* (a new page, a new process) must deal with host references; the
  rest of this section is about that case.
- **Aliens on restore (proposal).** *Decided:* invalidating aliens is
  acceptable. On top of that, the recipe for getting a host reference again
  is an ordinary **lazy slot**:
  1. On save, every lazy slot whose value is an alien is reset to its
     uninitialized state. After restore, the first read reruns the
     initializer, which looks the host object up again in the new host.
  2. Every other alien (in an ordinary slot, a collection or a paused frame)
     is dead after restore, and using it raises a defined exception.
  3. Host state the program *created* (DOM nodes, sockets, timers, pending
     promises) cannot be looked up again. It is rebuilt by the program from
     its own model, through a restore notification (for Hopscotch, a
     re-render).
  This keeps the recipe in source, needs no new syntax, and matches existing
  practice (platform services and CDN globals are already held in lazy
  slots). The VM's provenance alternative (an alien records how it was
  obtained and replays that) is rejected: most aliens come from calls with
  effects, so replaying the path is unsound, and the recipe would live in the
  VM, invisible to the program.
  *Accepted for now (2026-11-09).* Wrappers around aliens are uncommon; a
  wrapper holds its alien in its own lazy slot. Code that would keep an alien
  in a local across a point where the actor may be saved holds a wrapper
  instead, or reads the lazy slot again. This works for objects that are
  looked up, not for objects the program created (rule 3).
  Lazy initializers that are reset must be idempotent lookups. A lazy slot
  that *creates* a host object is rerun, giving a fresh object. That is
  usually acceptable, but it is a rule programmers must know.
- **Variant: reset all lazy slots on save (possible, not decided).** This
  gives a smaller saved state, which matters when a snapshot is the
  synchronized state (for example, a Croquet model). It is sound only under
  rules that the alien-only rule does not need:
  - *"Reset" means uninitialized, not nil*, since nil is a legitimate value.
  - *Mutation after initialization is lost.* `lazy registry = Map new`, later
    filled, comes back empty. So lazy slots must be recomputable caches, and
    state belongs in ordinary slots. This is a discipline, possibly a
    checkable one. Today's code certainly has lazy slots that hold state.
  - *Identity splits.* If another object kept the old value, it and the
    recomputed value differ. A writer can avoid this by dropping a value only
    when nothing outside the lazy slot reaches it (a reachability check at
    save time).
  - *Determinism under replication.* Initializers must be deterministic,
    which Croquet requires anyway. But a lazy slot first read from
    view-side (non-replicated) code runs its initializer on one replica only.
    That initializer allocates, which shifts allocation order, and so
    identity hashes and population order if those are defined by allocation
    (section 5). Either view code must not trigger model initializers, or
    allocation in them must not affect the deterministic orders.
- **VM identity (proposal, needs more thought).** In the actor semantics,
  `w` identifies a VM cohort, and a multi-VM system is a map from *distinct*
  `w` to configurations. Two running VMs with the same `w` is therefore
  ill-formed. A snapshot is a file and can be started any number of times,
  so identity cannot be a property of the snapshot. Proposal:
  1. **Every start mints a fresh identity**, whether a cold boot or a
     restore: an *incarnation id*, unguessable and drawn from host entropy
     (recorded as input, so replay reproduces it). Identity is never reused.
     An image that lives for decades has a new identity on every run;
     a shared snapshot run by someone else is a different VM.
  2. **A snapshot records its lineage**, meaning the id of the incarnation
     that saved it. Lineage is information, not authority: anyone holding a
     copy can read it, so it proves nothing.
  3. **Succession is a separate, explicit protocol.** A recovering
     incarnation claims to be *heir* to an old one so that peers redirect
     far references to it. This needs two things that lineage cannot give:
     - *Authority.* The old incarnation issues a succession capability when
       it saves a recovery snapshot. Holding the snapshot is not enough, or
       every copy could claim.
     - *Uniqueness.* A capability in a snapshot is copied with it, so two
       copies could both claim. Exactly one heir needs an arbiter: a lease
       or registry, or, in Croquet, the reflector's total order. A
       first-claim-wins rule at each peer is not enough, because different
       peers can accept different heirs.
  4. **An heir is a rollback.** It holds the old VM's state as of the
     snapshot, not as of the crash. Far references to objects created after
     the snapshot dangle, and messages since then are lost, unless the
     input log after the checkpoint survives. In that case the heir replays
     up to the crash (section 5) and is indistinguishable from the old VM up
     to that point. The claim carries the checkpoint position so peers know
     what was lost.
  Open: what peers do with far references the heir cannot honour, and
  whether ordinary restore (lineage only, no claim) needs anything more.
- The saved format names its kernel and bytecode versions (section 7).

## 7. Versioning and the bytecode format

The formal semantics deliberately leaves the VM-mirror selector set open. For
the kernel it should be closed and versioned: a snapshot (or the mirror
library) can ask the VM for its kernel and bytecode versions and fail with a
clear error on a mismatch. Today an old VM given a new snapshot dies with
*unimplemented code* (seen with primitives 168 and 169).

**Bytecode — decided 2026-11-09: the new VM implements V5 only; psoup stays on
V4 for the rest of its life; no converter, and no port of psoup.** Refining V5
where the new VM needs it is acceptable.

- V5 is an encoding redesign, not a semantics change (V4/V5 diff doc), and V5
  is already decided for the debugger and NS2JS (2026-07-14).
- Every vfuel is a build artifact regenerated from source by `build.sh`;
  users' work is saved as source, not as vfuels. So vfuel compatibility
  across bytecode sets buys little.
- The V5 code generator exists (`Newspeak2V5BytecodeCompilation.ns`) and
  already rejects the primitive pragma, which is what a mirror-based VM
  wants.
- Bootstrap: the existing V4 system on psoup runs the V5 code generator once
  to produce the new VM's first snapshots. After that the new VM compiles
  itself.
- Differential testing against psoup compares observable behaviour of the
  same source (V4 on psoup, V5 on the new VM), which is what we want to test
  anyway.
- A converter would have to handle V5's hard limits (send arity ≤ 15,
  selector index ≤ 4095, closure arguments ≤ 15), V4's runtime choice between
  local and non-local return, and remapping of debug-info positions. That is
  real work for something regenerating from source already does.

Settled: the instruction set is "our V5", with a version number, so it can
change where time travel and the kernel need it. Likely first refinements:
no primitive-number field in method headers, a native-method identity
(section 8), and a method-kind field for trivial methods (return self,
getters, setters) in place of `quickReturnSelf` and the accessor flags. Known upstream V5
issues: `pushClosure` arity decoded as 3 bits in the C++ VM, and the
Simulator's short branch-false dispatch bug (V5 port plan).

## 8. Efficiency of the mirror-based design

The concern: primitives were brought back for performance. Going through the
mirror naively costs an extra send per operation (`Integer>>+` calling
`vmmirror add: self to: other`) plus the mirror method's own dispatch.

**Proposed approach: bestowed native methods.** "Native" becomes a property
of a *method object*, not of source syntax.

1. The VM provides native implementations, identified in the kernel contract
   by name and version, not by a number in source.
2. Only a holder of the VM mirror with the right authority can install a
   native method on a class (`VMMirror.ns` already sketches this as
   `bestowPrimitive:access:named:onClass:` and `CapabilityForPrimitive`). At
   bootstrap the kernel classes receive their natives: `Integer>>+`,
   `Array>>at:`, `Closure>>value`, and so on.
3. A send that finds a native method runs it directly without building a frame,
   exactly as a primitive send does today. The cost is identical to psoup's
   primitives; the difference is that no source text can create one.
4. On top of that, the interpreter (and later a JIT) may inline fast paths
   for the commonest cases (SmallInteger arithmetic, array indexing) as
   **guarded** optimizations: valid only while the method that would be
   found is still the bestowed native. A reflective commit that replaces such
   a method invalidates the guard. These are invisible to the capability
   model.
5. Individual capabilities (`CapabilityForPrimitive`) cost nothing at run
   time once bestowed; attenuation happens at installation, not per call.

**Should this be deferred?** The detailed design can wait, but one decision
cannot: the method-object format must carry a native-method identity, and the
kernel's operation list must be the list of natives. That shapes sections 3
and 7, so it should be settled before the kernel's operation list is written
in detail.

## 9. Resource exhaustion

Out of memory, stack depth, nesting depth and handle limits must each raise a
defined exception or end the VM in a defined way, never corrupt state. The
2026-11-09 triage found silent corruption at three such limits (mark stack,
handle table, V8 stack).

## 10. Open questions

1. Does a bestowed native method keep a fallback Newspeak body? *Proposal
   (2026-11-09):* no. Failure goes through a failure role, and mixed-kind
   arithmetic is a defined tail send (section 3).
2. ~~Snapshots: idle actors only, or paused stacks too?~~ Paused stacks too
   (decided 2026-11-09). Still open: wrappers around aliens (section 6).
3. ~~Upstream V5 exactly, or our own versioned V5?~~ Our own versioned V5,
   refined as needed (decided 2026-11-09).
4. Deterministic GC scheduling, or recorded weak-clearing events? *Leaning
   (2026-11-09, to be finalized):* log weak clearing. Deterministic
   scheduling is too restrictive. On replay the collector must not clear
   weak references on its own; it applies the logged clearings at the logged
   points, where the objects are unreachable by construction.
5. The nested-callback rule (4.3): forbid draining other turns, or model it
   as permitted? *Decided 2026-11-09:* forbid it, and extend the semantics so
   a nested callback is a sub-step of the current turn. Expats are called
   synchronously only by their owner's turn (4.3).
6. ~~How fine-grained the initial capabilities are~~ An all-or-nothing VM
   mirror is acceptable to start (decided 2026-11-09). (Today `vmmirror` on the JS
   platform is all-or-nothing).

## 11. Proposed next steps

1. Agree on sections 2, 3 and 8 (the layering, operation categories, natives).
   *2026-11-10:* sections 2, 3 and 8 agreed (section 3 after review with a
   colleague who has implemented replay in Wasmtime).
2. Write the kernel operation list: today's 161 psoup primitives, classified,
   with duplicates and host-specific ones separated out (done:
   `VM_KERNEL_PRIMITIVE_CLASSIFICATION_2026-11-09.md`). Host-specific
   operations become FFI calls, not kernel operations.
3. Add the kernel as a new layer of the formal semantics (a refinement of
   `VM-Primitive`), with Lean/Prolog/SpecTec counterparts as the oracle.
4. Start the new VM against that list, V5 only.
