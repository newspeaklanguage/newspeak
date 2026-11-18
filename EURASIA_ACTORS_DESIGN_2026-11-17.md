# Eurasia actors: the rest of M4

**Date:** 2026-11-17
**Status:** Decided 2026-11-17 (section 5); sections 2.3 and 2.4 are
superseded where section 5 says so. Implementation under way.
**Context:** `NEW_VM_IMPLEMENTATION_PLAN_2026-11-17.md` (M4),
`VM_KERNEL_OPERATIONS_2026-11-10.md` section 7,
`formal-semantics/actor-semantics.tex`.

## 1. Where M4 stands

Eurasia runs psoup's actors module unchanged. Images run psoup's message
loop: eventual sends, promises, timers and `Actor named:` all work, and
psoup's `ActorsTesting` gives the same outcomes on both VMs.

All of that is psoup's model, which is not the semantics':

- **psoup:** `Actor named:` actors are library objects in **one shared
  heap**. The library keeps one FIFO of eventual sends per actor and drains
  them all from one VM stack (`MessageLoop>>drainQueue`). A far reference is
  a library object pointing directly at its target; isolation holds because
  the library only ever eventual-sends through it. Real isolation is a
  separate VM (an *isolate*): `rawSpawn:` starts one from the same program
  with a byte message, and ports carry bytes between isolates, serialized in
  Newspeak.
- **The semantics and the operation list (decided):** each actor has a
  **private heap**, and all actors of a cohort share one program and,
  optionally, a value heap. `vm spawn: mixin` creates an actor in the same
  cohort, applies the mixin in a fresh base heap, and answers a far
  reference to the new class. References cross actors only by the
  remote-representation rules (RR-Same, RR-Value, RR-Near-Far, RR-Far-Home,
  RR-Far-Pass, RR-Promise). An actor can be paused alone (`pausedTurn`),
  which is what the debugger (M6) builds on. Starting another cohort is a
  host start from a snapshot, not `spawn:`; ports remain for talking to
  other cohorts.

What psoup's model cannot give, and M6 and M7 need:

1. **Pausing one actor.** With every library actor on one VM stack,
   pausing one pauses all.
2. **Per-actor heaps** for per-actor snapshots, replay logs and statistics.
3. **Isolation by construction** rather than by library discipline.
4. **Parallelism** later (one cohort per worker or thread).

## 2. Proposal

### 2.1 VM actors, one arena

A Eurasia actor is a VM-level execution context: its own operand stack and
frames, its own mailbox, its turn state (idle, running, paused) and its own
heap. The heaps stay in the one arena: every object already records its
space (`Space::Actor(n)`), so an actor's heap is the objects tagged with its
number. The program space (frozen methods, mixins) is shared, as is a value
heap of canonical strings and numbers.

The VM guarantees that **no reference into actor B's heap is ever held by
actor A's stack or heap**, except inside a far-reference record (the
semantics' table Φ). Every path that moves a reference between actors goes
through one VM function implementing the RR rules, so isolation holds by
construction, not by library discipline.

One arena keeps the collector, snapshots and identity hashes as they are
(a collection is global; allocation sequence numbers stay unique across the
cohort). Separate arenas would only be needed for actors running in
parallel, which the operation list already treats as separate cohorts (open
question 1 there).

### 2.2 Turns and scheduling

The VM, not the library, owns the mailboxes and runs turns: it picks an
actor with a nonempty mailbox, installs that actor's stack, and delivers one
packet through the dispatch role. A turn ends with `finish:`. Scheduling is
round robin, which is deterministic given the inputs, as replay needs.
Timers stay per actor in the library and become wakeups the VM merges.

### 2.3 Far references and promises

Two options:

- **(a) In the VM, as in the semantics:** promises and far references are
  VM records (Π, Φ), and `asyncSend` routing (Route-Target, Route-Pending,
  Route-Fulfilled, Route-Broken) is VM code. The library's
  `InternalFarReference` and `InternalRemotePromise` become thin wrappers.
- **(b) In the library, as in psoup, over a small VM interface:** the
  library keeps its promise machinery. The VM adds one operation, *post a
  message to actor B*, which applies the RR rules to the arguments and
  queues the message, and the far-reference record (Φ) as a VM object kind
  whose target only its home actor can dereference.

**Recommendation: (b).** It reuses the library that already passes the
actor suites. It keeps the VM small (design doc: policy in Newspeak), and
confines the VM's new duties to the two things only it can guarantee:
isolation (RR on every crossing) and scheduling (pausable per-actor stacks).
The semantics' Π stays in the library, but for observation it is equivalent,
since promises cross actors only as RR-Promise.

### 2.4 `spawn:`

`vm spawn: mixin` creates actor B with an empty heap and its own stack. It
applies the instance mixin (whose class-side mixin is now a contract field)
to the platform's `Object` in B's heap, and answers a far reference to the
new class. The new class's enclosing object is nil, as for any top-level
class. The new actor's *platform* is the open part:

- **The base heap** (`base_P(B)`: "the distinguished classes and canonical
  values but no user-created mutable object") is, in Eurasia's terms, the
  roles and what they reach that is immutable. The kernel's classes are
  shared program objects; but the platform objects that genesis built (the
  public kernel module, collections, actors and the message loop) are
  mutable instances in the genesis actor's heap. B needs its own.

Proposed: each actor gets its own platform, built when it is spawned by the
same Newspeak code genesis runs (`platformOver:`), running as B's first
turn. Spawning therefore costs one platform construction, about what
genesis does.

### 2.5 Ports

For talking to other cohorts and to the host: as in psoup, ports carry byte
arrays, and messages are serialized in Newspeak. That needs psoup's
serializer (`PrimordialFuel.ns`), whose primitives go in the natives table
like the actors module's. This is independent of 2.1–2.4 and is needed for
the web host (M5) more than for anything in M4.

## 3. Order of work

1. VM actors with their own stacks and mailboxes in one arena; the dispatch
   loop schedules them; `Actor named:` creates one (library change: an
   InternalActor gets a VM actor).
2. The cross-actor post operation with the RR rules, and the far-reference
   object kind. The library's far references use them.
3. `vm spawn: mixin`, with a per-actor platform built in the actor's first
   turn.
4. Tests: `ActorsTesting` must still agree with psoup, plus new Eurasia
   tests for isolation (a reference never leaks), per-actor GC roots,
   `spawn:`, and pausing one actor (a stub until M6).
5. Ports and the serializer (with M5).

Steps 1–3 change psoup's actors module, so it becomes a fork, like the
kernel (a script that derives `EurasiaActors.ns` with every change checked).

## 4. Questions

1. **Option (b) for far references and promises** (library over a small VM
   interface) rather than (a) (VM tables, as the semantics writes them)?
2. **One arena** with per-actor ownership tags, and actors in parallel only
   as separate cohorts?
3. **A per-actor platform built in the new actor's first turn** for
   `spawn:`'s base heap?
4. **Do `Actor named:` actors become VM actors?** Proposed yes, so that
   every actor is pausable and isolated. The alternative keeps them as
   library actors inside one VM actor (psoup's model) and makes only
   `spawn:` create VM actors.

## 5. Decisions (2026-11-17)

1. **Actors are lightweight VM actors.** Their heaps are logically separate
   and physically shared: one arena, ownership by space tag. The program
   (methods, mixins) is shared, as are values. `Actor named:` actors are VM
   actors too.
2. **The platform is per actor, cloned from a template.** The platform may
   be stateful, so every actor has its own. Genesis builds the initial
   platform; the VM keeps it as a template (a role) and clones it when an
   actor is created. Cloning copies only the template's mutable objects;
   program objects and values stay shared. (Supersedes 2.4's platform built
   in the new actor's first turn.)
3. **Promises and far references stay in the library (option (b)),** over a
   small VM interface: posting a message to another actor with the
   remote-representation rules applied, and an opaque far-reference object.
   Each actor's library state lives in its own platform clone.
4. **Values carry a bit.** The language spec's `Value` class is the
   superclass of all values; values are deeply immutable. Strings, numbers,
   nil and the booleans have the bit, and so does a class whose enclosing
   object is a value. Crossing actors, a value passes as itself (one bit
   test); anything else becomes a far reference.
5. **Until the spec changes, applying a mixin on Value does the checks.**
   Superclasses are computed at run time, so the compiler cannot know a value
   class. `vm applyMixin:superclass:enclosingObject:` checks, when `Value` is
   in the new class's chain, that the enclosing object is a value and that no
   mixin in the chain has a mutable slot (a public setter besides the private
   `init` one), and marks the class a value class. Its instances get the bit
   at allocation, and every store through an `init` setter must store a value
   or an immediate. **Known gap:** the end of construction is not marked, so
   an initializer that hands out `self` before it finishes can expose a
   partly built value.
6. **Proposed spec change (Gilad):** a class declares itself a value class
   syntactically. The compiler can then mark the end of construction (freeze
   the instance and set its bit) and reject mutable slots, closing the gap
   in 5.

## 6. Progress

**2026-11-17: values.** Done and checked by `eurasia/scripts/genesis.sh`:
the kernel fork's `Value` class (role 34, and an `_Object` accessor so any
code can name it), the value bit (snapshot format version 3), and the rules
of section 5.5 in `vm applyMixin:superclass:enclosingObject:`, `basicNew`,
slot setters (which now also refuse frozen receivers) and `vm slotOf:at:put:`
(which refuses values). `vm isValue:` answers the bit. The mutable-slot rule
exempts nested-class cache setters (`` X`slot: ``): they memoize a class,
which is a value when its enclosing object, the instance being checked, is
one. A top-level module may name a kernel class as its superclass
(`EurasiaValueProbe new = Value new`), which makes it a value module.
Classes the genesis packager builds are marked by the packager (a class whose
chain includes Value is a value class; one with a nil enclosing object is a
value) and are not checked, being trusted.

Next: VM actors (section 3, step 1).
