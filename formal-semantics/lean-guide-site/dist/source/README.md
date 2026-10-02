# Newspeak semantics in Lean

This directory is the machine-checked companion to `../newspeak-semantics.tex`.
It is not a second, simplified language definition.  The development proceeds
in vertical slices, and each slice must preserve the identities, access rules,
reflection boundaries, actors, debugger state, and optional GC observations of
the complete semantics.

The first slice formalizes the identity domains, method access, the separation
of static program `P` from heap `H`, runtime class records, finite superclass
chains, and unrestricted/public/protected lookup.  It proves uniqueness of
class-chain witnesses, determinism of all three lookup modes, equivalence of
their executable and named-rule presentations, and the static `bind = scan`
result for implicit class binding.

The runtime bridge now also gives every mixin identity an object representation
in `Heap` while retaining its definition in `Program`.  It formalizes nearest
class application, lexical depth, ordinary dispatch, super dispatch (including
the explicit `Object`/`Top` errors), and deterministic DNU target selection.

The class-scope implicit-send slice now includes the special depth-one
enclosing-object rule, deeper nearest-application traversal, lexical private
selection, virtual protected lookup, outer/self dispatch, and a full dynamic
equivalence theorem between the elaborated and ECOOP-style presentations.

The dispatch loop is now closed through all four branches of annotated
implicit dispatch and the five request kinds.  Failed resolution performs one
unrestricted DNU selection, allocates a fresh mirror containing the original
message, and passes that mirror as the sole argument to
`doesNotUnderstand:`.  Explicit mirror supplies make allocation and complete
request resolution deterministic, and freshness preservation is proved.

The sequential layer now has its first annotated-core expressions, send
frames, control terms, and snoc-shaped activation stack.  Method invocation
allocates complete activation records with parameter and local environments,
runtime current receiver/class, continuation, home-method identity, and
lexical scope maps.  The tail and non-tail invocation rules are deterministic
and preserve all five explicit allocation supplies.

Receiver evaluation and argument evaluation now follow the specified order:
ordinary receivers are evaluated first, while implicit/self/outer/super sends
construct their request immediately, and every argument is accumulated from
left to right.  Completed request processing is installed as either invocation
control or an explicit invalid-super runtime error.  The current union of
expression-order, request-completion, and invocation steps is deterministic.

Local initialization now distinguishes immutable, initialized mutable,
uninitialized mutable, lazy immutable, lazy mutable, and simultaneous groups.
Simultaneous groups formally install all futures or `nil` values before their
source-ordered resolutions.  Direct local operations, statement sequencing,
method-versus-closure body results, and ordinary activation completion by
resume or halt are part of the deterministic sequential-step relation.

Explicit return now distinguishes method targets from a closure's captured
home method.  The least set of continuation-dependent activations is defined
inductively; transfer clears every member's continuation and continuability
flag before resuming.  A stale, repeated, or otherwise uncontinuable return
produces `cannotReturn` without discarding the failure-point frames.

Closures are now represented as allocated runtime objects.  Creation
materializes the installed closure body and local declarations while capturing
the defining activation, receiver, current class, and effective home method.
`value`, `value:`, and higher-arity value sends take a dedicated dispatch path
proved disjoint from ordinary lookup.  Tail and non-tail invocation allocate
lexically linked activations with the appropriate inherited or caller
continuation, and the resulting enlarged sequential relation remains
deterministic.

The machine now also carries an explicit `SequentialWellFormed` predicate.
Besides the static program/heap conditions, it tracks the five fresh
allocation supplies, every activation named by the stack, and the defining
class carried by pending invocation control.  A checked preservation theorem
covers every currently encoded step, including DNU allocation, method and
closure allocation, local mutation, ordinary completion, and non-local-return
marking.

Atomic values, physical instance slots, and lazy-slot access are now in the
same sequential relation.  Atomic payloads exclude characters and are proved
canonical.  Direct/current slot reads and writes bypass dispatch as required;
lazy reads distinguish cached non-`nil` values from initializer evaluation,
and every new rule preserves sequential well-formedness.

Normalized class bodies and mixin applications now evaluate their superclass
before allocation, validate instantiability and factory selectors, enforce the
top-level implicit-`Object` restriction, and allocate a fresh class/metaclass
pair.  The relation is deterministic, applied classes reuse the source
instance mixin, and object and class identities have independent monotone
supplies.  The instance-allocation foundation derives a unique root-to-leaf
physical layout from the runtime class chain, initializes exactly those slots
to `nil`, and begins with an empty receiver-local nested-class cache.  Deferred
initializer messages evaluate their arguments left-to-right.  `Factory-New`
now allocates the instance together with a fresh, explicitly distinguished
initializer activation, installs its receiver/class/continuation/home scope,
and is deterministic and well-formedness preserving.  The superclass/mixin
coordinator evaluates superclass arguments before recursively initializing the
superclass, then runs the body mixin or allocates a distinct applied-mixin
initializer activation with the application as current class.  Sequential and
simultaneous slot groups are also executable; the latter install every
`PastFuture` before any source-ordered `resolve` send.  The union of all three
instance-initialization phases is deterministic and preserves the sequential
invariant.  Those phases are pairwise disjoint and are disjoint from every
preceding sequential rule, so the single enlarged sequential relation through
complete instance initialization is likewise deterministic and
well-formedness preserving.

Object literals now distinguish top-level activation provenance from ordinary
method, closure, and initializer activations.  Evaluation fixes the enclosing
object before evaluating the superclass, allocates the implicit class and
metaclass, and enters the existing factory machinery through an ordinary
nullary send.  Synthesized nested-class getters use a receiver-local cache:
class bodies are evaluated with the receiver forced as enclosing object,
mixin applications retain their source class's enclosing object, and only a
successful class value is stored.  The sequential union through both features
is deterministic and preserves the full sequential invariant.

The synthetic primary-factory body is now representable as genuinely static
core syntax: `newInstanceCurrent` carries a selector and formal-parameter
identities, and the runtime rule reads their object values from the current
factory activation.  For object literals, a checked lookup theorem connects
the fresh class object to its public nullary factory method, while a separate
Factory-New theorem identifies the exact fresh object installed with the
computed nil-initialized layout.  A finite-execution theorem now composes the
entire successful path from Object-Commit through ordinary factory dispatch,
method entry, body execution, and Factory-New, proving freshness and the exact
installed instance record.

The exception-library boundary is explicit as well.  A checked platform
reifier may allocate a near exception and immutable diagnostics but must retain
all old heap records, preserve heap coherence and fresh supplies, and provide
an ordinary public `signal` method.  Both internal failure controls dispatch
that same nullary send while retaining the exact activation and evaluation
stacks, leaving handling and resumption to ordinary library/debugger behavior.

Top-level entry now has its specified representation rather than a sentinel
encoding.  Activation and closure context fields admit absent current class
and home method; `newTop` installs exactly those absent values, and Top-Halt
makes the top activation uncontinuable before producing the terminal value.
The top-level expression judgment excludes implicit, self, outer, and super
sends by construction, but recursively admits tuples of top-level
expressions.  Tuple evaluation uses the fixed `ReadOnlyTuple` and `Array`
bindings and the specified synthetic cascade closure, including source-ordered
`at:put:` sends and final `yourself`.  Pattern nodes cover wildcard, literal,
nested, variable, and keyword forms and expand only to ordinary tuple and
`Pattern` library expressions.  The integrated sequential relation through
compound literals and top-level termination is deterministic and preserves
the complete sequential invariant.

Every top-level runtime identity store now has an exact finite executable
domain while retaining the prior lookup syntax.  The resulting
`allInstancesOf` operation enumerates instances across all seven Newspeak
object categories, and `allApplicationsOf` enumerates every runtime class
application of a mixin, including metaclasses.  Their checked membership
theorems are exact and both result lists are duplicate-free; this is the
enumeration foundation needed by reflection and optional garbage collection.

The same finite-store representation now reaches inside runtime records:
ordinary-object slots and nested-class caches, and activation parameters,
locals, activation scopes, and object-literal scopes all expose exact domains.
Partial static program dictionaries and mixin method dictionaries are finite
too.  Checked domain theorems relate these stores to instance layouts,
parameter/argument pairing, declared locals, and lexical-scope extension, so
later reflection and GC need not infer any finite set from a function space.

The unconditional GC graph is now encoded independently of weak containers.
Every runtime record has an executable structural reference extractor,
including closure materialized code and message-mirror arguments, and direct
successors are intersected with the current live-object domain.  Exact
membership, liveness, and duplicate-freedom theorems cover direct successors
and each finite reachability iteration.  The live-record-count bound is now
proved extensionally stable and equivalent to the inductive
reflexive-transitive strong-reachability relation.  It is also proved to be the
least root-containing set closed under strong edges.  WeakArray and WeakMap
conditional edges can now be added as a separate overlay.

That overlay now has its storage boundary.  An ordinary object may carry one
optional `WeakArray` or `WeakMap` payload while its fixed instance slots remain
strong.  Distinctly named VM reads and writes have checked success and
read-after-write theorems.  A separate heap-wide validity predicate requires
all weak observations to resolve before collection and is preserved by writes
of live identities.  Most importantly, changing a weak payload is proved not
to change the object's unconditional strong-reference list.  Conditional map
reachability is now executable as a monotone finite iteration.  A map value is
enabled only when both the map and its key are in the current approximation;
the iteration is proved to stabilize at the live-record-count bound, coincide
with an inductive strong/ephemeron closure, and be its least fixed point.
Collection now performs one atomic transformation after that fixed point:
every top-level heap store is restricted to reachable identities, dead
WeakArray cells become `nil` without changing array length, and WeakMap entries
survive exactly when both key and value survive.  The collected heap's live
domain is exactly the conditional closure, and every retained weak observation
is proved to resolve in that heap.  Global well-formedness preservation and
the stuttering-refinement layer are now checked as well.  An executable root
extractor traverses finite Program tables, platform objects, suspended syntax,
all evaluation and activation frames, current control, installed actors, and
caller-supplied host handles.  Its conservative retention of installed classes
and actors discharges the former class/stack adequacy premises while leaving
class reclamation as a separate policy refinement.  Finite collecting
executions are classified step-for-step as exact base transitions or
strong-observation stutters, with roots recomputed at each source state.

The actor lift now covers the complete sequential machine.  Promise,
far-reference, event, VM, and pause-token identities are distinct.  A finite
actor world records private heaps, the shared value heap, running/paused/idle
turns, FIFO mailboxes, network packets, promise and far-reference tables,
causal histories, the permanent event ledger, delivered order, and monotone
supplies.  Remote representation has checked same-actor, value-transfer,
far-home, far-pass, promise, and near-to-far cases.  Returning a far reference
home provably recovers the near referent, while third-party passage preserves
its identity.  Packet emission and acceptance record causal order, and
settlement commits a terminal promise state before emitting ordered wakes.
Wake packets name both the originating promise and the dependent result
promise.  The temporal safety layer proves terminal states persist through
all actor-system transitions, promises settle at most once along an execution,
and every waiter notification is emitted only after the originating terminal
commit.
The root layer above this world retains heap locations explicitly and projects
duplicate-free roots for either a particular actor heap or the shared value
heap.  Eventual target selection and all four routing cases are represented;
asynchronous evaluation allocates the canonical next promise before routing.
FIFO application dequeue starts only an idle actor. Source eventual sends are
evaluated receiver-first and arguments left-to-right, intercepted before the
ordinary dispatcher, and return a newly allocated promise handle. Normal and
exceptional turns settle reply promises; settlement and wake packets are
dequeued in FIFO/E-order. All selected phases are pairwise disjoint and
deterministic, while `ActorAction` isolates global scheduler nondeterminism and
states weak fairness explicitly. Actor creation from a static seed allocates a
fresh private base, class/metaclass pair, idle run state, and far reference.

The reflection layer now has typed mirror targets and rights, authority-bearing
mirror records, structural containment, an explicit seven-way command
partition, complete write footprints, and transaction conflict detection.
Its read side is executable too: one exhaustive query sum covers inspection of
VM, program, mixin, method, class, object, activation, and actor state, plus
authorized instance and mixin-application enumeration across the cohort. Every
successful reflected read requires the mirror's `inspect` right just as every
change requires its command-family right.
Runtime class-graph, object-class, layout, nested-cache, slot, and activation
updates are executable and distinctly named. Layout migration preserves old
physical-slot values, initializes new slots to `nil`, and removes obsolete
slots. Continuation transfer can pop to any live continuable activation while
retiring discarded frames. Debugger stack images distinguish retained and
fresh frame keys, substitute all activation-valued links, require suspended
lower frames and exactly one active top frame, and install atomically. Pause
tokens guard cross-actor stack editing; replacement invalidates the token, and
full-speed resumption returns the actor to the ordinary sequential relation.
Finally, the transaction shell sequences source patching, complete
re-elaboration, runtime preparation, five explicit validation families, and a
single atomic commit. Checked laws show that a successful commit advances the
cohort version exactly once and rejection leaves every component unchanged.
The concrete identified-source front end implements each code-command patch,
rejects missing or conflicting method identities/selectors, checks its
bidirectional method indexes, and reconstructs the installed mixin, method
body, and method-local projections before the atomic runtime phase begins.
The first M6 layer now gives finite stores an explicit pointwise equivalence,
proves commuting installs and erasures, and lifts adjacent commutation to every
permutation of a pairwise-independent partial-command sequence, including
failure preservation.  Concrete checked instances cover distinct method-body
and full-definition replacements, removals, extensionally equal fresh adds,
and all slot, nested-class, and mixin-initializer replacements; the latter
commute even on one mixin when they update different fields.  The
static footprint conservatively treats a mixin's method dictionary as one
location because replacement and removal inspect the old selector.
The same checked algebra now covers superclass/enclosing-object edits,
object reclassification, validated reflective object-slot writes, and all
ordinary activation-record fields through a common edit algebra.
Continuation-dependent retirement, stack replacement, and continuation
transfer conservatively claim a global activation-graph footprint, since the
set of records they mutate is state-dependent.  Consequently a nonconflicting
transaction has at most one continuation transfer, so that whole phase is
permutation invariant.  Debugger footprints separately expose the global
pause-token supply; the checked compatible-pair classification and concrete
equations cover every permitted distinct-actor debugger pairing, including
all failure paths. Static nonconflict now derives the complete debugger
transaction certificate rather than requiring it as an assumption.
The permutation layer now has both exact and observational forms.  The latter
uses `OptionalResultsRelated` to preserve failures while quotienting away
finite-store domain order, and it lifts source-command diamonds through the
whole source fold.  All seven source command forms are proved extensional, so
that lift now needs only pairwise source diamonds. A program-level lookup
equivalence covers every semantic projection. Source consistency compares
finite-store supports rather than enumeration order, so equivalent identified
sources re-elaborate with the same success or failure and produce equivalent
installed programs. Program equivalence is proved observational for class-chain
and layout computation, cache reconciliation, reflective slot writes, and the
complete runtime preparation. The four mutable cohort
folds and continuation transfer now each have explicit permutation theorems;
the debugger fold uses actor/allocation-domain coherence as its invariant.
Every pre-debugger cohort edit and both reconciliation passes preserve that
invariant, so coherence of the initial actor world now derives coherence at
the debugger boundary rather than being supplied as a separate certificate.
Those results are composed into a checked theorem for the complete ordered
runtime preparation pipeline, including both layout/cache reconciliation
passes. One concrete runtime-certificate record now discharges the complete
compiler/runtime extensionality boundary. All of its phase-commutation fields
now derive from static nonconflict; callers supply only nonconflict, the
permutation, and initial-world coherence. The corresponding source audit also
corrected `addMethodDefinition`'s footprint to include the method body that it
installs, preventing a false independence classification against body
replacement. The exhaustive seven-by-seven source-edit matrix is now checked, including
all method-definition add/replace/remove combinations with slot, nested-class,
and initializer edits. Fresh insertion order is quotiented only by lookup
equivalence. Static nonconflict therefore derives the source certificate as
well as every runtime certificate, and the final theorem composes arbitrary
transaction permutations through source patching, re-elaboration, runtime
preparation, and atomic installation.
The outer-shell theorem then composes source patching, re-elaboration, runtime
preparation, and atomic program/version installation.  Its result relation
keeps all runtime state exact and quotients only the executable-domain order
inside equivalent source images and installed programs.
The Simulator refinement boundary is now explicit without freezing Newspeak's
replaceable bytecode format: each observed frame carries its activation,
operand stack, code address, and PC; a decoder relates every lower PC to
suspended control and the top PC to the exact current semantic term.  A
compiler/Simulator certificate must prove instruction soundness, semantic-step
completeness, and exact extraction of that represented configuration for
full-speed native resumption.  The checked finite-execution theorem composes
instruction soundness across arbitrary Simulator runs.
`V5Bytecode` is the first concrete artifact instance: it decodes every live
opcode in the local V5 instruction-set specification, rejects dead, corrupt,
and truncated encodings, and proves decoding deterministic and extended-send
operands bounded.  A V5 method artifact also carries the compiler-emitted
semantic PC map; its well-formedness contract proves that this map contains
exactly the in-range instruction boundaries, so debugger control recovery is
not incorrectly inferred from opcodes alone.

The source front end now begins at the PEG rather than at a presumed AST.  The
full PEG core is relational and functional, grammar admissibility has explicit
defined-reference, leading-cycle, and advancing-repetition clauses, and the
normalized 0.109 Newspeak production table is executable.  Captured concrete
trees are projected by typed semantic actions into the complete surface
syntax domain, with punctuation erased and metadata accumulated separately.
Structural source-node paths feed stable declaration/site identification;
successful identification is proved injective, sort-correct, deterministic,
and preserving every retained identity.  Binding, receiver authority, send
selection, expressions, patterns, clauses, and statements have finite-fuel
elaboration functions, while an independent core checker validates installed
declaration annotations.  `FrontEndDerivation` composes those stages with
surface validation, atomic Program derivation, and the top-level restriction
and proves the complete accepted result unique.  Declaration-to-Program
construction now installs finite images for direct named classes, primary
factories, eager and lazy slots, explicit and synthesized methods, closures,
compound-literal descriptors, recursively nested classes, object-literal
bodies, actor seeds, and mixin-application folds with and without an explicit
body. The same construction is used recursively for nested and
expression-local classes. In particular,
the surface AST now retains both the source class and initializer at every
`<:` step; an earlier initializer-only representation was insufficient to
implement the specified fold. A structural pass discovers object literals and
class expressions in every embedded surface form. The complete static gate
checks selector arity, binder and induced-selector uniqueness, derivation
success, declaration–mixin injectivity, annotations throughout every installed
method, closure, initializer, pattern expansion, and deferred message, and the
top-level restriction against the derived Program. Finally, an executable finite
certificate proves the distinguished grammar admissible: character predicates
are normalized only for this structural analysis, and normalization is proved
to preserve reference, nullability, leading-edge, and repetition checks.

The metacircular boundary now treats the parser, elaborator, compiler, and
Simulator as four live ordinary Newspeak objects; it adds no special semantic
transition for replacing them. Artifacts obtained from those objects are
admitted at use boundaries. Parser admission requires a well-formed PEG,
elaborator admission requires checked output to satisfy `AnnotatedCoreValid`,
and compiler/Simulator admission requires the bidirectional simulation and
exact full-speed-resumption certificate. A compiled-program admission ties a
specific checked core expression to its top-level semantic entry and initial
Simulator state, from which finite compiled-execution refinement follows.
The V5 specialization fixes only decoding and PC-map obligations, not a
reflectively replaceable compiler or Simulator implementation.

## Design rules

1. Distinct semantic identities have distinct Lean types.
2. Cheap shape invariants belong in structures; mutable semantic invariants
   belong in explicit `WellFormed` predicates.
3. Deterministic operations have executable functions plus relational graphs.
4. Genuine scheduling, reflection, and GC nondeterminism remains relational.
5. Fresh allocation uses explicit supplies, so sequential determinism is
   literal equality rather than equality only up to renaming.
6. No unproved theorem is exported from `Newspeak.Properties`.
7. `THEOREMS.md` records the complete obligation even before its layer exists.

## Build

With `elan` installed, run:

```sh
~/.elan/bin/lake build
```

The `lean-toolchain` file pins Lean 4.34.1, the version used for the first
checked build.
