# Formalization design

## Authority

The LaTeX semantics remains the readable normative presentation while this
development is incomplete.  Every Lean definition records the corresponding
LaTeX equation or named-rule family in its documentation.  When a vertical
slice is complete, the Lean statement and proof become the conformance test
for later edits to that slice; disagreement must be resolved explicitly in
both artifacts.

This is a formalization of the complete language, not a calculational subset.
Omitting a layer temporarily is represented by an unchecked entry in
`THEOREMS.md`, never by silently weakening a theorem.

## Representation policy

Semantic identities use distinct wrapper types over natural numbers.  Static
mixins and lexical maps live in `Program` (`P`); applied runtime class records
and superclass links live in `Heap` (`H`).  Values
and heap records will refer to those identities rather than recursively
containing runtime objects.  The eventual machine state will carry a separate
monotone supply for each allocatable identity domain.  Canonical allocation
then makes sequential determinism an equality theorem; it does not require a
quotient by permutations of freshly chosen names.

`FiniteStore` is an extensional partial-map lookup paired with an exact,
duplicate-free executable domain.  The seven top-level heap stores, ordinary
object slots and nested-class caches, and all four activation environments use
this representation.  The partial static dictionaries in `Program` and each
mixin's method dictionary do likewise; total syntax projections whose domain
comes from those dictionaries remain ordinary functions.  The representation
preserves function-call lookup notation while making every partial-store
domain explicit.  Domain theorems connect instance allocation to its physical
layout and activation construction to paired parameters, declared locals, and
lexical scopes.

`liveObjectReferences` covers every tagged object category;
`allInstancesOf` filters it by runtime class, and `allApplicationsOf` filters
the finite class domain by applied mixin.  Checked membership theorems show
that neither query omits nor invents a result, and both results are
duplicate-free.  These finite domains now also support the forthcoming exact
reference-edge traversal for reflection and garbage collection.

The base strong-reference graph is now executable and deliberately separate
from weak observations.  Structural extraction traverses every reference-
bearing runtime field: class, superclass, metaclass, and mixin links; instance
slots and nested-class caches; activation environments, continuations, and
lexical scopes; closure captures and materialized syntax; mirror messages; and
actor class links.  `strongSuccessors` intersects those structural references
with the current live store, matching the prose `strongSucc` operation.
Finite root and reachability iterations have exact membership theorems and
produce duplicate-free live-object lists.  The live-store cardinality bound is
proved to have stabilized extensionally: otherwise every prior iteration
would strictly increase the duplicate-free reached list beyond the number of
live records.  An inductive `StronglyReachable` relation supplies the
reflexive-transitive presentation, and the executable result is proved
equivalent to it, closed under strong edges, and contained in every other set
with the same roots and closure property.  Weak-array and ephemeron-map
contributions can therefore be layered on without changing this unconditional
least fixed point.

Weak storage is represented as an optional payload of an ordinary object, not
as a new object-identity category: its class, slots, and reflective identity
therefore retain the ordinary semantics.  A payload is either a finite indexed
weak array or a finite weak-key map with ephemeron values.  Fixed instance
slots and nested-class caches remain unconditionally strong, and the checked
strong-reference extractor is definitionally independent of the weak payload.
The four VM primitives have distinct names and executable failure behavior.
`WeakContainersWellFormed` is intentionally separate from global program/heap
coherence so a collector can compute dead observations and clear them in one
atomic transition; valid writes of live references preserve that predicate.

Conditional reachability begins from the same finite live-root set and closes
simultaneously under unconditional strong edges and the WeakMap ephemeron
rule.  That rule has two reachability premises: the map and key must both be in
the current approximation before the stored live value becomes an edge.  The
executable iteration is monotone, duplicate-free, and confined to the finite
live domain.  Hence it stabilizes by the live-record-count bound; its result is
proved equivalent to the corresponding inductive relation and least among all
sets containing live roots and closed under both rules.  The unconditional
strong result is a proved subset of this conditional result.

The collection function consumes that fixed point in one atomic heap update.
All seven top-level stores are restricted to their tagged reachable
identities.  Retained ordinary-object records preserve their class, fixed
slots, and nested-class cache while transforming only weak payloads:
WeakArrays retain their length and replace each dead element with the supplied
canonical `nil`; WeakMaps retain exactly entries whose key and value are both
in the fixed point.  The resulting live-object domain is proved equal to the
conditional closure, and—assuming `nil` is a live root—every weak reference in
the resulting heap resolves there.  Its lift to allocation states preserves
the five monotone identity frontiers literally and
therefore preserves their freshness invariant despite removing store entries.
It also leaves the activation stack and current control term definitionally
unchanged.  The root oracle has now been replaced by executable traversal of
finite Program stores, installed bodies and descriptors, platform bindings,
canonical atoms mentioned by suspended syntax, activation/evaluation stacks,
current control, installed actor records, and explicit host handles.  Total
syntax maps are sampled only at their corresponding finite installed domains.
The conservative policy roots all installed class and actor records; this
proves full sequential well-formedness without making a premature claim about
class or actor reclamation.

The collecting step relation is the ordinary complete sequential relation
plus an optional atomic collection step.  `CollectionStutter` requires literal
agreement of stack, control, and allocation frontiers, and agreement of class
and unconditional structural-reference observations for every retained
identity.  Weak reads are excluded precisely so clearing and removal remain
observable as specified.  The finite erasure theorem classifies every enlarged
execution step as either the exact base step or such a stutter, recomputing
roots at each source state.

The actor layer represents near references separately from global promise and
far-reference capabilities.  Its finite world makes every mailbox, private
heap, run state, causal history, permanent event record, promise, and far
target enumerable, while distinct monotone supplies make emission and handle
allocation canonical.  Remote representation is relational because immutable
value transfer is a platform contract, but fresh far allocation itself is
executable.  The checked normalization theorems rule out proxy chains:
returning a far reference home yields its near target and passing it through a
third actor preserves the original identity.  Settlement has no constructor
for a terminal promise, commits fulfillment or breakage before ordered wake
emission, and provably cannot leave the promise pending.

Cheap, immutable shape facts belong in Lean structures.  Properties that can
be invalidated by execution or reflection belong in explicit `WellFormed`
predicates.  Runtime states will not carry their proofs as dependent fields:
each transition instead has a preservation theorem.  This keeps reflective
updates executable and their proof obligations visible.

## Operations and judgments

Deterministic semantic operations receive:

1. an executable definition;
2. a relational or syntax-directed presentation corresponding to the paper;
3. a graph-equivalence theorem; and
4. a uniqueness or determinism theorem.

The `Lookup` relation is the graph of lookup over the unique finite class
chain.  Separate inductive judgments encode U-Top/U-Here/U-Super,
Pub-Top/Pub-Hit/Pub-Protected-Barrier/Pub-Super, and
Prot-Top/Prot-Hit/Prot-Super; their graph equivalence and determinism are
proved.  Dispatch then composes those judgments through annotated implicit
receiver selection and request resolution.  DNU allocation uses an explicit
mirror supply, stores the complete original message in the heap, and has a
checked freshness-preservation theorem.

Method bodies are addressed through `Program.methodBodies` by stable method
identity.  Invocation therefore consults the currently installed body while
materialized control terms retain the body already selected by an earlier
step.  Method-activation allocation uses its own explicit supply and installs
parameter/local environments, current receiver and defining class,
continuation, home method, continuability, and the initial lexical environment.
Tail and non-tail stack effects are separate constructors of one deterministic
invocation relation.

Closure literals likewise read the currently installed declaration body only
when the closure is created.  The allocated closure record materializes that
body and its local declarations, and captures the defining activation,
receiver, current class, and effective home method.  Direct `value` dispatch
is a separate phase that is proved disjoint from ordinary method lookup.
Closure invocation allocates an activation whose lexical map extends the
defining activation's map at the closure declaration.  A non-tail invocation
suspends the caller; a tail invocation replaces it and inherits its
continuation.  Creation, dispatch, invocation, and their union are each
deterministic.

Sequential well-formedness is now explicit rather than an ambient assumption.
It combines program/heap coherence, freshness of the mirror, activation,
closure, ordinary-object, and class supplies, liveness of every activation
named by the stack, and
liveness of a pending method invocation's defining class.  Program/heap
coherence includes live distinguished runtime classes and live captured
classes for every closure.  Lookup-to-liveness lemmas connect every dispatch
mode and DNU selection to activation allocation.  Every rule in the current
sequential relation preserves this invariant, including local writes,
continuation severing, and the pointwise marking performed by non-local return.

The next sequential layer adds exact atomic payloads, physical slot identities,
direct/current/lazy slot primitives, normalized class descriptors, and fresh
class/metaclass allocation.  Descriptors remain in `Program`; evaluated class
records and their stable origins remain in `Heap`.  Instance layouts are
computed from the unique runtime class chain in root-to-leaf order, require
distinct physical slot identities, and allocation initializes exactly that
domain to `nil`.  Class-commit constructors currently carry derived
post-allocation heap-coherence evidence explicitly (freshness is proved from
the class supply); eliminating that evidence premise by deriving it solely
from static descriptor coherence is
the next preservation refactoring, not a semantic relaxation.

Deferred initializer messages have a dedicated left-to-right evaluator.  An
initializer activation is represented as a third activation provenance, not
as a closure: it is its own return/home target and introduces its initializer
declaration into the activation scope.  `Factory-New` now atomically allocates
the ordinary object and that initializer activation, starts with every physical
slot set to `nil`, preserves all five fresh supplies and heap coherence, and
has a checked deterministic extension of the preceding sequential relation.
The superclass/mixin coordinator and slot-group machines extend that relation
as deterministic, well-formedness-preserving phases.  The coordinator
recursively initializes the superclass before the current mixin and allocates
a distinct home activation for an applied mixin.  Sequential slot groups use
physical writes directly.  Simultaneous groups retain an elaboration-assigned
closure-declaration identity for each eager initializer, install every
`PastFuture` in source order, and only then issue the source-ordered `resolve`
sends through ordinary dispatch.  All three initialization phases are
pairwise disjoint and disjoint from the earlier sequential machine.  The
checked `SequentialStepWithInitialization` relation therefore provides one
deterministic, invariant-preserving step relation through completion of
instance initialization.

Object-literal and nested-class evaluation now form the next checked layer.
Top-level provenance makes the absence of a top-level enclosing object
explicit; other activations contribute their activation object.  An object
literal allocates its fresh implicit class/metaclass pair and hands execution
to the ordinary nullary factory send, reusing the already checked instance
initializer.  Nested-class caches are fields of individual ordinary-object
records, successful cache writes preserve all allocation supplies and heap
coherence, and repeated reads of one receiver/declaration pair are proved
single-valued.  `SequentialStepWithObjects` is deterministic and preserves
sequential well-formedness.

The primary-factory bridge no longer places runtime objects in static syntax.
Its internal primitive retains the selector and parameter identities and
reifies their current activation values when Factory-New executes.  Static
`ObjectLiteralFactoryImplementation` evidence records the synthesized public
method, its empty object-literal parameter list, and its installed primitive
body.  Public dispatch from the freshly allocated class object to that exact
method is checked, as is the subsequent Factory-New allocation of the precise
fresh object frontier and nil-initialized physical layout.  The finite
execution closure preserves sequential well-formedness, and
`objectLiteralCommit_allocatesFreshInstance` composes the full successful path
from Object-Commit through factory dispatch and invocation to the exact
freshly installed instance record.

`ErrorReifier` isolates the VM-only part of the exception boundary as a total
deterministic allocation operation with explicit extension, coherence,
fresh-supply, and public-`signal` obligations.  `ExceptionBoundaryStep` maps
both `runtimeError` and `throw` to the same ordinary nullary `signal` dispatch
and proves the full stack is unchanged; no handler stack or built-in catch
semantics is introduced.

Top-level entry uses optional activation/closure current-class and home fields,
so the specified nil contexts are represented as absence rather than `Top` or
an invented activation sentinel.  `TopLevelExpression`, `TopLevelEntry`, and
`TopLevelHaltStep` encode the static boundary, exact fresh activation, and
terminal transition; the enlarged sequential relation remains deterministic
and preserves well-formedness.  Its recursive tuple clause admits exactly
tuples whose elements are themselves top-level expressions; patterns remain
excluded because their `Pattern` binding is implicit.

Compound literals retain the stable syntax needed by their specified dynamic
expansions.  Empty tuples send `new:` to the fixed `ReadOnlyTuple` binding;
nonempty tuples allocate through `Array new:`, populate in source order via an
`at:put:` cascade, send `yourself`, and finally send `fromArray:`.  The cascade
is not an administrative shortcut: its core node retains a synthetic
one-argument closure descriptor and the complete clause list.  Closure
creation materializes exactly that parameter, empty local list, and
source-ordered statement body rather than rereading a possibly reflectively
replaced program body.  Thus an in-flight tuple obeys the existing
materialized-control boundary.
Wildcard, literal, nested, variable, and keyword patterns expand to ordinary
library expressions.  Keyword symbols and component patterns occupy distinct
stable tuple sites, and the underspecified variable constructor remains the
single explicit `Program.patternVariable` parameter.

The implicit-send runtime class context is correspondingly optional.  An
activation-bound parameter reference in a synthetic top-level cascade needs no
class context; class-bound implicit sends and the self fallback still have
constructors only when that option is `some D`.  This removes the need for a
fake top-level class while preserving the authority checks of ordinary class
code.

Both frame stacks use snoc-shaped inductive representations corresponding
directly to the prose notation.  Receiver and argument continuation functions
case-split executable lists, so their rules enforce receiver-first and
left-to-right argument order without a separate scheduling premise.  Request
completion consumes `missing` through DNU before installing control; hence the
machine-level result is either an invocation or an explicit runtime error.

Normalized local declarations retain their initialization mode in the core.
Installed method-local declarations and statement bodies are read through
stable method identities, while invocation materializes the selected versions
in control.  Simultaneous initialization is an executable two-phase list:
every future or `nil` installation precedes the source-ordered resolve sends.
Normal completion severs the completed activation's continuation and either
resumes its saved activation or produces a terminal value.

Explicit return uses an inductive least dependent-activation predicate over
continuation links.  The activation store is finite, and marking maps over its
exact domain.  The operation remains declared noncomputable because membership
in that inductively defined propositional dependency relation currently uses
classical decision, not because the heap lacks an executable domain.  Transfer
marks the entire dependent set uncontinuable before resumption, while failure
retains the current frames for resumable `cannotReturn` handling.

Genuine choice remains relational.  Actor selection, permitted message
delivery interleavings, reflection initiated in different VMs, and GC timing
will therefore not be forced into deterministic functions.

## Layering

The dependency direction is:

```text
identities and syntax
        ↓
program structure and static well-formedness
        ↓
class chains, lookup, and dispatch
        ↓
sequential machine
        ↓
actors and eventual references
        ↓
reflection and debugger control
        ↓
optional garbage collection
```

PEG recognition and elaboration share the syntax and program layers, then
connect to the machine through compiler refinement.  They do not depend on
actors, reflection, or GC.

## Main proof forms

- Sequential execution: exact one-step determinism and preservation.
- Actors: deterministic selected turns plus trace safety under nondeterministic
  scheduling.
- Reflection: validation/commit atomicity, preservation, authorization, and
  commutativity only under an explicit independence predicate.
- Debugger: forward and backward simulation between reified control images and
  implementation PC/operand-stack states.
- GC: least-fixed-point reachability, preservation, and stuttering refinement
  modulo the specified weak-reference observations.
- Compiler: forward simulation from executable artifacts to annotated core,
  parameterized by the installed parser/elaborator/compiler objects.

## Acceptance rule

`Newspeak.Properties` imports and re-exports only completed theorems.  The
project must build with no `sorry`, `admit`, or axioms introduced by this
development.  Open obligations remain prose entries in `THEOREMS.md` until
their definitions exist and proofs check.
