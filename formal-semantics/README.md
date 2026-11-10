# Newspeak formal semantics

## Application-local storage correction (October 12, 2026)

Equation (8.16), `eq:slot-layout`, formerly appended bare declaration IDs.
With two applications of the same stateful mixin, the LaTeX and SpecTec
therefore repeated keys; Lean and Prolog rejected the resulting non-unique
layout. Neither behavior implements separate storage for each application.

All four now qualify instance cells by `(application class, slot declaration)`.
Accessors, lazy getters, and initializers use the activation's selected class;
deferred frames capture that address before evaluation. Nested-class caches
also use `(application class, nested declaration)` per receiver. Reflection
reconciliation preserves qualified keys rather than conflating declarations.

`lean/Newspeak/ApplicationStorage.lean` proves application/address separation
and arbitrary successful-write isolation, with kernel-checked repeated-mixin
layout, access, initialization, cache, closure-context, and migration examples.
The Prolog suite resolves the actual clauses in nine bounded ground tests;
the test driver is not a general Prolog interpreter or an equivalence proof.
SpecTec has 226 evaluated regressions, including repeated-stateful-mixin
isolation. These checks close this specific gap; existing metatheorems alone
did not establish that every intended legal class had an accepted storage layout.
The new general layout theorem establishes acceptance for any duplicate-free
application chain with duplicate-free own layouts, irrespective of repeated
mixin identities. This is structural acceptance, not a claim that every factory
returns normally: a legal class's factory (including its initializers) can raise
an exception. The non-normative Python initialization oracle now uses the
same qualified-address model and has repeated-mixin isolation tests too.

This directory contains a formal, executable-minded account of Newspeak's
runtime semantics.  Its normative language reference is working version 0.109
of the Newspeak specification.  Section 3.3 of *Modules as Objects in
Newspeak* (ECOOP 2010) is supporting explanatory material, especially for
implicit-receiver selection; where the two differ, the current specification
wins.

The project deliberately separates four things that are often conflated:

1. the surface PEG and its AST;
2. elaboration of syntactic conveniences and implicit members;
3. the sequential operational semantics;
4. concurrency and causally connected reflective change.

Design draft 0.14, `newspeak-semantics.tex`, fixes the semantic domains, the
lookup/dispatch kernel, the complete sequential language, and its actor lift:
isolated heaps, remote representation, asynchronous sends, FIFO turns, promise
settlement and pipelining, actor creation, and causal/E-ordered delivery.
It also includes mirrors, exact-instance and mixin-application population
queries, transactional reflective program change, and an explicit
garbage-collection overlay.  The reflective layer also gives every live frame
an explicit current term and source/PC location, supports immutable stack
snapshots, pause-token guarded actor suspension, atomic whole-stack
replacement, fresh frame and segment copying, resumable-exception transfer,
and resumption under the normal VM execution relation.  It states the
refinement obligation connecting the Newspeak Simulator's bytecode frames to
these abstract frame images.  The garbage-collection layer is isolated in
`gc-semantics.tex`; removing its single `\input` line restores the
monotonically growing-store semantics without altering the actor or reflection
rules.  When included, that layer also gives `WeakArray` weak-element clearing
and `WeakMap` ephemeron/key-weak behavior, including atomic clearing during a
partial collection.  The draft also gives a normalized concrete Newspeak PEG,
production-complete concrete-tree actions, metadata attachment, stable AST
identities, exhaustive static elaboration, annotated-core validation, and
executable artifacts.  The
active parser, elaborator, and compiler are ordinary Newspeak objects selected
through a reified language descriptor; their replacement uses existing
mutation and reflection, while the VM retains a fixed core-verification and
artifact-loading boundary.  `coverage.md` is a
ledger against the language specification.  A feature may not disappear merely
because it is inconvenient to formalize: it remains in the ledger until it has
rules or is explicitly classified as a host/platform parameter.

`lookup_model.py` is a non-normative executable oracle for the lookup rules.
Its tests pin down access barriers, lexical private dispatch, virtual protected
dispatch, DNU, and the starting point of super lookup.
`class_init_model.py` similarly pins down freshness, mixin sharing, physical
layout, initialization order, simultaneous installation, lazy nil behavior,
and per-receiver nested-class caching.
`actor_model.py` pins down remote-representation normalization, immediate
promise creation, FIFO turns, causal delivery barriers, pipelined sends, and
broken-promise propagation.
`gc_model.py` pins down strong and conditional weak-map reachability,
`WeakArray` clearing, `WeakMap` entry removal, closed partial reclamation,
observable instance and mixin-application enumeration, and permanent non-reuse
of collected identities.
`debugger_model.py` pins down stack imaging, push/pop/copy construction,
fresh-identity rewiring, stale pause-token rejection, atomic replacement, and
full-speed resumption.
`frontend_model.py` pins down PEG ordered choice, greedy repetition, capture
spans, grammar admissibility, complete-input recognition, front-end image
capture, ordinary component replacement, and fixed-boundary rejection of
invalid core images.

`lean/` is the machine-checked companion development.  Its theorem inventory
tracks every obligation in section 14, while `Newspeak.Properties` exports
only completed proofs.  The initial checked slice covers typed semantic
identities, the static-program/heap separation, static program coherence,
finite superclass and lexical-class chains, deterministic unrestricted,
public, and protected lookup, equivalence with the named lookup rules, and the
static `bind = scan` theorem.  The current runtime bridge keeps mixin
definitions in the program while giving mixin identities ordinary heap object
representation; it also proves determinism of nearest application, lexical
depth, ordinary dispatch, super dispatch, and DNU target selection.
It also covers the special depth-one enclosing-object rule, deterministic
outer/self dispatch, and the dynamic equivalence of the elaborated and
ECOOP-style class-scope implicit-send presentations.

`prolog/` is the auditable relational bridge between the labeled LaTeX rules
and Lean.  Its canonical `newspeak.pl` source is restricted to checked
definite clauses plus `dif/2`; every clause names its LaTeX origin and Lean
counterpart.  The completed initial slice covers class chains, unrestricted,
public, and protected lookup, the independent defining-class judgment,
ordinary and super dispatch, exact lexical depth, enclosing receivers,
outer/self/implicit dispatch, and allocation-bearing DNU fallback.  Lean
proves the bridge relations sound and complete with respect to the existing
named rules and executable lookup definitions.  The generated traceability
manifest hashes the actual Prolog source so drift is visible.  The bridge now
continues through direct-closure exclusion and all non-eventual request
resolution/completion branches, method-activation allocation, tail/non-tail
method invocation, and the request-completion machine step.
Closure construction (including cascades), direct closure-value dispatch,
captured activation allocation, and both closure invocation modes are also
connected bidirectionally.  Expression-order correspondence now covers
literal and self values, ordinary and eventual receiver evaluation, all four
non-ordinary requests, and left-to-right argument evaluation for sends and
deferred messages.  Simultaneous-local expansion and its required
installation-before-resolution order are connected as well.  The bridge also
covers every body/local-machine transition, normal activation completion,
canonical atoms, direct, current, and lazy object-slot access, and the complete
local/non-local-return machine including heap-wide continuation invalidation.
Sequential and simultaneous instance-slot initialization, including the
installation-before-resolution expansion, is connected bidirectionally too.
So is `Factory-New`, from physical-layout construction and nil initialization
through fresh object and initializer-activation allocation.  The bridge now
also covers the superclass/mixin coordinator, applied-mixin activation, both
wrong-factory outcomes, and the complete three-phase instance-initialization
union.
All class-construction support equations and all nine construction clauses are
now represented too.  Their bridge exposes, rather than conceals, one current
Lean/LaTeX mismatch: Lean's two commit constructors carry an additional
post-allocation global-well-formedness proof.  The correspondence theorem is
therefore stated for a raw Prolog step paired with that explicit commit-safety
obligation.
The two exception-library boundary rules also correspond bidirectionally.  An
explicit `error_reification(...)` graph witness represents the abstract total
platform operation's application; it is not a second exception allocator.
Object-literal allocation, receiver-local nested-class caching, tuple and
pattern expansion, retained cascades, and top-level halting are now connected
bidirectionally as well.  Explicit Horn union clauses assemble all of these
pieces into the complete sequential relation; Lean proves the final
admissible union equivalent to `SequentialStepWithTopLevel`.  The adjective
``admissible'' records only the post-allocation well-formedness evidence still
stored in Lean's class and object-literal commit constructors, while the raw
union remains an exact reading of the LaTeX/Prolog operational clauses.
The bridge has now crossed the sequential/actor boundary as well.  Remote
representation, recursive message transport, all routing and settlement
branches, asynchronous return, turn start and completion, system-packet
dequeue, eligible network delivery, and the complete scheduler-visible actor
step are represented by Horn clauses.  `Newspeak.PrologActorCorrespondence`
proves each component and the final actor-system union equivalent to the Lean
relations.  Platform-defined value transfer, local handle interpretation, and
message materialization remain explicit proof-carrying graph premises rather
than being silently implemented by the bridge.
The named reflection rules are connected next: authorized inspection,
authority-attenuating mirror derivation, atomic commit/reject, selected-VM
installation, and capability-checked host primitives.  The bridge adds Lean
relations for mirror derivation and VM primitive invocation where the prose
previously had no named Lean judgment, then proves the Prolog and Lean forms
equivalent.  It now also covers reflection query targets and results,
source-command patching, re-elaboration and preparation, every command-family
fold, validation and diagnostics, conflict footprints, version observation,
stack snapshots and descriptors, pause/resume/replace operations, continuation
transfer, and fresh stack-frame segment copying.
The optional global GC wrapper is represented too: ordinary actor or
reflection steps lift only when their new identities have never appeared in
the execution history, while collection is an independently enabled atomic
pruning step that preserves that history.  With this addition every named
natural-deduction rule in the LaTeX sources has a checked Prolog clause; the
remaining ledger entries are supporting equations, not missing rules.
The source boundary is connected as well.  Proof-carrying Horn relations now
separate complete PEG recognition, tree-to-AST projection, stable
identification, surface checking, Program derivation, and annotated-core
validation.  `Newspeak.PrologFrontEndCorrespondence` proves the composite
relation bidirectionally equivalent to `FrontEndDerivation` and proves its
result deterministic.  The current grammar, decoder tables, and derivation
services remain parameters so reflective language-service replacement does
not become a hidden trusted constant.
The PEG portion is structural, not just a phase certificate: all atomic and
composite recognition cases and the mutually recursive tree/forest projection
clauses have direct Lean soundness and completeness proofs.
Stable identification is structural too.  The Horn layer explicitly enumerates
surface nodes, chooses retained identities before sort-specific fresh ones,
recurses through the node list, checks the resulting identities, and extends
the retention map in source order.  Lean proves the recursive identification
and retention-extension relations sound and complete for their executable
counterparts, then derives the compilation-unit identification theorem from
those results.
The successful branches of static elaboration are also explicit Horn clauses:
ordinary and specialized sends, cascades, setters, tuples, patterns, closures,
class/object expressions, list recursion, and superclass selection all expose
their fuel, binding, receiver-kind, and retained-identity premises.  Lean graph
theorems pin each relation to the pre-existing executable elaborator.
The bridge now continues through statements and local declarations.  Return
admissibility, all ordinary and lazy local forms, declaration lists, and
sequential/simultaneous groups have structural soundness and completeness
proofs.  Formal-parameter identities, physical-slot collection, eager
initializer declarations, and optional initializer groups are source-visible
Horn clauses whose graphs are fixed to the corresponding Lean functions.
Access defaulting, synthesized ordinary/lazy slot methods, method installation,
and recursive member installation are now exposed at the next boundary too.
Explicit methods expose their declaration and activation identities, formal
and local identities, flattened declaration environment, activation context,
elaborated locals and body, method definition, image insertion, and activation
member update.
`Newspeak.PrologProgramDerivationCorrespondence` continues through class and
object headers, anonymous mixin-application folding, bodyless and bodied mixin
chains, structural-artifact completion, image installation, and the final
bodyless/bodied/ordinary Program choice.  Its complete-program relation is
deterministic and `prologCompleteClassProgram_services_iff` connects it to the
exact `ProgramDerivationServices` value used by the composite front end.
Every numbered LaTeX equation is now accounted for by the checked disposition
ledger.  Of 361 equations, 291 have checked Horn clauses, 51 are represented
by the Prolog term grammar, 10 are explicit abstract contracts, and 9 are
theorem-only propositions.  No equation remains deferred; all 86 named
natural-deduction rules are represented as well.
The checker rejects any unclassified equation or any manually asserted
`encoded` status not backed by a clause.

## Building

`spectec/` begins the LaTeX-first migration to a checked, generatable SpecTec
source. It transcribes lookup, lexical receiver selection, binding, dispatch,
full base runtime records, DNU allocation, and much of the sequential machine;
class construction, factories, initializer groups, and slot/cache operations
are now included as well. Its exhaustive coverage ledger distinguishes converted
definitions, explicitly
partial transcriptions, and pending work. It uses a pinned upstream
checker and deterministic mathematical/AST generation. Full-language
conversion, Rocq generation, and correspondence proofs are not yet complete.
See [the SpecTec guide](spectec/README.md).

From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error newspeak-semantics.tex
python3 -m unittest discover -s prolog/tools -p 'test_*.py'
python3 prolog/tools/check_relational_spec.py --write
cd lean && ~/.elan/bin/lake build Newspeak.Properties
```

The semantics is currently a design draft, not yet a replacement for any
normative text in the language specification.
