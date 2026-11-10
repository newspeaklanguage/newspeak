# Relational Prolog bridge

This directory is the auditable middle layer between the mathematical
presentation in `../newspeak-semantics.tex` and the machine-checked Lean
development in `../lean`.

The authoritative Prolog source is `newspeak.pl`.  It is intentionally not
idiomatic, optimized Prolog.  Each semantic clause is introduced by metadata
that names its primary LaTeX rule or equation and its Lean counterpart.  An
optional `@also` annotation records additional equations genuinely embodied by
the same clause, avoiding duplicate alias predicates.  The clauses
belong to a small declarative subset checked by
`tools/check_relational_spec.py`.

The current checked inventory contains 1353 Horn clauses.  They encode 291 of
the 361 numbered equations.  No semantic equation remains deferred; the other
70 equations are classified explicitly as term representations, abstract
contracts, or theorem-only statements
in `EQUATION_DISPOSITIONS.tsv` rather than being silently omitted.

Instance-storage keys are `slot_address(ApplicationClass, SlotDeclaration)`;
nested-class-cache keys are `nested_cache(ApplicationClass, ClassDeclaration)`.
They are not bare declaration IDs or source names. `application_slots/3`
qualifies the declarations of each class application before layout concatenation.
The selected activation class supplies the qualification for accessors and
initializers. Reflection's typed heap-reconciliation adapters use these same
keys. `tools/test_application_storage.py` resolves the actual clauses in nine
bounded ground regressions without requiring a Prolog installation; it supports
only the tested ground `dif/2` calls and is not a general Prolog interpreter.

The completed dispatch vertical slices cover:

* finite-store lookup and the `direct` and superclass projections;
* the finite class-chain relation;
* unrestricted lookup (`U-Top`, `U-Here`, and `U-Super`);
* the independently specified defining-class relation;
* public lookup, including the protected barrier and transparent private
  declarations; and
* protected lookup;
* ordinary and super dispatch, including invalid super sends;
* finite lexical-class chains and exact lexical depth;
* enclosing-receiver traversal and outer/self dispatch;
* all four annotated implicit-dispatch cases; and
* unrestricted DNU selection plus fresh message-mirror allocation and final
  invocation;
* the positive, exhaustive complement of direct closure invocation; and
* all five non-eventual request-resolution branches and complete request
  handling through invocation, invalid-super, or DNU;
* method-activation construction and allocation; and
* tail/non-tail method invocation and installation of completed request
  results into machine control; and
* ordinary and cascade closure creation, direct closure-value dispatch,
  captured activation allocation, tail/non-tail closure invocation, and the
  closure-machine union; and
* expression evaluation order: literal/self values, ordinary and eventual
  receivers, non-ordinary request construction, empty/nonempty argument
  starts, source-ordered argument accumulation, and the analogous deferred
  message-template evaluator; and
* simultaneous-local expansion, including its installation-before-resolution
  ordering and empty/nonempty machine entry; and
* the complete body/local machine, including direct local access, statement
  sequencing, normal halt/resumption, canonical atoms, and all
  direct/current/lazy object-slot transitions; and
* return targets and dependent activations, heap-wide continuation
  invalidation, return-frame transfer, successful non-local return, and both
  `cannotReturn` cases; and
* sequential and simultaneous instance-slot groups, including direct commit,
  PastFuture installation-before-resolution, and the internal continuation
  sequence; and
* `Factory-New`, including activation-parameter extraction, root-to-leaf
  layout, nil-filled object allocation, initializer-activation allocation,
  and its machine transition; and
* the superclass/mixin initialization coordinator, its applied-mixin
  activation path and wrong-factory outcomes, plus the complete union of the
  factory, coordinator, and slot-group phases; and
* all nine class-body/mixin-application construction clauses, including
  inheritance validation, enclosing-object selection, factory construction,
  and fresh class/metaclass-pair allocation; and
* object-literal class allocation and immediate factory dispatch, plus
  receiver-local nested-class cache hit, miss, forced-enclosing-object, and
  store transitions; and
* both exception-library boundary transitions, using an explicit
  proof-carrying graph application of the platform's abstract total error
  reifier; and
* tuple, retained-cascade, and recursively nested pattern expansion, exact
  top-level halting, and every explicit union up to the complete sequential
  relation; and
* the complete actor layer: remote representation and recursive message
  transfer, eventual target selection and all routing cases, promise
  settlement and wake emission, asynchronous return, turn start and lifted
  sequential execution, local/remote turn completion, system-packet dequeue,
  eligible network delivery, and the complete actor-system union.
* the reflective boundary: authorized inspection, attenuated mirror
  derivation, atomic commit/reject, selected-VM installation, and
  capability-checked host primitives.  The fixed front end, runtime preparer,
  validator, rejection diagnostic, and host primitive remain explicit
  proof-carrying relation parameters; and
* the optional global GC wrapper, including never-reuse identity history,
  lifted ordinary transitions, and independently enabled atomic pruning; and
* the complete front-end phase composition: admissible PEG recognition,
  concrete-tree projection, Newspeak semantic actions, stable source-node
  identification, surface validation, Program derivation, and annotated-core
  checking.  The PEG core itself is expanded constructor by constructor for
  atomic recognition, sequence, ordered choice, repetition, lookahead,
  nonterminal invocation, and capture; concrete-tree/forest projection is
  recursive rather than an opaque phase witness.

`Newspeak.PrologLookupCorrespondence` proves in Lean that the relational
clause schema is sound and complete with respect to the existing named Lean
lookup and dispatch rules.  It composes lookup with the previously proved
equivalence between the rules and the executable Lean lookup function, and
continues compositionally through lexical depth, enclosing receivers,
implicit dispatch, DNU fallback, closure invocation, and expression order.
The same bidirectional correspondence now covers the body/local and
object-slot machines and local/non-local return.
Instance-slot group initialization has the same checked correspondence.
The complete `Factory-New` allocation path, coordinator, and their union with
slot-group execution do as well.
The class-construction bridge is exact after making one discrepancy explicit:
the Prolog clauses follow the LaTeX rules, while Lean's two commit constructors
also carry a proof that the resulting heap is globally well formed.  The
theorem names this `PrologClassConstructionCommitSafe`; it is not an invented
Prolog runtime test.
The analogous reifier witness is likewise just the Horn representation of the
premise `reifyError(P,H,error) = (H', exception)` printed in the LaTeX rule.
Object-literal commit has the same deliberately exposed allocation-certificate
boundary as named-class commit.  The final
`prologSequentialStepWithTopLevel_iff` theorem covers the complete sequential
machine.  It uses an admissible wrapper solely to carry those existing Lean
certificates; a parallel raw relation is the literal reading of the Horn
unions.
`Newspeak.PrologActorCorrespondence` then proves the actor clauses equivalent
component by component through `prologActorSystemStep_iff`.  Its graph
witnesses mark genuine platform contracts---value transfer, eventual-handle
interpretation, promise-handle installation, and incoming-message
materialization---rather than introducing hidden Prolog implementations.
`Newspeak.PrologReflectionCorrespondence` applies the same treatment to the
named reflection rules and proves their read, derivation, transaction, VM,
and host-primitive relations bidirectionally.
`Newspeak.PrologGCCorrespondence` proves the two modular wrapper rules
equivalent as well.  Consequently all named LaTeX natural-deduction rules are
represented; unchecked coverage entries now identify supporting equations.
`Newspeak.PrologFrontEndCorrespondence` continues through the source-to-core
boundary.  Its final `prologFrontEndDerivation_iff` theorem is bidirectional,
and its determinism theorem is inherited from the already-proved functional
PEG, identification, and derivation phases.  Grammar, lexical decoders, and
Program-derivation services remain explicit parameters, as required for
reflective replacement of language services.
`Newspeak.PrologPEGCorrespondence` proves the lower structural layer directly:
`prologPEGRecognizes_iff` covers every PEG constructor, while mutually
recursive soundness/completeness theorems cover tree and forest projection.
Character predicates, source indexing, arithmetic progress, source slicing,
and semantic-action calls are visible proof-carrying graph premises.
`Newspeak.PrologIdentificationCorrespondence` gives stable identity allocation
the same structural treatment.  Its clauses enumerate source nodes, project
their keys and sorts, prefer retained identities, generate fresh identities
when necessary, validate the resulting list, and extend the retention map.
The recursive identification and map-extension relations are both proved
sound and complete before being composed into
`prologSurfaceIdentification_iff`.
The recursive static elaborator is now readable in the same form.  Separate
clauses cover every successful surface-expression constructor, expression and
clause lists, all four receiver-specialized send forms, all pattern forms and
pattern pairs, and implicit/explicit class and object superclasses.  Fuel
decrease, binding, receiver classification, and retained synthetic identities
are explicit premises.  `Newspeak.PrologStaticElaborationCorrespondence`
fixes each relation's graph to the corresponding executable Lean function.
`Newspeak.PrologDeclarationCorrespondence` takes the next layer upward.
Statements, return admissibility, all five successful local-declaration forms,
declaration-list recursion, and sequential/simultaneous local groups have
structural Lean soundness and completeness proofs.  It also pins the Horn
graphs for formal parameters, physical slot collection, eager slot
initializers, and optional initializer groups to their executable Lean
definitions.
Access defaulting and member installation are also explicit: method, ordinary
slot, lazy slot, and deferred nested-class branches are distinct, and the
member-list fold is recursive.  Explicit methods expose the synthesized method
and activation identities, formal and local identities, flattened declaration
environment, activation context, elaborated locals and body, method definition,
image insertion, and activation-member update.
The outer Program layer is readable as Horn clauses too.  Class and object
header selection, implicit/explicit superclass syntax, superclass expressions
and messages, lexical object ownership, anonymous mixin-application folding,
bodyless and bodied mixin chains, structural-artifact completion, final image
installation, and the complete bodyless/bodied/ordinary class choice are all
separate predicates.  `Newspeak.PrologProgramDerivationCorrespondence` pins
their graphs to Lean; the final relation is deterministic and is connected to
the concrete complete-class derivation service used by the front end.

## Contract

The proof-facing source uses only definite clauses and the declarative
`dif/2` constraint.  It does not use cut, negation as failure, dynamic clauses,
side effects, meta-calls, or instantiation tests.  Absence is data (`none`),
not failed proof search.  Newspeak identities and uninitialized cells are
ground tagged terms, never Prolog variables.

Every clause group has these annotations:

```text
% @latex rule:U-Here
% @lean Newspeak.Program.UnrestrictedLookupRules.here
% @mode unrestricted_lookup(+,+,+,+,-)
```

An equation uses `equation:label` rather than `rule:name`.  A LaTeX rule may
expand into several Horn clauses when its premise contains a disjunction; the
`@variant` annotation distinguishes them.

The Prolog file is canonical for encoded clauses.  The checker reads the actual
file, rejects constructs outside the subset, verifies every LaTeX reference,
verifies every Lean declaration reference, and emits a normalized manifest.
`EQUATION_DISPOSITIONS.tsv` accounts for every numbered equation not directly
encoded as a clause.  Its allowed classifications are `term-representation`,
`abstract-contract`, `theorem-only`, and `deferred`, and every row must carry a
rationale.  Encoded status is inferred from actual clauses, so the checker
rejects attempts to claim it manually.  It also rejects missing, duplicate,
unknown, or contradictory dispositions and regenerates `COVERAGE.md` as the
complete 361-equation ledger.  Lean correspondence files are reviewed against
that manifest.  A future
fully mechanized importer can replace this deliberately small trusted
checking boundary without changing the Prolog source.

## Checking

From `formal-semantics`:

```sh
python3 prolog/tools/check_relational_spec.py
cd lean && ~/.elan/bin/lake build
```

If a Prolog implementation is installed, the source can also be consulted
directly.  Execution is useful for examples, but its search strategy is not
part of the correspondence claim.
