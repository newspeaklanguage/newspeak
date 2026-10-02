# Theorem inventory

This inventory decomposes section 14 of the formal semantics into Lean-sized
claims.  `[x]` means the theorem is checked and exported by
`Newspeak.Properties`; `[ ]` means the necessary semantic layer or proof is
still outstanding.  Numbered invariant entries refer to the order in section
14, while M-entries come from its final metatheory paragraph.

## Static structure and lookup

- [x] S1. Direct method selection is functional (`direct_unique`).
- [x] S2. A class-chain witness from a fixed class is unique
  (`ClassChain.unique`).
- [x] S3. Unrestricted lookup is deterministic.
- [x] S4. Public lookup is deterministic, including protected barriers.
- [x] S5. Protected lookup is deterministic and skips private methods.
- [x] S6. The U/Pub/Prot named inference rules are equivalent to executable
  lookup over the unique finite runtime class chain.
- [x] S7. The U/Pub/Prot named inference rules are deterministic.
- [x] S8. Under the explicit scope/parent correspondence, the elaborated
  class binding and ECOOP-style lexical-class scan agree (`binding_equivalence`).
- [x] S9. Nearest runtime application and lexical depth are deterministic.
- [x] I2. Every live base class has a finite chain ending in `Top`
  (`WellFormed.chain_exists`, `ClassChain.last_eq_top`).
- [x] I3. Every class retains its applied mixin and enclosing object; a
  well-formed class record's mixin resolves in the installed program
  (`WellFormed.class_record_retains_mixin_and_enclosingObject`).
- [x] I4. Every class retains its tagged expression/actor origin and source
  declaration (`class_record_retains_origin_declaration`).
- [x] I5. Created classes have fresh, distinct metaclasses; repeated
  applications preserve the selected instance-side mixin
  (`allocateClassPair_was_fresh`, `allocateClassPair_installs`).
- [x] I6. Every installed mixin retains its inducing declaration identity
  (`mixin_lookup_retains_inducing_declaration`).
- [x] I8. Nested-class caches are receiver-local and single-valued by inducing
  declaration (`NestedClassStep`, `readNestedClass_singleValued`).
- [x] I12. Direct selectors are unique within each elaborated mixin
  (`MixinDef.method_at_selector_unique`).
- [x] I14. Inherited public/protected lookup never selects a private method;
  public lookup returns only public methods, while protected lookup returns
  public or protected methods (`publicLookup_result_is_public`,
  `protectedLookup_result_not_private`).
- [x] M4a. The static `bind = scan` equivalence holds after ruling out nearer
  activation and object-literal bindings.
- [x] M4b. After nearer activation/object-literal bindings are ruled out, the
  elaborated and ECOOP presentations yield the same outer/self dispatch result.

## Sequential runtime

- [x] D1. Ordinary dispatch is deterministic for a well-formed `P,H` pair.
- [x] D2. Super dispatch is deterministic, including explicit `Object` and
  `Top` errors.
- [x] D3. Unrestricted DNU method/current-class selection is deterministic.
- [x] D4. Enclosing-receiver traversal is deterministic and preserves the
  specification's special depth-one behavior.
- [x] D5. Private selection, outer dispatch, and self dispatch are
  deterministic for a well-formed `P,H` pair.
- [x] D6. The elaborated and scanned class-scope implicit-dispatch
  presentations are equivalent and deterministic.
- [x] D7. Complete annotated implicit dispatch, including activation,
  object-literal, class, and self fallback branches, is deterministic.
- [x] D8. Ordinary, implicit, outer, self, and super requests resolve
  deterministically; closure-value requests are disjoint from ordinary
  lookup.
- [x] D9. DNU allocates a fresh message mirror, preserves the mirror-supply
  invariant, and complete request processing is deterministic.
- [x] D10. Tail and non-tail method invocation allocate a fresh activation,
  preserve all five allocation supplies, and are deterministic.
- [x] D11. Receiver-first and left-to-right argument evaluation, request-result
  installation, and their current union with invocation are deterministic.
- [x] D12. Sequential, lazy, absent, and simultaneous local initialization;
  local reads/writes; statement sequencing; and ordinary completion are
  deterministic.  Simultaneous installation precedes every resolution.
- [x] D13. Local and non-local return use method/home-method targets, mark the
  least continuation-dependent activation set uncontinuable, and deterministically
  resume or produce `cannotReturn`.
- [x] D14. Closure creation materializes the installed declaration and captures
  its defining activation, receiver, class, and home method.  Direct closure
  dispatch, tail/non-tail closure invocation, and the enlarged sequential-rule
  union are deterministic and preserve all five allocation supplies.
- [x] D15. Every rule in the current sequential relation preserves explicit
  sequential well-formedness: program/heap coherence, all five fresh-supply
  invariants, stack-activation liveness, and invocation-class admissibility.
- [x] D16. Atomic evaluation, direct/current/lazy slot operations, normalized
  class bodies, mixin applications, inheritance errors, and fresh
  class/metaclass allocation are deterministic in the enlarged relation
  (`objectSlotStep_deterministic`, `classConstructionStep_deterministic`).
- [x] D17. Deferred message arguments evaluate left-to-right.  `Factory-New`
  allocates a fresh instance and a distinct initializer activation, installs
  their complete runtime context, and extends the prior relation
  deterministically while preserving sequential well-formedness
  (`messageEvaluationStep_deterministic`, `factoryNewStep_deterministic`,
  `sequentialStepWithFactory_deterministic`).
- [x] D18. The superclass/mixin initializer coordinator is executable,
  deterministic, and well-formedness preserving.  It evaluates the superclass
  message before entering the superclass initializer, then executes either the
  body mixin directly or an applied mixin in a fresh initializer activation;
  selector or arity mismatch produces `wrongFactory`.
- [x] D19. Sequential and simultaneous instance-slot groups are executable,
  deterministic, and well-formedness preserving.  Sequential groups bypass
  accessors; simultaneous groups install all source-ordered `PastFuture`
  objects before their source-ordered `resolve` sends
  (`slotSimCode_installationPrefix`).
- [x] D20. The factory, coordinator, and slot-group phases are pairwise
  disjoint and are also disjoint from every preceding sequential rule.  Their
  union with the preceding relation is deterministic and preserves sequential
  well-formedness (`sequentialStepWithInitialization_deterministic`,
  `sequentialStepWithInitialization_preserves_wellFormed`).
- [x] D21. Object literals fix their enclosing object before superclass
  evaluation, allocate a fresh class/metaclass pair, and continue through an
  ordinary nullary factory send.  Nested-class getters force the receiver as
  enclosing object for class bodies, cache only successful class results per
  receiver, and the enlarged relation remains deterministic and
  well-formedness preserving (`sequentialStepWithObjects_deterministic`).
- [x] D22. The synthesized primary-factory primitive is static syntax over a
  selector and parameter identities; it reads runtime argument objects from
  the factory activation.  An allocated object-literal class is proved to
  reach that synthesized method through ordinary public lookup, and
  `Factory-New` is proved to allocate exactly the fresh object frontier with
  its complete nil-initialized layout (`allocatedObjectLiteral_dispatchesToPrimaryFactory`,
  `factoryNewStep_allocates_fresh_instance`).
- [x] D23. Finite execution is explicit and preserves sequential
  well-formedness.  Successful Object-Commit is composed with public factory
  lookup, ordinary method entry, body execution, and `Factory-New`; the
  resulting theorem identifies the new instance with the original object
  frontier and proves its class, complete layout, nil slot values, and empty
  nested-class cache (`objectLiteralCommit_allocatesFreshInstance`).
- [x] D24. The VM exception boundary is parameterized by a total deterministic
  error reifier whose laws preserve existing heap records, well-formedness,
  and fresh supplies and guarantee an ordinary public `signal` method.
  `runtimeError` and `throw` both reify and dispatch that same nullary message
  without changing the activation/evaluation stack
  (`exceptionBoundaryStep_preserves_stack`,
  `exceptionBoundaryStep_has_public_signal_dispatch`).  The enlarged
  sequential relation is deterministic and preserves the full invariant
  (`sequentialStepWithExceptions_deterministic`,
  `sequentialStepWithExceptions_preserves_wellFormed`).
- [x] D25. Activation and closure current-class/home fields admit genuine
  absence, so top-level execution uses neither `Top` nor an activation ID as a
  nil sentinel.  A checked top-level expression allocates the exact empty top
  activation; Top-Halt makes it uncontinuable and halts with an empty stack.
  Entry and the enlarged step relation are deterministic and preserve
  well-formedness (`topLevelEntry_wellFormed`,
  `sequentialStepWithTopLevel_deterministic`,
  `sequentialStepWithTopLevel_preserves_wellFormed`).
- [x] D26. Tuple and pattern core forms have their exact syntax-directed
  library expansions.  Nonempty tuples retain a stable cascade site and use
  the specified synthetic one-argument closure; its parameter, empty locals,
  and complete source-ordered body are retained in materialized control and
  are therefore unaffected by a later reflective program installation.
  Keyword patterns construct distinct ordered keyword and component tuples,
  nested patterns retain the lexical `Pattern` annotation, and only the
  Specification's underspecified variable-pattern constructor remains a
  program parameter.  The compound-literal relation and its integration with
  top-level execution are deterministic and preserve sequential
  well-formedness (`compoundLiteralStep_deterministic`,
  `sequentialStepWithLiterals_deterministic`).
- [x] D27. Every top-level runtime identity store has an exact finite,
  duplicate-free domain.  The executable `allInstancesOf` query ranges over
  ordinary objects, classes, mixins, activations, closures, mirrors, and
  actors; the executable `allApplicationsOf` query ranges over every runtime
  class record, including metaclasses.  Both queries have exact membership
  theorems and duplicate-free results (`mem_allInstancesOf_iff`,
  `mem_allApplicationsOf_iff`).
- [x] D28. Every partial runtime environment is finite: ordinary-object slots
  and nested-class caches, plus activation parameters, locals, activation
  scopes, and object-literal scopes.  Every partial static `Program` dictionary
  and each mixin method dictionary is finite as well.  Allocation/binding
  constructors have exact domain theorems for instance layouts, paired
  parameters, local declarations, method/initializer scopes, and inherited
  closure scopes (`mem_slotsInitializedTo_domain_iff`,
  `mem_bindParameters_domain_iff`,
  `mem_initializeLocalCells_domain_iff`,
  `mem_extendActivationScope_domain_iff`).
- [x] I1. Every live ordinary object names exactly one live class
  (`liveOrdinaryObject_has_unique_liveClass`).
- [x] I7. Instance layouts are uniquely determined root-to-leaf class-chain
  concatenations; allocation gives exactly those slots initial value `nil`
  and an empty nested-class cache (`instanceLayout_unique`,
  `allocatedInstance_realizes_layout`).
- [x] I9. Equal atomic payloads denote one canonical literal object, and
  equality of atomic objects implies equality of exact payloads
  (`atomObject_iff_payload`).
- [x] I10. Object-literal evaluation allocates a fresh object, class, and
  metaclass while reusing its declaration mixin. The class/metaclass pair is
  fresh and distinct and the installed instance-class record contains exactly
  the descriptor's instance mixin
  (`objectLiteralClassPair_fresh_and_reuses_mixin`); the complete successful
  commit allocates the instance at the unchanged fresh object frontier
  (`objectLiteralCommit_allocatesFreshInstance`).
- [x] I11. Module definitions are precisely instantiable top-level named-class
  expressions: their runtime class record has a factory, expression provenance,
  and `topOwner`; requiring a factory excludes the paired metaclass
  (`moduleDefinition_iff_instantiable_topLevelExpression`). A module instance
  is exactly an object whose class is such a definition, and every module
  definition is a primitive value object
  (`moduleInstance_iff_classIsModuleDefinition`,
  `ModuleDefinition.isPrimitiveValueObject`).
- [x] I13. Dispatch determines both method and activation current class; method
  allocation installs the dispatch defining class as the callee current class.
- [x] I15. Failed user dispatch invokes DNU exactly once for the original
  message; its freshly allocated mirror is the sole DNU argument.
- [x] M1. The complete sequential one-step relation through compound literals,
  exception reification, and top-level termination is deterministic
  (`sequentialStepWithTopLevel_deterministic`).
- [x] M2. The complete sequential relation preserves heap coherence, fresh
  supplies, live materialized stacks, and invocation-class admissibility
  (`sequentialStepWithTopLevel_preserves_wellFormed`).

## Actors and eventual references

- [x] I16. Mutable objects and active computations have exactly one actor;
  cross-actor arguments are transferable values, far references, or promises.
  Under the checked private/value-heap isolation invariant, every live record
  has a unique heap owner, every private record has exactly its allocating
  actor as owner, and a live activation has that same unique actor
  (`ObjectOwner.existsUnique_of_worldHeap`,
  `ObjectOwner.privateHeap_owned_exactly_by_actor`,
  `ObjectOwner.activation_owned_exactly_by_actor`).
  `RemoteRepresentation.cross_actor_classification` proves that the five
  distinct-actor transport cases are exhaustive: copied/shared values remain
  near, far references come home or retain identity, promises retain identity,
  and a non-value near reference receives one fresh far identity. The
  location-aware actor root extractor covers running/paused turns, mailboxes,
  network packets, promise states, far targets, and external handles.
- [x] I17. Transfer back to a target actor normalizes a far reference to its
  near referent, while transfer to a third actor preserves the same far
  identity and never creates a proxy chain
  (`RemoteRepresentation.far_home_normalizes`,
  `RemoteRepresentation.far_third_party_preserves_identity`).
- [x] I18. Actor executions impose one-turn-at-a-time execution, FIFO mailbox
  selection, E-order, and weak fairness.  Scheduler choices are explicit
  action labels; `WeaklyFairActorExecution` states the fairness condition, and
  `ActorActionStep.delivery_respects_e_order` proves that delivery cannot
  overtake a same-destination causal predecessor.
- [x] I19. Promises settle at most once and resume dependents only afterward.
  Terminal promise states are preserved by every actor-system step under the
  explicit promise-store-preserving value-transfer obligation.  Hence a
  promise has at most one pending-to-terminal transition in an execution
  (`IsActorExecution.promise_settles_at_most_once`).  Wake packets carry the
  originating promise identity, and the recursive emission proof records that
  the terminal commit precedes every dependent wake
  (`PromiseSettlement.emits_wakes_only_after_terminal_commit`).
- [x] M3. Each selected actor turn is deterministic; global scheduling remains
  deliberately nondeterministic.
  Source-level eventual sends evaluate receiver-first and arguments
  left-to-right, stop at an explicit eventual dispatch, and are intercepted by
  the actor rule that allocates, routes, and returns the result promise.
  Application start, sequential execution, eventual interception, normal
  completion, settlement dequeue, and wake dequeue are pairwise disjoint and
  deterministic under the explicit platform-functionality assumptions
  (`SelectedActorStep.deterministic`).  A fixed scheduler action is likewise
  deterministic (`ActorActionStep.deterministic`); nondeterminism is exactly
  the action choice.

## Reflection and debugger

- [x] I20. Source edits and their required re-elaboration commit atomically.
  `ReflectionFrontEnd` separates partial source patching from complete
  re-elaboration, and `prepareReflection` sequences both before any candidate
  can be committed.  `prepareReflectionRuntime` now instantiates the complete
  ordered run-time phase composition over the VM cohort.
  `identifiedSourceReflectionFrontEnd` supplies distinct partial functions for
  all seven code edits, folds them over the identified normalized source AST,
  checks both directions of its method indexes, and rebuilds the program's
  mixin, body, and local-declaration projections before runtime preparation.
  Initial PEG-to-identified-AST construction is discharged separately by I34.
- [x] I21. Every reflective read or change is covered by mirror target and
  rights. Authority-bearing mirror payloads, target containment, command
  targets/rights, and `ValidReflection.every_command_authorized` cover every
  transaction command. The exhaustive `ReflectionQuery` API covers VM,
  program, mixin, method, class, object, activation, actor, instance-enumeration,
  and mixin-application reads. `AuthorizedReflectionRead.requires_inspect`
  gates every successful read with the `inspect` right, and
  `ReflectionAccess.is_authorized` classifies every modeled read or change by
  its exact mirror, target, and required right.
- [x] I22. Success increments the VM program version exactly once; failure is
  the identity on every state component.  Preparation overwrites the candidate
  version with exactly `n + 1`, proved by
  `prepareReflection_increments_version_exactly_once`; rejection has the
  identical state as both source and target, and `atomic_version_effect`
  classifies every transaction step as stuttering or one version increment.
- [x] I23. Layout migration preserves retained slots, initializes new slots to
  `nil`, and makes removed slots unreachable.  `reconcileKeys_preserves`,
  `reconcileKeys_initializes`, and `reconcileKeys_removes` prove the three
  cases; the all-object and nested-cache folds are explicit partial functions.
- [x] I24. A VM cohort observes one committed version; other VMs change only
  through their own authorized transactions.  An actor observes the single
  `Program` field of its `ActorWorld` (`cohort_observes_one_program`), while
  `VMReflectionStep.other_vms_unchanged` proves a selected cohort update is
  pointwise identical at every other VM identity.
- [x] I25. Code installation preserves materialized control; later dispatch
  uses the current installed version.  `RunControlObservation` erases only the
  mutable allocation embedded in a live configuration;
  `prepareReflection_codeOnly_preserves_materialized_control` proves a
  code-only source/re-elaboration commit preserves every actor's stack, term,
  reply/event metadata, pause token, and stop reason.  Future ordinary actor
  execution requires the current `ActorWorld.program` explicitly
  (`ActorSequentialStep.uses_installed_program`).
- [x] I26. A nonempty running or paused stack has one active top control image
  and resumable suspended lower frames.  `decodeControlImage` accepts only a
  sequence of suspended lower frames followed by one active frame, and
  `materializeStackTemplate_nonempty` proves successful installation is
  nonempty.
- [x] I27. Copied frames receive fresh activation IDs and consistently renamed
  internal links; retained frames preserve IDs.  The executable resolver now
  distinguishes retained and fresh keys, rejects collisions, and substitutes
  continuation, home, and activation-scope links.
  `resolvedTemplateKeys_are_fresh_and_distinct` proves resolved IDs are
  duplicate-free, every fresh binding was absent from the old heap, and every
  retained binding preserves its activation ID.
- [x] I28. Paused-stack mutation requires the current pause token and
  invalidates it on success.  Wrong-token resumption is rejected, and
  `replacePausedActorStack_invalidates_token` proves successful replacement
  installs the next fresh token and advances its frontier.
- [x] I29. Stack replacement is atomic and discarded activations cannot
  continue.  Materialization computes removed live frames and retires them
  before installing the new records;
  `retireRemovedActivations_makes_uncontinuable` proves every removed record
  that remains inspectable has `continuable = false`.
- [x] I30. Full-speed resumption uses the ordinary sequential relation.
  `resumePausedActorAtFullSpeed_installs_running_turn` proves exact-token
  resumption installs `runningTurn`, after which the existing selected-actor
  rule admits only the ordinary sequential semantics.
- [x] M5. Valid reflective transactions preserve global well-formedness.  The
  concrete validator checks all cohort heaps for class-graph and full heap
  coherence, exact layouts and nested caches, live coherent run states,
  acyclic/live continuation links, admissible activation classes, and heap
  isolation. `ValidReflection.preserves_reflectionCohortWellFormed` extracts
  the complete structural invariant from every valid commit.
- [x] M6. Pairwise-independent reflective commands commute; therefore every
  permutation of an independent transaction has the same commit result.
  The generic theorem
  `applyOptionalCommandSequence_permutation` now lifts adjacent commutation to
  any permutation while preserving both success and failure; the companion
  theorem handles lists already carrying pairwise semantic commutation, and
  family filters preserve permutations.  Checked source instances now cover
  method-body and full-definition replacement, distinct removals, fresh adds
  up to pointwise source-image equivalence, and every pair among slot,
  nested-declaration, and mixin-initializer replacement.  Method-dictionary
  footprints include old-selector read dependencies.  Checked runtime
  instances cover class-graph edits, object reclassification, validated
  object-slot writes, and a common record-edit algebra for parameter, local,
  current-class, and continuation changes.  A conservative global
  activation-graph footprint accounts for state-dependent frame retirement;
  it proves that a nonconflicting transaction contains at most one
  continuation transfer, making that entire phase permutation invariant.
  Debugger footprints now also expose the global pause-token supply.  The
  complete compatible-pair classification is proved, together with concrete
  commutation for every permitted constructor pairing (distinct-actor resume
  with each command form, plus pause with the two non-token-minting stack
  replacement forms). These equations now include every rejection path, and
  static nonconflict directly derives debugger transaction independence.
  Invariant-indexed lifting through the debugger fold is checked, as are exact
  permutation theorems for the class-graph,
  object-class, object-slot, activation, and continuation cohort folds.
  The source fold now has a separate observational permutation theorem:
  relational command extensionality and pairwise diamonds compose through
  failures and arbitrary permutations.  Every source command is proved
  extensional under source lookup equivalence, so the source-fold theorem no
  longer takes extensionality as a hypothesis. `Program.LookupEquivalent`
  removes finite-store domain order from program observation. Source
  consistency compares finite-store supports rather than domain-list order
  and is invariant under source lookup equivalence, so re-elaboration agrees
  on failure and success and preserves program lookup equivalence. The
  ordered runtime prefix and complete runtime preparation are now explicitly
  composed: given the phase certificates, initial actor-store coherence, and
  the static nonconflict witness, any transaction permutation has exactly the
  same prepared actor world. Every pre-debugger cohort phase and both
  reconciliation passes preserve actor-store coherence, so the debugger
  boundary no longer requires a separate coherence certificate.
  `prepareReflection_permutation_modulo` also
  completes the outer composition through source patching, re-elaboration,
  runtime preparation, and atomic installation, preserving failure and
  quotienting only source/program domain order. Program lookup-equivalence is
  observational for executable class chains, layouts, nested-class keys, heap
  reconciliation, reflective slot writes, cohort reconciliation, debugger
  materialization, and complete runtime preparation. Consequently
  `reflectionPipelineExtensionality_of_runtimeCertificates` discharges the
  compiler/runtime boundary from one concrete phase-certificate record; no
  abstract pipeline-extensionality premise remains. Static nonconflict now
  constructs that entire runtime certificate directly (class graph, object
  class, object slots, activations, debugger, and continuation). During the
  source audit, `addMethodDefinition` was corrected to claim the method-body
  location it actually installs; without that location, adding method `m` and
  replacing `m`'s body formed a false independence pair. The exhaustive
  seven-by-seven source-edit matrix is now checked by
  `compatibleSourceCodeCommands_commuteModulo`; its add cases use lookup
  equivalence because fresh finite-store insertion order is unobservable.
  `sourceTransactionIndependentModulo_of_nonconflicting` derives the complete
  source certificate from static nonconflict, and
  `prepareReflection_permutation_of_nonconflicting` composes it with all
  runtime certificates, re-elaboration, and atomic installation. Thus callers
  supply only nonconflict, a permutation, and initial actor-store coherence.
- [x] M7. Simulator steps correspond to semantic steps under the bytecode/PC
  representation relation.  `SimulatorFrameObservation` and
  `SimulatorObservationRepresents` now make every frame's activation,
  operand stack, code address, PC, and decoded active/suspended semantic
  control explicit.  `SimulatorRefinementCertificate` states both weak
  instruction soundness and non-stuttering semantic-step completeness, plus
  exact full-speed handoff.  `SimulatorExecution.sound` lifts instruction
  soundness to arbitrary finite Simulator runs.  `V5.decodeAt` now gives a
  deterministic complete decoder for every live opcode in the local V5
  specification and rejects dead, corrupt, and truncated encodings.  A
  well-formed `V5.MethodArtifact` separates bytecode boundaries from the
  compiler-emitted semantic PC map and proves the generic frame decoder is
  defined exactly at in-range instruction boundaries.
  `CompiledArtifactAdmission` makes the refinement certificate mandatory for
  every installed compiler/Simulator pair and derives instruction refinement,
  finite-execution refinement, non-stuttering semantic completeness, and exact
  native resumption. `V5CompiledArtifactAdmission` instantiates this boundary
  with the V5 decoder without freezing a particular reflectively replaceable
  compiler or Simulator implementation into the language semantics.

## Optional garbage collection

- [x] G1. The base sequential heap has an executable unconditional
  strong-reference extractor for every runtime record category.  It includes
  references embedded in finite stores, message mirrors, captured closure
  context, and materialized closure syntax; `strongSuccessors` intersects the
  result with the live collectable domain.  Direct successors and every
  depth-indexed reachability iteration have exact membership theorems, contain
  only live objects, and are duplicate-free (`mem_strongSuccessors_iff`,
  `mem_strongReachabilityAt_iff`).
- [x] G2. Iteration through the number of live records has stabilized
  extensionally and is equivalent to the inductive reflexive-transitive
  closure of the unconditional strong-reference relation.  The executable
  result contains the live roots, is closed under strong edges, and is a
  subset of every other such closed set (`strongReachability_stabilized`,
  `mem_stronglyReachableReferences_iff_reachable`,
  `stronglyReachableReferences_least`).
- [x] G3. Ordinary objects have optional, disjoint `WeakArray` and `WeakMap`
  payloads.  Their distinctly named read/write operations are executable;
  successful writes install the exact updated payload and read back the
  written value.  Heap-wide weak-container validity makes every observed key
  and value live, is preserved by valid writes, and changing only weak payload
  is proved unable to change the unconditional strong graph.
- [x] I31. Weak-array elements do not retain targets and reclaimed cells are
  cleared atomically to `nil`.  Weak contents remain absent from the strong
  extractor, collection preserves array length, and
  `readWeakArrayCell_after_collection` gives the exact retained-or-`nil`
  result for every previously occupied cell.
- [x] I32. Weak-map keys are weak; values are conditionally strong exactly
  while map and key are reachable.  Conditional closure uses the two-premise
  ephemeron rule, and `lookupWeakMapEntry_after_collection_iff` proves that an
  entry survives exactly when both its key and value occur in the fixed point.
- [x] I33. Every retained weak-container reference resolves after collection
  (`collectHeap_weakContainersWellFormed`).
- [x] M8. Conditional reachability has the required least fixed point.  The
  executable iteration admits a WeakMap value exactly when both its map and
  key occur in the current approximation, stabilizes by the live-object-count
  bound, equals the inductive strong/ephemeron closure, and is contained in
  every root-containing set closed under those rules
  (`conditionalReachability_stabilized`,
  `mem_conditionallyReachableReferences_iff_reachable`,
  `conditionallyReachableReferences_least`).
- [x] M9. Collection preserves well-formedness using executable roots from
  finite Program tables, platform bindings, suspended syntax, evaluation and
  activation stacks, current control, actors, and explicit host/VM handles.
  The present conservative policy roots all installed runtime classes and
  actors; this discharges the formerly exposed class/stack adequacy premises
  without claiming class reclamation.  All five allocation frontiers remain
  unchanged and fresh, stack/control remain unchanged, and the resulting weak
  containers are valid when canonical `nil` is live
  (`WellFormed.collectHeap_wellFormed`,
  `SequentialWellFormed.collectGarbageFromRuntimeRoots_wellFormed`).
- [x] M10. The collecting semantics is a finite stuttering refinement of the
  base semantics modulo specified weak observations.  Every transition in a
  finite collecting execution is classified as either an exact top-level
  sequential step or a `CollectionStutter` using roots recomputed from that
  transition's source state.  Stack, control, allocation frontiers, retained
  classes, and retained unconditional record references agree literally;
  only weak observations may expose clearing/removal
  (`SequentialExecutionWithRuntimeCollection.refines_base_with_stutters`).

## PEG, elaboration, compilation, and metacircularity

- [x] I34. Accepted units have a successful PEG derivation, injective source
  identities, a statically well-formed AST, and a checkable annotated core.
  The checked path now includes the normalized 0.109 `G_NS` production table,
  concrete-tree semantic projection, the complete surface datatype domain,
  Newspeak semantic actions, structural source-node enumeration, stable
  retention, executable shape and annotated-core checks, and the composed
  `FrontEndDerivation`.  Successful identification is proved sort-correct and
  injective, retained identities are proved preserved, and complete front-end
  derivations are unique.  Recursive structural discovery installs object
  literals and class expressions throughout method, closure, initializer,
  pattern, tuple, cascade, and nested-class bodies. Both bodied and body-less
  mixin chains use the same image-level application fold at top level and in
  nested or expression-local classes. The executable finite certificate for
  `G_NS` is proved sound for the relational admissibility judgment; character
  predicates are erased only for that structural check, with a proof that all
  four certificate analyses are unchanged. Direct named classes derive
  physical/eager/lazy slots, explicit and synthesized methods, primary factories, closure and
  compound-literal artifacts, actor seeds, and recursively nested classes;
  object literal bodies have a complete image builder.
- [x] I35. Parser, elaborator, compiler, and Simulator components are ordinary
  mutable Newspeak objects, while admitted artifacts refine the fixed core
  semantics. `MetacircularComponents` selects four live ordinary objects and
  deliberately introduces no replacement transition: existing evaluation and
  reflection mutate them. `ParserArtifactAdmission`,
  `ElaborationArtifactAdmission`, and `CompiledArtifactAdmission` validate the
  artifacts obtained at use boundaries. The standard Newspeak grammar and
  complete elaborator construct these admissions directly.
- [x] M11. The full PEG core (empty, character, character-set, wildcard,
  nonterminal, sequence, ordered choice, greedy advancing repetition,
  lookahead, and capture) has a big-step recognition relation whose success
  forest and diagnostic failure offset are functional. Complete parses are
  unique (`PEGRecognizes.deterministic`, `PEGCompleteParse.unique`).
  Grammar admissibility is separately formalized by
  `PEGGrammarWellFormed`: defined references, absence of leading cycles, and
  non-nullable repetition operands.  Admissible complete parses remain unique.
- [x] M12. Static elaboration is deterministic.
  Binding, receiver classification, send construction, expression lists,
  patterns, clauses, statements, and superclass expressions are executable
  finite-fuel functions; successful expression and statement elaborations are
  already proved deterministic. Direct and recursively nested class Program
  derivation, structural artifacts, object literals, and both forms of mixin
  chain are deterministic; `FrontEndDerivation.deterministic` composes this
  with parsing, projection, and stable identification.
- [x] M13. Successful checked elaboration produces well-formed annotated core.
  The complete static gate checks declaration–mixin injectivity, every
  annotation reachable from the top-level core expression and from all
  installed method bodies, closures, local and instance initializer groups,
  pattern expansions, and deferred superclass/mixin messages, plus the
  top-level expression restriction against the actual derived Program. Its soundness
  theorem constructs `AnnotatedCoreValid` evidence
  (`completeSurfaceStaticOK_coreValid`).
- [x] M14. Compiled execution refines annotated-core execution.
  `CompiledProgramAdmission` connects one `AnnotatedCoreValid` expression to
  its ordinary top-level semantic entry and the initial Simulator state.
  `CompiledProgramAdmission.execution_refines_annotatedCore` lifts every
  finite compiled execution to a finite annotated-core execution ending in a
  represented configuration.

## Immediate next slice

1. Validate the currently shipped compiler/Simulator object pair against the
   mandatory V5 admission boundary as an implementation-verification project;
   replacements must provide the same certificate.
2. Strengthen actor packet-provenance invariants so every dequeued wake can be
   traced to its unique earlier settlement event.
