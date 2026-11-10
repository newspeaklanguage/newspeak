# Prolog bridge coverage

This ledger is generated from the labels in the LaTeX sources and the
annotations on the checked clauses, plus the checked disposition of every
numbered equation. No equation is left implicit or unclassified.

Rules: **86 / 86** represented.
Equations: **291 / 361** encoded as clauses.

## Named rules

- [x] `Actor-Sequential`
- [x] `Async-Receiver`
- [x] `Async-Return`
- [x] `Class-Commit`
- [x] `Class-Super`
- [x] `Closure-Invoke-NonTail`
- [x] `Closure-Invoke-Tail`
- [x] `Closure-New`
- [x] `Closure-Value`
- [x] `DNU`
- [x] `Defining-Here`
- [x] `Defining-Super`
- [x] `Defining-Top`
- [x] `Enc-One`
- [x] `Enc-Step`
- [x] `Enc-Zero`
- [x] `Factory-New`
- [x] `Finish-Halt`
- [x] `Finish-Resume`
- [x] `GC-Collect`
- [x] `GC-Lift`
- [x] `Implicit-Activation`
- [x] `Implicit-Class`
- [x] `Implicit-Literal`
- [x] `Implicit-Self`
- [x] `Init-Applied-Mixin`
- [x] `Init-Super`
- [x] `Invoke-NonTail`
- [x] `Invoke-Tail`
- [x] `Mirror-Derive`
- [x] `Mirror-Inspect`
- [x] `Mixin-Commit`
- [x] `Network-Deliver`
- [x] `Object-Commit`
- [x] `Object-Super`
- [x] `Outer-Missing`
- [x] `Outer-Private`
- [x] `Outer-Protected`
- [x] `Prot-Hit`
- [x] `Prot-Super`
- [x] `Prot-Top`
- [x] `Pub-Hit`
- [x] `Pub-Protected-Barrier`
- [x] `Pub-Super`
- [x] `Pub-Top`
- [x] `RR-Far-Home`
- [x] `RR-Far-Pass`
- [x] `RR-Near-Far`
- [x] `RR-Promise`
- [x] `RR-Same`
- [x] `RR-Value`
- [x] `Reflection-Commit`
- [x] `Reflection-Reject`
- [x] `Resolve`
- [x] `Return-Cannot`
- [x] `Return-Transfer`
- [x] `Return-Value`
- [x] `Route-Broken`
- [x] `Route-Fulfilled`
- [x] `Route-Pending`
- [x] `Route-Target`
- [x] `Runtime-Error-Signal`
- [x] `Self-Value`
- [x] `Send-First-Arg`
- [x] `Send-Missing`
- [x] `Send-No-Args`
- [x] `Send-Public`
- [x] `Send-Receiver`
- [x] `Settlement-Packet-Dequeue`
- [x] `Super-Hit`
- [x] `Super-Missing`
- [x] `Super-Object-Error`
- [x] `Super-Top-Error`
- [x] `Throw-Signal`
- [x] `Top-Halt`
- [x] `Turn-Break-Local`
- [x] `Turn-Break-Remote`
- [x] `Turn-Fulfill-Local`
- [x] `Turn-Fulfill-Remote`
- [x] `Turn-Start`
- [x] `U-Here`
- [x] `U-Super`
- [x] `U-Top`
- [x] `VM-Primitive`
- [x] `Wake-Broken`
- [x] `Wake-Fulfilled`

## Equation dispositions

- **abstract-contract**: 10
- **deferred**: 0
- **encoded**: 291
- **term-representation**: 51
- **theorem-only**: 9

## Numbered equations

| Equation | Disposition | Rationale |
|---|---|---|
| `eq:activation-class-edit-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-command-fold` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-continuation-edit-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-field-effects` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-local-edit-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-parameter-edit-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-transaction-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:activation-uncontinuable-edit-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:actor-configuration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:actor-fairness` | `abstract-contract` | Fair scheduling is a trace-level assumption rather than a machine transition. |
| `eq:actor-heap-view` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:actor-run-state` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:actor-seed` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:actor-stack-snapshot` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:admissible-garbage-set` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:after-mixin` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:after-super` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:all-instances-of` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:allocate-class` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:annotated-core-checker` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:annotated-core-roots` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:annotated-core-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:annotated-program-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:application-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:application-entry` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:application-indices` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:application-object` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:applied-own-init` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:apply-source-commands` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:argument-continuations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:artifact-domain` | `term-representation` | Artifacts and certificates are represented by tagged terms. |
| `eq:artifact-validity` | `abstract-contract` | Artifact validity is an admission relation supplied at the VM boundary. |
| `eq:ast-tree-projection` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:async-frames` | `term-representation` | The asynchronous continuation frames are represented by tagged Prolog terms. |
| `eq:async-receiver-continuations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:atom-canonicality` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:atom-payload` | `term-representation` | Atomic literal payloads are represented directly by tagged terms. |
| `eq:binding-equivalence` | `theorem-only` | This is the bind-equals-scan proposition proved in Lean. |
| `eq:body-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:body-own-init` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:body-results` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:bootstrap-basis` | `abstract-contract` | The bootstrap basis is an explicit trusted starting assumption. |
| `eq:cached-nested-class-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:callee-continuation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:cascade-expansion` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-chain` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-command-projections` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-construction-frames` | `term-representation` | Class-construction frames are represented directly by tagged terms. |
| `eq:class-enclosing-object` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-forms` | `term-representation` | Normalized class forms are represented directly by tagged terms. |
| `eq:class-membership-depth` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-object-command-folds` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-object-heap-effects` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-origin` | `term-representation` | Class creation provenance is represented by tagged origin terms. |
| `eq:class-origin-declaration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-scan` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:class-with-enclosing-object` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:closure-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:closure-invocation-data` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:code-command-projection` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:compilation-unit` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:compilation-unit-projection` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:compound-expression-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:concrete-tree-domain` | `term-representation` | Concrete trees and forests are represented directly by tagged Prolog terms. |
| `eq:configuration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:continuation-command-fold` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:continuation-transfer-count` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:control-command-projections` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:control-location-domain` | `term-representation` | Control locations are represented by tagged terms. |
| `eq:copy-stack-frame-segment` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:core-expressions` | `term-representation` | Core expressions are represented directly by tagged Prolog terms. |
| `eq:create-actor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:current-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:current-slot-operations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:debug-activation-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:debug-frame-image` | `term-representation` | Debug frame images are represented by tagged record terms. |
| `eq:debug-stack-image-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:debug-stop-reasons` | `term-representation` | Debugger stop reasons are represented by tagged terms. |
| `eq:debugger-command-fold` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:debugger-command-projection` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:declaration-derivation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:declaration-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:declares` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:decode-control-image` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:definedness-notation` | `term-representation` | Definedness is represented by explicit some/none terms. |
| `eq:dependents` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:derived-auxiliary-indexes` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:derived-mixin-entry` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:derived-program-indexes` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:direct` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:distinguished-platform-classes` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:e-order-eligibility` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:elaborated-send-construction` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:elaboration-context` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:elaboration-context-extension` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:elaboration-function-signatures` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:elaboration-helper-functions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:emit-packet` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:empty-body` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:event-ledger` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:eventual-identities` | `term-representation` | The identity domains are represented by tagged Prolog terms. |
| `eq:eventual-tables` | `term-representation` | The eventual-routing tables are represented as tagged finite-store fields. |
| `eq:eventual-target` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:exception-reification` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:expression-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:factory-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:factory-selector` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:failed-reflection-validations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:frame-control-domain` | `term-representation` | Frame control states are represented by tagged terms. |
| `eq:frame-current-term-and-location` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:frame-grammar` | `term-representation` | Continuation frames are represented directly by tagged terms. |
| `eq:fresh-installed-activations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-anonymous-application-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-application-identities` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-artifact-admission` | `abstract-contract` | Artifact admission is an explicit trusted-boundary certificate. |
| `eq:front-end-bodied-mixin-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-bodied-prefix` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-body-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-bodyless-mixin-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-bodyless-prefix` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-class-body-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-default-superclass` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-image` | `term-representation` | The captured front-end image is represented by a tagged record term. |
| `eq:front-end-message-template` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-mixin-fold` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-named-application-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-object-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-phase-behavior` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-reflective-change` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:front-end-uniqueness` | `theorem-only` | This is a determinism proposition proved in Lean. |
| `eq:front-end-value-decoders` | `term-representation` | Decoder services are represented as fields of a service term. |
| `eq:gc-all-instances-effect` | `theorem-only` | This equation states an observable consequence of collection. |
| `eq:gc-clear-weak-payload` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-control-state` | `term-representation` | Collector control states are represented by tagged terms. |
| `eq:gc-mixin-applications-effect` | `theorem-only` | This equation states an observable consequence of collection. |
| `eq:gc-new-identities` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-prune-store` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-pruned-actor-heap` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-reachability` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-reference-payload` | `term-representation` | Reference payload variants are represented by tagged terms. |
| `eq:gc-reference-store` | `term-representation` | The collectable reference store is represented as a finite-store term. |
| `eq:gc-roots-and-successors` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-safety` | `theorem-only` | These are collector safety propositions proved in Lean. |
| `eq:gc-strong-payload` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:gc-underlying-transition` | `abstract-contract` | The underlying actor/reflection transition is a modular parameter. |
| `eq:gc-weak-array-effect` | `theorem-only` | This equation states an observable consequence of collection. |
| `eq:gc-weak-map-effect` | `theorem-only` | This equation states an observable consequence of collection. |
| `eq:gc-wrapper-state` | `term-representation` | The GC wrapper state is represented by a tagged record term. |
| `eq:heap-records` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:home-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:implicit-binding-annotation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:implicit-judgment` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:implicit-receiver` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:inheritance-error` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:inheritance-error-step` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:init-class` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:init-frames` | `term-representation` | Initialization continuation frames are represented directly by tagged terms. |
| `eq:init-group-sequential` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:init-group-simultaneous` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:init-groups-empty` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:init-sequential` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:instance-initializer-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:internal-sequence` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:keyword-pattern-expansion` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:language-registry` | `term-representation` | The registry is represented by a tagged record term. |
| `eq:lazy-read` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:lex-ancestor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:lex-depth` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:lexical-binding` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:live-activation-control` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:live-activation-order` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:live-activation-record-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:live-activation-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-declaration` | `term-representation` | Local declaration variants are represented directly by tagged terms. |
| `eq:local-declaration-sequence` | `term-representation` | The recursive sequence is represented directly by Prolog lists whose elements are sequential or simultaneous local-declaration-group terms. |
| `eq:local-group-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-init-commit` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-init-empty` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-init-nil` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-init-start` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-simultaneous-expansion` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-simultaneous-install` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-simultaneous-start` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:local-slot-operations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mark-uncontinuable` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:materialize-stack-template` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:message-evaluation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:message-template-domain` | `term-representation` | Message templates are represented directly by tagged terms. |
| `eq:message-transfer` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:metacircular-compilation-pipeline` | `abstract-contract` | The compiler/parser service pipeline is intentionally supplied by the active language image. |
| `eq:metadata-association` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:metadata-attachment` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:metadata-trivia-gap` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:method-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:method-definition` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:method-formals` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:method-owner` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:method-projections` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mirror-query-grammar` | `term-representation` | Mirror queries are represented directly by tagged terms. |
| `eq:mirror-query-result` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mirror-query-target` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mirror-record` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mirror-target-containment` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mirror-targets-rights` | `term-representation` | Mirror targets and rights are represented by tagged terms. |
| `eq:mixin-applications` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mixin-initializer` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mixin-initializer-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mixin-record` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mixin-right` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:mixin-start` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:module-definition` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:module-instance` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:nearest-application` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:nested-class-cache` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:nested-declaration-keys` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:new-top-activation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-action-abbreviation` | `term-representation` | The abbreviation is represented by the same action-application term. |
| `eq:newspeak-action-sequence-helpers` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-compound-expression-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-declaration-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-declaration-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-expression-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-expression-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-inheritance-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-lexical-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-literal-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-literal-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-message-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-message-sequence-names` | `term-representation` | The equation defines action-name constants represented as atoms. |
| `eq:newspeak-pattern-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-punctuation-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-send-fold-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-structural-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-type-actions` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-type-pattern-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-type-peg` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-type-word-set` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:newspeak-word-tokens` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:nonempty-body` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:number-decoding` | `abstract-contract` | Numeric decoding is supplied by the platform primitive boundary. |
| `eq:object-inheritance-error` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:object-literal-descriptor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:object-literal-enclosing-object` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:object-literal-frame` | `term-representation` | The object-literal continuation frame is represented by a tagged term. |
| `eq:object-slot-command-fold` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:object-top-superclass-error` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:ordinary-service-call` | `abstract-contract` | Ordinary service invocation is supplied by the host object protocol. |
| `eq:own-slots` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:packet-grammar` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:patched-source-candidate` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:pattern-binding` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:pattern-components` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:pattern-elaboration` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:pattern-step` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:pause-actor-effect` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-action-map` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-admissibility-certificate` | `term-representation` | Certificate records are represented as terms; their checker is encoded separately. |
| `eq:peg-atomic-recognition` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-certificate-soundness` | `theorem-only` | This is a soundness proposition proved in Lean, not an operational definition. |
| `eq:peg-complete-parse` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-derived-notation` | `term-representation` | The equation introduces derived PEG notation represented by existing constructors. |
| `eq:peg-expression-domain` | `term-representation` | PEG expressions are represented directly by tagged Prolog terms. |
| `eq:peg-grammar-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-nonterminal-capture` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-repetition-lookahead` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:peg-sequence-choice` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:pop-stack-frames` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:prepare-reflection` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:primary-factory-body` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:private-method` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:program-definition` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:promise-settlement` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:promote-demote-frame-control` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:push-stack-frame` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:receiver-continuations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reconcile-nested-cache` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reconcile-object-layout` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reconciliation-phases` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-authorized` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-command-footprint` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-command-grammar` | `term-representation` | Reflection commands are represented directly by tagged terms. |
| `eq:reflection-command-right` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-command-target` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-conflict` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-diagnostic-candidates` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-error-index-sets` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-failure` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-failure-domain` | `term-representation` | Reflection failure values are represented by tagged terms. |
| `eq:reflection-location-overlap` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-validation-kinds` | `term-representation` | Validation kinds are represented by tagged terms. |
| `eq:reflection-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflection-version-observation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-actor-isolation` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-class-chain-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-class-graph-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-class-record-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-continuation-transfer` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-descriptors` | `term-representation` | Reflective descriptor variants are represented by tagged terms. |
| `eq:reflective-object-record-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-object-slot-write` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-object-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-record-id-sets` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:reflective-reelaboration` | `abstract-contract` | Re-elaboration invokes the active parser/compiler services as an explicit relation parameter. |
| `eq:reflective-step` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:remote-debugger-component-step` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:replace-current-actor-stack` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:replace-paused-actor-stack` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:replace-resume-paused-actor-stack` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:request-construction` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:request-grammar` | `term-representation` | Requests are represented directly by tagged terms. |
| `eq:request-resolution` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:resolve-stack-template-keys` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:resume` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:resume-exception-stack-template` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:resume-paused-actor-full-speed` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:retire-removed-stack-activations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:return-target` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:run-program` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:runtime-identities` | `term-representation` | Runtime identity sorts are represented by distinct tagged terms. |
| `eq:scope-chain` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:self-send-derived` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:setter-expansion` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:simulator-step-correspondence` | `theorem-only` | This is the admitted compiler/Simulator correspondence proposition. |
| `eq:simultaneous-expansion` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:slot-frames` | `term-representation` | Slot initialization frames are represented directly by tagged terms. |
| `eq:slot-group` | `term-representation` | Slot declaration groups are represented directly by tagged terms. |
| `eq:slot-layout` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:slot-operations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:source-patch` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:source-to-annotated-core` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:stable-ast-identification` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:stable-ast-identity-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:stack-control-image` | `term-representation` | Stack control images are represented by tagged record terms. |
| `eq:stack-template-domain` | `term-representation` | Stack templates are represented by tagged terms. |
| `eq:stack-template-record-locations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:statement-continuations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:statement-start` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:static-binding-function` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:static-well-formedness-components` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:structural-reference-extractor` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:surface-context-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:surface-declaration-domain` | `term-representation` | Surface declarations are represented directly by tagged terms. |
| `eq:surface-expression-domain` | `term-representation` | Surface expressions are represented directly by tagged terms. |
| `eq:surface-message-folds` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:surface-message-pattern-domain` | `term-representation` | Surface message patterns are represented directly by tagged terms. |
| `eq:surface-receiver-kind` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:target-application` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:top-level-expression` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:top-superclass-error` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:tuple-expansion` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:tuple-platform-bindings` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:tuple-step` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:value-transfer-contract` | `abstract-contract` | Value transfer is an explicitly platform-supplied relation. |
| `eq:variable-pattern-parameter` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:vm-family` | `term-representation` | VM family/cohort values are represented by tagged terms. |
| `eq:vm-object-store` | `term-representation` | VM object stores are represented by finite-store record terms. |
| `eq:wake-all` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:weak-array-operations` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:weak-container-records` | `term-representation` | WeakArray and WeakMap records are represented by tagged terms. |
| `eq:weak-container-validity` | `encoded` | Represented by one or more checked Horn clauses. |
| `eq:weak-map-operations` | `encoded` | Represented by one or more checked Horn clauses. |
