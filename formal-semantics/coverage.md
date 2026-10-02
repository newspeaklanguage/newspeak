# Normative coverage ledger

Normative basis: working Newspeak specification 0.109.  Status
labels mean:

- **Defined**: mathematical rules are present in the semantics document.
- **Scaffolded**: domains or judgments are present, but evaluation rules remain.
- **Pending**: not formalized yet.
- **Parameterized**: deliberately supplied by the Newspeak platform or host,
  with the required boundary behavior still to be specified.
- **Question**: the prose specification does not determine one observable case.

This ledger tracks semantic behavior, not merely grammar productions.

| Spec section | Feature | Status | Notes |
|---|---|---:|---|
| 3.1 | Objects, identity, class membership | Defined | Factory, object-literal, and canonical atomic-literal cases are explicit. |
| 3.1.1 | Deeply immutable values | Scaffolded | Primitive value cases and the greatest-fixed-point characterization are stated; explicit initialization bookkeeping and reflective effects remain. |
| 3.1.2 | Near, far, and promised eventual references | Defined | Actor-relative remote representation normalizes homeward far references, transports values, and preserves promise capabilities. |
| 3.2 | Classes, metaclasses, mixins, inheritance | Defined | Each evaluation creates a class and unique metaclass; applications share their instance-side mixin. |
| 3.3 | Enclosing objects, including relative/kth enclosing object | Defined | The relation is used directly by outer sends. |
| 3.4 | Messages and message mirrors | Scaffolded | Messages are defined; allocation/reification rules remain. |
| 3.5 | Methods and defining classes | Defined | Direct definition, unrestricted lookup, and defining class are defined. |
| 3.6 | Method, closure, and top-level activations | Defined | Method, closure, and top-level activation rules, per-frame current control, retained dead activations, and reflective continuation invocation are explicit. |
| 3.7 | Actors, heaps, mailboxes, turns, E-order | Defined | Disjoint mutable heaps, FIFO mailboxes, one active turn per actor, weak fairness, and causal-envelope delivery are explicit. |
| 3.8 | Top-level programs | Defined | The least top-level-expression predicate, activation allocation, and halting rule are explicit. |
| 4.1-4.2 | Lexing and surface PEG | Defined | A normalized 0.109 PEG is given explicitly, including lexical priority, reserved words, asynchronous sends, captures, deterministic ordered choice, greedy repetition, lookahead, termination conditions, and complete-input recognition. |
| 4.3 | Metadata association and reflective availability | Scaffolded | Before-pattern/header attachment and ordinary-comment preservation are formal; explicit mirror query constructors for metadata remain. |
| 5.1.1-5.1.6 | Numeric, Boolean, nil, string, symbol, tuple literals | Defined | Exact radix/fraction/exponent decoding, NFC/canonical atoms, and the specified tuple expansion are explicit; 0.109 has no character literals. |
| 5.1.7 | Closure literals and captured activation | Defined | Creation captures lexical/runtime state; value-selector invocation allocates a closure activation. |
| 5.1.8 | Pattern literals | Scaffolded | Wildcard, literal, nested, and keyword patterns elaborate to ordinary sends; the unspecified variable-pattern constructor is isolated as a program parameter. |
| 5.1.9 | Object literals | Defined | Each evaluation allocates a fresh implicit class, metaclass, and instance while sharing the literal's mixin. |
| 5.2-5.3 | `self` value and parentheses | Defined | `self` reduces to the activation's current instance; elaboration preserves parenthesized self-send authority. |
| 5.4 | Receiver/argument order and message construction | Defined | Frames enforce receiver first and arguments left-to-right. |
| 5.4.4 | Cascades | Scaffolded | Elaboration is stated; proof of single receiver evaluation remains. |
| 5.4.4 | Chains | Pending | Marked unimplemented/proposed by the spec; tracked, not silently included. |
| 5.5 | Ordinary sends and public lookup | Defined | Protected declarations are barriers; private declarations are transparent. |
| 5.6 | Asynchronous sends and promise settlement | Defined | Receiver/argument order, immediate result promises, routing, fulfillment, breaking, pipelined sends, communication failure, and E-order are explicit. |
| 5.7 | Implicit receiver sends | Defined | Lexical binding precedes inherited self lookup. Activation-local dispatch needs completion. |
| 5.8 | Self sends | Defined | Reduced to depth-zero outer dispatch, not to ordinary send. |
| 5.9 | Outer sends and protected/private access | Defined | Private dispatch is lexical; public/protected dispatch remains virtual. |
| 5.10 | Super sends | Defined | Lookup starts above the activation's current class. |
| 5.11 | Class declarations and class factories | Defined | Class identity is fresh per evaluation; synthesized getters memoize nested classes per receiver. |
| 6.1 | Inheritance clause evaluation | Defined | The superclass is fixed at class creation; its message template is evaluated later with factory parameters. |
| 6.2 | Mixin application | Defined | Operands evaluate left-to-right; the result shares the source mixin and copies its enclosing object. |
| 6.3 | Class initialization order | Defined | Rules sequence superclass message/initializer, own or applied mixin initialization, and factory return. |
| 6.3.1 | Default/protected/public/private access | Defined | Top-level classes are always public. |
| 6.3.2 | Mutable/immutable, sequential/simultaneous slots | Defined | Physical writes bypass setters; simultaneous groups install all `Past` futures before source-order resolution. |
| 6.3.3 | Lazy slots | Defined | Nil is the sentinel; reads force and cache directly, nil results re-force, and mutable setters may reset. |
| 6.3.4 | User-defined methods | Defined | Dispatch allocates an activation, initializes sequential locals, and executes the body. |
| 6.4 | Modules and module definitions | Defined | Creation-site provenance defines module definitions and instances; module definitions are primitive values. |
| 7.1, 7.3 | Expression statements and sequences | Defined | Frames give source-order execution and method/closure-specific default results. |
| 7.2 | Local and non-local returns, `cannotReturn` | Defined | Return targets, continuation severing, non-local transfer, and failed return are explicit. |
| 8.1 | Compilation units | Defined | Language-id selection captures a reified front-end image; ordinary parser, elaborator, and compiler sends must produce a verified annotated core and refining artifact. |
| 8.2 | Mirror capabilities, population inspection, atomic install, object class change | Defined | Exact-class instance and exact-mixin application snapshots, capability checks, transactions, and reconciliation are explicit. |
| 8.2 | Activation, continuation, and debugger reflection | Defined | Activation fields and live control are inspectable; stack snapshots, push/pop/copy template operations, pause-token guarded replacement, resumable transfer, and ordinary-VM resumption are explicit. |
| 8.3-8.3.1 | Platform and VM mirror | Parameterized | Required protocols and failure boundary must be stated. |
| Platform | `WeakArray` and `WeakMap` | Defined | Weak-array elements do not retain their targets and clear to nil; weak-map keys are weak and their values are conditionally strong under ephemeron reachability. |
| Platform | Metacircular front ends and compiler | Defined | Parser, elaborator, and compiler components are ordinary Newspeak objects changed by existing reflection or mutation; decoders, artifact loading, primitive stepping, and concrete compiler refinement form the explicit VM boundary. |
| 8.4 | Application entry | Defined | Entry is an ordinary `main:args:` send in a top-level activation. |
| 8.5 | Aliens and expats | Parameterized | Actor isolation is defined; synchronous alien callbacks and expat lifetime constraints remain platform obligations. |
| 8.6 | Resumable exception library | Defined | Internal failures are reified and sent `signal`; the original frames remain live, and a formal stack-template operation removes the handler/debugger suffix and resumes the protected send with a chosen value. Catch/pass policy remains ordinary library code. |

## Specification questions exposed by formalization

1. **Current class after lexically bound private outer dispatch.** The selected
   method is fixed by a lexical class declaration, but the general activation
   rule derives `current class` from the receiver's dynamic class and selector.
   A subclass can define the same selector, making those two descriptions select
   different classes.  The draft semantics uses the actual application of the
   lexical mixin from which the private method was selected.
2. **DNU lookup start for a failed super send.** The spec says the
   `doesNotUnderstand:` method "defined for S" is invoked, which implies lookup
   starts at `S`, while its receiver remains `self`.  The draft makes that choice
   explicit.
3. **Lexical activation-slot access.** An implicit send bound to a parameter or
   local is described as a send to its activation.  The accessibility of the
   activation's synthesized accessors is not stated.  The intended reading
   appears to be capability-safe lexical access independent of class-member
   access modifiers.
4. **Malformed class hierarchies after reflection.** The base rules assume a
   finite superclass chain ending in `Top`.  The reflective transaction rules
   must say whether cyclic hierarchy changes are rejected atomically.
5. **Resolution order for simultaneous slots.** The specification requires all
   `Past` futures to be installed before they are resolved, but does not state
   an observable forcing order when their initializers have effects.  The draft
   chooses source order to keep the sequential machine deterministic.
6. **Variable-pattern construction.** The pattern grammar admits `?x`, but the
   specification gives no equivalent expression or required constructor
   protocol for the corresponding named pattern.  The draft isolates this one
   case as `P.patternVariable`; the other pattern forms are fully expanded.
7. **Sends to broken promises.** The specification explicitly leaves the
   meaning of broken promises open.  The draft propagates the represented
   exception to the promise returned by a dependent asynchronous send; no
   application message is delivered.
8. **Promise transport.** Literal application of the general remote-
   representation clause would wrap a promise in a far reference to the
   promise object, defeating eventual-send pipelining.  The draft instead
   treats promise identities as monotonic transferable capabilities, analogous
   to the no-proxy-chain rule for far references.
9. **Value transfer across address spaces.** The specification permits shared
   values in one address space and requires copies across address spaces, but
   does not yet define the address-space construct.  The draft parameterizes
   `valTransfer` by sharing or immutable graph copying; the reflective VM layer
   must choose between them for each actor pair.
