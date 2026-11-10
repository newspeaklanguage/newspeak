# Newspeak in SpecTec

This is the start of a **LaTeX-first transcription**, not a translation of the
Lean or Prolog implementations. Its source is `../newspeak-semantics.tex` and
that document's included files. The existing LaTeX remains authoritative
during the migration. Nothing in this directory claims that the whole
language has already been converted or that Rocq equivalence has been proved.

The initial slice covers sections 4–6.4: direct selection; unrestricted,
public, and protected lookup; the independent defining-class judgment;
superclass membership/depth; lexical ancestry/depth; repeated mixin
applications; enclosing receivers; private selection; ordinary, outer, self,
super, and elaborated implicit dispatch; static binding; and the ECOOP-style
class scan and implicit receiver. DNU **requests** are retained faithfully,
including their lookup start class.

The runtime slice now adds the four full base heap records, seven-field
methods, mixin/initializer/factory descriptors, and lookup projections derived
from the runtime heap. It transcribes allocation-bearing DNU and most of
section 7: left-to-right sends, selected-method capture, closures, tail/non-tail
activation allocation, sequential local initialization, bodies, normal
completion, and explicit/non-local return with dependent invalidation.
Section 8 now adds class/metaclass construction, inheritance validation,
mixin application, deferred message evaluation, primary-factory instance
allocation, superclass/mixin initialization, sequential/simultaneous slot
groups, simultaneous locals, direct slot primitives, lazy getters, and
per-receiver nested-class caches. It is **not yet the whole sequential
language**: remaining expression forms, platform/exception boundaries,
front-end derivation, and the no-method-home return boundary remain pending.

## Reading the source

Read these in order:

1. [00-domains.spectec](00-domains.spectec): identity tags, finite-map operations,
   lookup state views, direct selection, and result domains.
2. [01-lookup.spectec](01-lookup.spectec): the named lookup rules and finite
   superclass chains.
3. [02-lexical.spectec](02-lexical.spectec): lexical and enclosing-object
   operations, nearest applications, and static binding.
4. [03-dispatch.spectec](03-dispatch.spectec): message dispatch.
5. [04-runtime-domains.spectec](04-runtime-domains.spectec): full base records,
   core expression/descriptor domains, and runtime-to-lookup projections.
6. [05-machine-support.spectec](05-machine-support.spectec): configurations,
   allocation, DNU, closures, locals, body results, and return bookkeeping.
7. [06-machine.spectec](06-machine.spectec): sequential transition rules.
8. [07-class-support.spectec](07-class-support.spectec): class allocation,
   factory descriptors, layouts, initializer records, and simultaneous expansion.
9. [08-class-machine.spectec](08-class-machine.spectec): class construction,
   initialization, slots, lazy getters, and nested-class caching.

`syntax` defines a domain; `var` declares a metavariable; `def $name` gives a
function signature followed by its equations. A `relation` declares a
judgment's shape. Each `rule` starts with its conclusion and then lists
premises prefixed by `--`. `eps` is an empty sequence; absent scalar results
have explicit typed constructors (`NOMETHOD`, `NOCLASS`, `NODECL`, `NOSCOPE`,
or `NOINDEX`). `=/=` is inequality; `/\` is conjunction.

The `;; @equation`, `;; @rule`, and `;; @partial` annotations are exact LaTeX
origin labels. [COVERAGE.md](COVERAGE.md) lists **every** equation and named
rule, including the unconverted ones. `manifest.json` records source hashes.
Coverage is an audit of transcription, not a proof of equivalence.

## State-view boundary

The lookup views are explicit projections, not simplified replacement
definitions of the complete program or heap. The runtime modules now define
the full four base heap records and their lookup projections. Bodies,
physical slots, nested-class caches, continuation links, and captured closure
data are retained. The projection/correspondence theorem is still an obligation.

| View field | LaTeX source |
| --- | --- |
| `methodview.ID/SELECTOR/ACCESS/OWNER` | `i_f/s/alpha/K` of the full method |
| `mixinview.DECL/METHODS` | `K/phi` of `P.mixin(M)` |
| `classview.MIXIN/SUPER/ENCLOSING` | `M/S/eo` of `H(C)` |
| `activationview.RECEIVER/CURRENT/SCOPES` | current instance/current class/lexical environment of `H(a)` |
| `lookupProgram.TOP/OBJECT` | distinguished `P.platform` class entries |
| Other `lookupProgram` maps | corresponding maps in the program definition |
| `lookupHeap.CLASSES/ACTIVATIONS` | projected typed heap stores |
| `lookupHeap.TYPEOF` | graph of `classOf_H` for live object references |

`methodview` remains a partial projection, alongside the complete `fullmethod`.
`INVOKE` selects a method view; request resolution immediately recovers and
checks the **full selected method**, which `CALLMETHOD` then carries, including
its body. A later program edit does not cause invocation to fetch another body.
`TYPEOF` is derived from the actual heap records, including fresh metaclasses,
not an independently mutable class assignment. Finite maps have unique keys;
program coherence, live references, and finite acyclic class/lexical chains
are inherited from well-formed full states. Their full SpecTec validity
judgments have not yet been transcribed.

`runtimeProgram` is explicitly an operational projection of P, not its complete
source image: PEG/source ASTs, source units, actor seeds, and front-end metadata
are still pending. The base heap's message mirrors support DNU; authority-bearing
mirrors, weak stores, and other reflection/GC extensions are not yet present.
`NOCLASS`/`NOCONT` represent the nil current class/home of a top activation,
without inventing a nil class or activation record. Top activations are omitted
from the lookup activation view: its class-context operations are inapplicable
at top level, while ordinary sends do not require that view entry.

The operational program now also stores two explicit **derived elaboration
annotations**: `FUTUREEXPRESSIONS` contains the lexical core send denoting
PastFuture in each activation declaration, and `LOCALTHUNKS` gives each eager
simultaneous local's stable closure declaration identity. These transcribe the
`e_F`/`[e]` annotations required by the LaTeX expansions; they are not new
runtime authority or global PastFuture shortcuts. Their derivation from the
full source AST remains a front-end obligation. Slot declarations already
carry their thunk identities explicitly. Empty/non-eager groups do not require
a PastFuture annotation. The factory primitive likewise accepts **core
parameter expressions**, evaluates them as sends, then allocates the instance;
it does not silently read the parameter map instead.

## Transcription choices

- Identity domains use distinct constructors: SpecTec types are structural,
  so different aliases of `nat` alone would not enforce disjointness.
- Hit/barrier rules make `C != Top` explicit. This exposes the LaTeX
  invariant that `Top` has no methods and agrees with the existing Lean rules;
  it does not change lookup on well-formed states.
- Disjunctive premises become separately named cases with the same LaTeX
  origin. No first-applicable-rule priority is introduced.
- Chain, scan, and other graph judgments are inductive relations. There is
  no arbitrary fuel bound in the specification. Finite derivations witness
  the relevant chains; the regression driver's depth limit is test-only.
- `appIndices` uses an increasing sequence to represent the finite set.
  Its first element is its minimum, including with repeated applications.
- Generic finite-map lookup returns a zero-or-one-element sequence. The
  defining equations ensure this cardinality. Typed adapters expose scalar
  partial results without confusing them with empty argument lists.
- `Enc-One` deliberately uses the supplied current class's enclosing object,
  not an application recomputed from the dynamic receiver class.
- Functions have one signature; different operations have different names.
  No name is overloaded by arity.
- Allocation makes a fresh-identity choice, as in the LaTeX, rather than imposing
  a counter/minimum policy. Determinism must therefore be stated modulo fresh
  identity renaming. The optional GC overlay must later constrain freshness
  against retired identities too.
- Dependents are computed by finite-set growth to the least predecessor-closed
  set, including off-stack activations. There is no arbitrary semantic fuel.
- `textConcatenate` is an explicit pure primitive denoting Unicode-scalar
  sequence concatenation; this SpecTec pin has no native text-concatenation
  operator. Its backend implementation is an obligation, **not** an opaque
  Newspeak-language operation. Zero/one-argument value selectors reduce with
  the upstream evaluator; arbitrary-arity closure selector evaluation awaits
  this primitive's implementation. The specification has no arity bound.
- `TRANSFER NOCONT` for a closure created outside any method needs the exception
  boundary treatment. The current return rules do not read a fictitious nil
  activation; `Return-Cannot` is marked partial in the ledger for this reason.
- Class-side factory synthesis and its annotated parameter sends remain a
  front-end obligation (`eq:primary-factory-body` is partial). Class allocation
  checks the class-side method's public access and matching signature; full
  program well-formedness must also establish that it is the synthesized body.

### Application-local storage (corrected October 12, 2026)

The original `eq:slot-layout` appended declaration IDs without qualifying them
by their class applications. The author confirmed that each application owns
separate storage. The LaTeX, Lean, Prolog, and this transcription now use
`PHYSICALSLOT C slot` for cells and `NESTEDCACHE C D` for nested-class caches.
Accessors, initializers, and lazy getters use the activation's **selected**
application, not the most-derived receiver class. Deferred store frames capture
the qualified address before evaluating the initializer.

Regressions allocate one object with two applications of the same stateful
mixin and test disjoint layouts, independent ordinary/lazy cells, selected-class
access, initializer addresses, and independent nested-class caches. This resolves
the reported inconsistency; a whole-language correspondence proof remains pending.

## Build and test

The checker is pinned to the upstream Wasm SpecTec revision in
`toolchain.json`. This pin provides the declarative checker and mathematical
renderer; **it does not contain a Rocq backend**. The proof-generating branch
still needs to be selected and tested before promising Rocq output.

From this directory:

```sh
python3 tools/bootstrap.py             # downloads/builds only in .toolchain
python3 tools/check_sources.py --write # refresh after source or LaTeX changes
python3 tools/build.py
```

The bootstrap does not update `~/.opam`, shell startup files, or system
packages. On ARM macOS it also builds private static GMP when needed;
other platforms require a recent opam and existing GMP/pkg-config.
Direct package versions are pinned; transitive opam dependencies are not yet
locked, so bootstrap dependency resolution is not fully reproducible yet.
Inside the Codex sandbox, Apple's compiler may need permission for its cache
and architecture queries; a normal terminal build does not have that sandbox.

The build checks the source, its binding-premise transformation, and the full
upstream intermediate-language pass pipeline, runs provenance-checker unit tests, and runs ground
regressions over **the actual SpecTec IL**. Regressions exercise access
barriers, private transparency, defining class, static binding, repeated
application indices, ordinary dispatch, super lookup starts, and both root
errors. Runtime regressions also cover DNU access/payload/freshness, metaclasses,
method-body capture across a program edit, closure scope inheritance/shadowing,
tail/non-tail calls, source-order evaluation, local initialization and writes,
body results, completion, non-local return, and off-stack invalidation.
Construction tests cover enclosing objects, fresh metaclasses, inherited/lazy
physical slots, deferred message order, both mixin selector mismatches,
initializer activation/current-class selection, simultaneous installation
before resolution, lazy re-entry without a sentinel, and receiver-specific
caches. A finite trace witness checks factory allocation through initializer
completion and factory return; a negative trace rejects skipping initialization.
They include negative queries and reject multiple applicable rules.
The limited ground test driver is not a general interpreter, not a proof,
and does not claim to test all enclosing/implicit-dispatch derivations.
It evaluates declarative IL directly. The binding-premise transformation is
typechecked separately, not assumed to preserve behavior merely because its
output typechecks. Backend correctness remains an explicit proof obligation.
Explicit typed result constructors also avoid upstream optional-iteration
reduction quirks; the specification does not rely on that evaluator behavior.

One pinned evaluator bug required a **test-harness-only** workaround: its
known-suffix list matcher splits at suffix length instead of total length minus
suffix length (`src/il/eval.ml`, right-`ListE` `CatE` case). The regression driver
corrects that structural match and has singleton/three-entry/negative tests.
The upstream compiler and generated semantics are unchanged; stack growth is
still rightward. `resumeStack` uses equivalent head recursion to avoid the bug
inside upstream function evaluation. Value tests now reject unresolved calls,
even if actual and expected expressions happen to be identical. This harness
workaround is not a proof of the checker or future Rocq backend.

Outputs in ignored `build/` are `newspeak.generated.tex` (a mathematical
fragment, not a replacement standalone document), `newspeak.ast`, the
pass-normalized `newspeak.mechanization.ast`, and their hash report.
Generation is repeated and compared byte-for-byte, also from a different
source-directory path. The normalized AST is not itself Rocq code.

## Remaining migration

Next: remaining expressions (including object literals), tuples, patterns and
platform/exception boundaries; full-state
validity and source-image records; actors; reflection/debugging; the optional
GC/weak-reference overlay; PEG/AST/elaboration and metacircular front ends;
and theorem statements. `COVERAGE.md` is the exhaustive checklist.

Actors and GC must remain genuinely relational where the LaTeX admits
choices. The Wasm-specific interpreter backend will not be used to impose a
deterministic execution order on Newspeak. Once a compatible Rocq backend is
pinned, the first proof target is lookup determinism and correspondence;
generated files must be regenerated, never hand-edited.
