# Incremental typechecking in NewspeakTypechecker

**Status: implemented.** Committed on `master` as `ea304c6`, 2026-09-22, suite
289/289. This file began as a proposal, `TYPECHECKER_INCREMENTAL_REDESIGN_2026-09-21.md`,
and has been rewritten to describe what was built and why. Where the proposal
and the implementation disagree, the implementation is right and the difference
is called out.

Everything here lives in `NewspeakTypechecker.ns` unless stated otherwise. The
module comment at the top of that file covers the older, more general framing
(queries as pure functions, memory/time proportional to program size); this file
covers the dependency and invalidation machinery specifically.

---

## 1. The problem

A whole-program typecheck is too slow to run on every edit, so results are
memoized and edits invalidate the memos. The hard part is not caching, it is
knowing precisely what an edit invalidates — too little and the IDE shows stale
errors, too much and the cache is worthless.

Two facts about this system shape everything below:

- **Mixin identity is stable across an edit, method identity is not.** The psoup
  installer uses `become:`, so a class keeps its identity when reinstalled, but
  its method mirrors are fresh objects. Nothing may key a dependency on a method
  mirror.
- **Lexical scope ignores access control.** A class nested inside C reaches C's
  private members by implicit send. Dependencies therefore do not follow the
  inheritance graph alone.

## 2. Vocabulary

**Declaration** (`class Declaration path:side:kind:name:`) — a structural,
mirror-independent identity for something that can be depended upon: the
top-level-rooted path of simple names of its enclosing class, the side
(`#instance`/`#class`), a kind, and a name. It is a pure value object; `=` and
`hash` are structural, and `path` is compared element-wise because `List>>=` is
identity on this platform. Being structural is what lets an edge survive the
reinstall that follows an edit.

Kinds:

| Kind | Names | Created by |
|---|---|---|
| `#method` | a method selector | the IDE / tests, on an edit |
| `#lazySlot` | a lazy slot name | the IDE / tests, on an edit |
| `#classHeader` | the class's own name | the IDE / tests, on a header edit |
| `#lookup` | a selector | `declarationsForSignatureQuery:` — the dependency edge |
| `#expression` | a selector | throwaway, for evaluations and internal recomputes |

`#absent` is **retired**. It existed only to work around the old asymmetry
described in §4.

**Query** — a memoized question about the program. Two kinds:

- `SignatureQuery type: t selector: m` — what is the type of `m` looked up in
  type `t`? Memoized in `cachedTypes`.
- `SubtypeQuery subtype: s supertype: t` — is `s <: t`? Memoized in `trail`
  (the name is from recursive-type algorithms, not from anything Newspeak).

Note a query is keyed by a **type**, not a class. `ObjectType(C)`,
`SelfType(C)` and `OuterType(C)` are different queries with different answers,
because they have different access rules. This matters in §7 and §10.

## 3. The maps

Three dependency maps and two result caches, all slots of the typechecker:

| Slot | Shape | Meaning |
|---|---|---|
| `dependentDeclarations` | `Map[Query, Set[Declaration]]` | who needed this query |
| `dependentQueries` | `Map[Declaration, Set[Query]]` | which queries refer to this declaration |
| `queriesOfDeclaration` | `Map[Declaration, Set[Query]]` | which queries this declaration used last time |
| `namespaceDependents` | `Map[Symbol, Set[Declaration]]` | who resolved this top-level name |
| `cachedTypes` | `Map[Query, Type]` | memoized signature answers |
| `trail` | `Map[SubtypeQuery, Boolean]` | memoized subtype answers |
| `subclassIndex` | `Map[MixinMirror, Set[MixinMirror]]` | direct subclasses (see §9) |
| `superclassTable`, `typeBuilderCache` | | structure caches (see §11) |

`subclassIndex` is a **lazy** slot, not a header slot, so that hot-loading the
class into a live image cannot leave an existing typechecker with it unset —
schema migration fills a new eager slot with nil and does not re-run
initializers.

## 4. What a signature query depends on — the central decision

`declarationsForSignatureQuery:` answers **one** declaration: the `#lookup` of
the asking type's own class.

```
^{declarationFor: mixin kind: #lookup name: q selector. }
```

It names *the effective result of looking this selector up from this class* —
whether that resolves locally, resolves in an ancestor, or does not resolve.

**Why not the class that answers.** The previous scheme recorded, for a lookup
that resolved, the declaration of the ancestor that defined the member; for one
that did not resolve, an `#absent` declaration for every class on the chain.
That asymmetry was the bug: adding an override on a subclass produces a
declaration nobody depends on, so every dependent kept typechecking against the
inherited signature, and the test suite could not see it because tests drove
invalidation on the declaration the query had actually resolved to.

Recording the class that was *asked* makes an added override visible, and it
retires `#absent` as a concept: a lookup that fails is an ordinary lookup whose
answer is simply not cached.

**Cost.** One edge per query instead of one per class on the chain. The cost
moves from registration (every query of every typecheck) to invalidation (once
per edit).

**The uncached-means-changed convention.** Error and access-error results are
never cached (`cacheableSignature:`), and `functionTypeOf:` registers the
dependency *before* consulting the cache. So a lookup that failed still leaves
an edge, and "nothing cached" is how a previously-failing lookup presents
itself. Propagation treats that as changed. This is load-bearing: it is what
replaces the `#absent` chain, and it is why error results cannot simply be
cached without first distinguishing genuine not-found from the cycle guard's
transient `errorType` (§14).

## 5. What a subtype query depends on

`declarationsForSubtypeQuery:` records a `#classHeader` declaration for each
endpoint's mixin. This is **imprecise and knowingly so**: `S <: T` walks S's
whole superclass chain, so a re-parent of an intermediate class changes the
answer without touching either endpoint's header.

That hole is closed bluntly rather than precisely: `flushClassStructureCaches`
drops the entire `trail`. Recording the dependency on the subtype's chain and
invalidating selectively is the precision upgrade, not yet done.

## 6. Namespace dependencies

Newspeak modules are self-contained, but types cross module boundaries, so type
names are resolved against an external namespace. When a type name reaches that
resolution path, the current declaration is recorded in `namespaceDependents`
under that name — **whether or not the name resolves**, so that a later add
invalidates a prior not-found result.

`invalidateNamespaceName:` flushes the structure caches, then invalidates every
recorded dependent. It **reads** the edges; it does not consume them. They used
to be removed here, but they are only rebuilt when a dependent is actually
re-typechecked, so any declaration whose re-check never happened — or raised —
lost its edge permanently and a second invalidation of the same name became a
silent no-op.

## 7. Invalidation

`invalidateDeclaration:` is the single entry point. Given the declaration that
changed it:

1. `#expression` — does neither walk; it names no member and heads no class.
2. `#classHeader` — flushes the structure caches, **then** runs
   `propagateHeaderChangeAt:`. The flush must come first so recomputation reads
   the new superclass chain; the walk uses the retained pre-edit `subclassIndex`
   to find whom to notify.
3. anything else — runs `propagateMemberChangeOf:at:` for that name.

and then, in all cases, `removeDependenciesOf:` (wipes what this declaration
used last time, since it is about to be re-checked) and
`invalidateDependenciesOn:` (invalidates the queries registered against this
exact declaration and collects their dependents).

It answers the set of declarations that must be re-checked.

### 7.1 Member propagation

`propagateMemberChangeOf:at:` walks down from the edited class. At each class it
calls `recheckLookup:of:into:` for that class's `#lookup` of the selector, which
answers one of:

- `#none` — nothing recorded here. Nothing to invalidate, **but keep
  descending**: a descendant may hold a stale answer.
- `#unchanged` — every recorded answer still compares the same. **Prune the
  subtree.** A descendant resolves the selector to the same definer unless it
  overrides, and overriders are pruned separately.
- `#changed` — invalidate, collect dependents, keep descending.

Plus one structural prune: a descendant that **declares the selector itself**
shadows the edit, so neither it nor anything below it can see the change.

Pruning on `#unchanged` is the win over the old scheme, which could not tell a
body edit from a signature edit and so invalidated every caller of every edited
method.

### 7.2 Header propagation

A header edit can move the superclass clause *and* change the slot set, and with
it the accessors the header declares. There is no single selector to walk, so
`propagateHeaderChangeAt:` enumerates the subtree once, scans `dependentQueries`
for every `#lookup` owned by a class in it, and rechecks each directly.

It does **not** route through `propagateMemberChangeOf:at:` per distinct name.
That form looks attractive because it prunes, but it re-enumerates the whole
subtree per name and rebuilds a `Declaration` — path walk included — at every
class it visits. Measured: no better (§13). The scan already holds each
declaration, so nothing needs re-deriving.

## 8. Recomputation

`signatureOfMember:asSeenFrom:` is the recompute primitive. It takes a **type**,
not a class, and ends in `t at: selector`.

This is not incidental. A cached answer was produced by one particular type
asking, so the only answer comparable with it is what that same type says now. A
private member recomputed through an `ObjectType` answers an access error, which
can never compare equal to the `FunctionType` a self-send cached — so every edit
to a non-public member would look like a change and non-public members would
never prune. `recheckLookup:` therefore recomputes through each recording
query's own type.

`signatureOfMember:inClass:` remains as the ordinary-send wrapper
(`ObjectType forMixin:`), which is the right question when you really mean "what
would a plain send see".

The primitive establishes visitor state exactly as the typecheck entry points do
(`currentClass`, `typeBuilder`, `currentTopLevelClass`), because resolving an
inherited member runs the superclass clause through the visitor; without that
the lookup degrades to an error type and every inherited signature looks
changed. State is saved and restored, errors go to a throwaway `errorSet`, and
`currentDeclaration` is set to a throwaway `#expression` declaration so any
namespace resolution records its edge there rather than against whatever was
last typechecked.

**Recompute only when it can change the outcome.** An answer that is not cached
is already reported as changed, so computing a fresh signature for it produces a
value compared against nothing. The loop also stops at the first difference.
This was the only optimisation of several that measurably helped (§13).

## 9. What "descendant" means

`descendantsOf:` answers **subclasses and lexically nested classes** (both sides
of each nested class).

Both directions are needed and neither substitutes for the other. A nested class
is not a subclass, but its implicit sends reach the enclosing class's members
through lexical scope *regardless of access modifier* — so a private member's
dependents are typically exactly the enclosing class and the classes nested in
it. A subclass-only walk strands them, and since the dependency is recorded
against the class that asked rather than the definer, nothing else reaches them
either.

Subclass edges come from `subclassIndex`, maintained by `recordSuperclassOf:is:`,
through which every genuine `superclassTable` write in `computeSuperclassOf:`
passes (the `cycle` marker deliberately does not). Nesting edges come straight
from the mirrors.

Edges are **add-only**. A stale edge left by a re-parent costs one
recompute-and-compare that then prunes itself; a missing edge silently leaves a
descendant's cached lookup stale. Completeness is adequate for a non-obvious
reason: any class with a cached query had its whole chain walked to answer that
query, so it is already in the table. A class never queried is absent, but has
no cached answer to go stale.

## 10. Comparison

`sameSignatureAs:` / `sameTypeAs:` on `Type` and its subclasses.

They exist because `#=` is unusable for this. `List>>=` is identity on this
platform, so `FunctionType>>=` — `domain = o domain and: [range = o range]` — is
identity for *every* signature, including unary ones, since two empty domains
are distinct `List`s. Comparison is load-bearing for the whole scheme; left on
`#=` it would answer "changed" every time and silently degrade propagation to
invalidating the entire subtree on every edit.

`#=` was **not** changed, because `hash` is also identity-derived and
`FunctionType` values may be Map keys elsewhere.

The default on `Type` is identity, so any type that does not explicitly know how
to compare itself answers false and the caller treats the signature as changed.
Over-invalidation is always correct; a false "unchanged" silently drops a needed
re-check. Overrides exist on `ObjectType` (kind + mixin), `FunctionType`
(element-wise domain, then range), `ClosureType`, `GenericType`, `TypeVariable`
(name *and* mixin — `#=` compares mixins only, so `E` and `K` over the same bound
are equal by it) and `UnionType` (order-sensitive).

`typeKindOf:` gives the discriminating kind symbol, built from the `isKindOf`
predicates because an explicit-receiver `class` send raises in this system. The
kind test carries real weight: `ObjectType>>=` accepts anything answering
`isKindOfObjectType`, so without it a `SelfType` would compare equal to a plain
`ObjectType` over the same mixin.

## 11. Structure caches

`flushClassStructureCaches` drops `superclassTable` (reseeding the built-ins),
`typeBuilderCache` and `trail`.

It deliberately does **not** drop:

- `cachedTypes` — the expensive one, and the whole point of being incremental.
  The subtree walk in §7.2 is what keeps it honest instead.
- `subclassIndex` — this flush fires on exactly the event where the *pre-edit*
  graph is needed. A re-parent must notify the classes that used to inherit
  through the edited class, and after the flush they are reachable only through
  the index's retained edges.

`clearQueryState` is the full reset hatch and drops everything including
`subclassIndex`; that is safe there precisely because no cached answer survives
for a walk to find.

## 12. The re-check driver

- `recheckFrom:` — seed with one edited declaration.
- `recheckAfterNamespaceName:` — seed with everything that resolved a top-level
  name.
- `recheckSeeded:` — work-list: invalidate a node, re-typecheck it
  (`recheckDeclaration:` dispatches on kind to the matching typecheck entry
  point), enqueue its dependents, bounded by a `queued` set.

## 13. IDE wiring

In `HopscotchWebIDE.ns`:

- `typechecker` — a lazy slot holding the persistent typechecker, built over the
  **live** Root namespace so it stays in sync as classes are added and removed.
- `reportRecheckFrom:onSubject:` — drives `recheckFrom:` and pushes results into
  the edited member's display.
- `reportRecheckAfterNamespaceName:` — drives `recheckAfterNamespaceName:`.
- `freshTypechecker` — a throwaway for whole-class reports.

In `Browsing.ns`: the three Accept paths (method, lazy slot, class header) build
the edited `Declaration` and call `reportRecheckFrom:` after installing; the
class install and the two `deleteTopLevelClassNamed:` methods (instance side and
class side of `Utilities`) call `reportRecheckAfterNamespaceName:`. Every call
is wrapped so a re-check glitch cannot break Accept, install or delete.

## 14. Performance, as measured

All figures from the live IDE, `Date.now` around `invalidateDeclaration:`.

| Operation | Cost |
|---|---|
| Method edit, `NewspeakTypechecker` (~30 nested classes) | 2.2 ms |
| Method edit, whole `Browsing` subtree, nothing cached | 8.7 ms |
| Header edit, leaf class | ~4 ms |
| Header edit, module-sized subtree | ~195 ms |

The header figure is the one to watch. Its history is worth recording because
two of three attempts to improve it were wrong:

| Attempt | Result |
|---|---|
| Recheck every (class, selector) pair, always recompute | 221 ms |
| Per-name walks with pruning | 237 ms — no better |
| Skip recompute when nothing is cached to compare | 190 ms — the only real win |
| Back to direct per-declaration rechecks | 195 ms — no different |

What the numbers ruled out: the `dependentQueries` scan (a leaf-class header
edit does the scan in full for ~4 ms), and recomputation (the repeat iterations
run with every answer already dropped and still cost the same). What is left
scales with the *number of recorded lookups in the subtree* — per lookup a query
set is snapshotted into a fresh List, maps are probed, and
`invalidateDependenciesOn:` allocates and iterates again.

**The lever, if this ever matters:** record, per `#lookup`, the declaration its
answer resolved *to*. A change at C then only has to examine lookups that
actually resolved through C, instead of every lookup in the subtree. That is the
precise version of the defining-declaration edge that `#lookup` replaced, kept
*alongside* it rather than instead of it.

Note also that the benchmark's repeat loop is pathological: re-invalidating the
same declaration with nothing re-typechecked in between is the worst case for
retained edges, since every lookup sits in the uncached-means-changed state. A
real Accept is the first-hit number.

## 15. Invariants — the things that are easy to break

1. `subclassIndex` must survive `flushClassStructureCaches`.
2. `descendantsOf:` must include nesting edges, not just subclass edges.
3. Recomputation must go through the recording query's own type.
4. Error results must stay uncached while "uncached means changed" is the
   absence signal.
5. Dependency registration must happen *before* the cache is consulted.
6. `invalidateNamespaceName:` must read its edges, not consume them.
7. Comparison must not route through `#=`, and `#=` must not be "fixed" to be
   structural without `hash`.
8. Over-invalidation is always correct; a false "unchanged" is silent staleness.
   When in doubt, answer changed.

## 16. Known limits and open work

- **Header-edit cost** (§14) — the lever above.
- **Subtype dependencies are endpoint-only** (§5) — currently masked by flushing
  the whole `trail`.
- **`recheckDeclaration:` swallows every `Error` into nil**, which
  `recheckSeeded:` cannot distinguish from "member deleted", so a throwing
  re-check leaves the IDE's previous error display standing. The three
  `Browsing.ns` Accept sites wrap `reportRecheckFrom:` in a silent handler too.
- **`recheckSeeded:`'s comment claims it is over-eager.** That predates
  comparison-based propagation, which now prunes at invalidation time. Whether
  the driver still over-cascades deserves re-measuring rather than believing
  either the comment or this sentence.
- **Caching error results** is impossible without first distinguishing genuine
  not-found from the cycle guard's transient `errorType`.
- **Outer-send hop ambiguity** — in `outer C m`, if a member of the named class
  shares a name with a class enclosing it, the class hop wins, because hop one
  must always be a class name and nothing in the AST says which hop it is.

## 17. Test map

In `NewspeakTypecheckerTesting.NewspeakTypecheckerTests`. Each was checked
against the unfixed code and shown to fail first.

| Property | Test |
|---|---|
| Added override invalidates the inherited lookup | `testIncrementalAddOverrideInvalidatesInheritedLookup` |
| Re-parent invalidates cached subtype answers | `testIncrementalReparentInvalidatesSubtypeCache` |
| Re-parent invalidates cached inherited lookups | `testReparentInvalidatesInheritedLookups` |
| Header slot addition invalidates dependents | `testHeaderSlotAdditionInvalidatesDependents` |
| Unchanged signature prunes (public) | `testSignatureEditWithoutChangePrunesDependents` |
| Unchanged signature prunes (private) | `testPrivateSignatureEditWithoutChangePrunesDependents` |
| Nested-class dependent of a changed private member | `testNestedClassDependentOnOuterPrivateIsInvalidated` |
| Walk passes through an uncached middle class | `testDeeplyNestedClassDependentIsInvalidated` |
| Namespace invalidation is repeatable | `testNamespaceNameInvalidationIsRepeatable` |
| Structural signature comparison | `testSignatureOfMemberIsStructurallyComparable` |
| The dependency edge a send records | `testSignatureDependencyInvalidation` |
| Outer send reaches an enclosing private member | `testOuterSendReachesEnclosingPrivateMethod` |
| Outer send to a missing member still errors | `testOuterSendNonexistentMemberErrors` |
| `outer C N` answers the class | `testOuterSendNestedClassAnswersTheClass` |
| Outer-send dependent is invalidated | `testOuterSendDependentIsInvalidated` |

## 18. Related fixes made along the way

Found while testing the above, committed in `ea304c6`:

- **Outer sends did not typecheck at all.** `OuterType>>at:` looked `C` up as a
  member of the *asking* class in `outer C m`, where `C` is a lexically
  enclosing class — so every outer send answered `errorType`. The parser makes
  `outer C m` a reference to the pseudo-variable `outer` followed by two unary
  sends, so both hops land in `at:`: it now resolves the class hop via
  `enclosingClassNamed:from:` and uses `selfMember:at:` for the member hop,
  which is exactly the outer-send rule (any modifier locally, then
  public/protected up the chain; the old code used `localMember:in:` and missed
  the inherited half). The suite had **zero** outer-send coverage, which is why
  this sat unnoticed.
- `OuterType>>signatureForNestedClass:` removed, so `outer C N` answers N's
  class rather than an N instance.
- `computeSuperclassOf:` pushed no scope, so a header whose superclass clause
  takes an argument failed when called cold, and the `cycle` marker was never
  removed on a raise — poisoning the class's chain to Object permanently.
- `PseudoType>>=` had a stray `is` (`o is isKindOfOuterType`), latent because
  every concrete pseudo type overrides `=`.
- `definingMixinOfMember:in:` and `kindForMember:` deleted, dead once `#lookup`
  replaced the defining-declaration edge.
