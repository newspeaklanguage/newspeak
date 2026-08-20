# Scoped fragment numbering for Croquet — design and implementation plan

2026-08-18. Addresses the class of failure where one client "fails to catch up and
after that all is lost". Companion to `CROQUET_NOTES.md`.

## The defect

Every interactive Croquet fragment takes its identity from a per-type counter on
the `Hopscotch` module, incremented at construction:

```
HopscotchForCroquet.ns
    fragmentId <Integer> = newButtonId.        (* in the initializer *)
    newButtonId ^<Integer> = ( buttonCount:: buttonCount + 1. ^buttonCount )
    scope_slot: 'nsbutton_' , fragmentId printString
```

That scope string **is** the Croquet event address: a widget publishes on it, and
every client's corresponding widget subscribes to it. Clients therefore agree on
which fragment an event refers to **only if they create fragments in the same
order**. There are 18 such counters (`newButtonId`, `newCheckboxId`, … ), all in
one global namespace per type.

Anything that lets one client create fragments in a different order — or merely a
different *number* of them — permanently skews every id after that point on that
counter. Events then land on the wrong widget. This is consistent with the
observed symptom: a client drifts once, and everything afterwards is wrong.

Three constructs now do exactly that, all added after the Croquet code was last
maintained (2025-11-20, `28ab47e`):

- **`LazySequenceComposer` / `LazyColumnComposer`** realize only the rows near the
  viewport. Two clients with different viewports — or one joining late and
  replaying — realize different row sets, so they number different fragments.
- **`AsyncContentComposer`** installs content when a promise resolves, which is
  client-local timing.
- **`WebTransclusionFragment`** loads a document asynchronously; the content is
  identical on every client, but *when* it is inserted is not.

The lazy case is the hard one, and cannot be fixed by pre-resolving: we do not know
what kinds of fragments a row will create, how many, or any upper bound, and lazy
lists may nest to arbitrary depth.

## The solution: scope the numbering

A lazy list (and any other construct with client-dependent realization) forms a
**dynamic scope** for the fragments created within it. A fragment's identity
becomes a path — the scopes enclosing it, then a per-type ordinal within the
innermost scope — instead of a single global ordinal.

**Within a lazy list the scope must be keyed by row index, not by a counter.**
This is the crux. If a list opened one scope and kept counting inside it, a client
showing rows 5–10 would assign 1…n to row 5's fragments while a client showing
1–20 assigns 1…n to row 1's: the same skew, one level down. Keyed by index, row 7's
fragments are numbered inside *row 7's* scope on every client, whatever window each
has realized.

Inside a row a plain per-type counter is correct, because a row's construction is
deterministic: the same `elementAt:` block on the same index builds the same
fragments in the same order everywhere. This is what lets us ignore all three
unknowns — we never need to know what a row builds, only that it builds it the same
way. Nesting falls out, because the enclosing scope is itself stably identified.

Example identity: `nsbutton_/l3/r7/2` — the second button in row 7 of the lazy list
whose own scoped id is `l3`.

## Design

### The seam

The counters live in `HopscotchForCroquet`; the lazy composers live in
`HopscotchForHTML5`. The base module must therefore expose a **no-op seam** that
Croquet overrides — the same shape as the rest of this architecture:

```
HopscotchForHTML5 (module level)
    withFragmentScope: key <String> do: block <[X def]> ^<X> = (
        (* A seam for HopscotchForCroquet, which numbers fragments for Croquet
           event addressing and must scope that numbering. Here, nothing. *)
        ^block value
    )
```

`HopscotchForCroquet`'s `Hopscotch` overrides it to push/pop. Nested classes reach
it by lexical scope, and the override is found through class hierarchy inheritance
— exactly how `newButtonId` and `dropDownImage` already work.

### Scope state and id construction

In `HopscotchForCroquet`'s `Hopscotch`:

```
    fragmentScopePath <String> ::= ''.        (* '' = root *)
    scopedCounters <Map[String, Integer]>     (* path+type -> ordinal *)

    withFragmentScope: key do: block = (
        | saved = fragmentScopePath. |
        fragmentScopePath:: saved , '/' , key.
        ^[ block value ] ensure: [ fragmentScopePath:: saved ]
    )

    newIdFor: type <String> ^<String> = (
        | k = fragmentScopePath , '/' , type.
          n = (scopedCounters at: k ifAbsent: [ 0 ]) + 1. |
        scopedCounters at: k put: n.
        ^fragmentScopePath , '/' , n printString
    )
```

The 18 `new<Type>Id` methods become calls to `newIdFor:`, and `fragmentId` becomes
a **String** rather than an Integer. Scope strings then read
`'nsbutton_' , fragmentId`, dropping the `printString`.

Restoration must be exception-safe (`ensure:`), or one failing row poisons the
numbering for everything after it.

### Hook points

| construct | scope key | site |
|---|---|---|
| `LazySequenceComposer` | `'r' , i printString` | `HopscotchForHTML5.ns:2650` (`recovered:: elementBlock value: i`) and `:2796` (`nu = elementBlock value: i`) |
| `AsyncContentComposer` | the composer's own scoped id | `fillWith:` (`:1329`) |
| `DeferredContentComposer` | the composer's own scoped id | `deferAction:` blocks (`:1251`, `:1279`) |
| `WebTransclusionFragment` | its own scoped id | where transcluded content is built |

Both lazy sites must be wrapped: 2650 realizes a fresh window, 2796 re-realizes on
update. Note 2649 first tries `takePinnedAt: i`, which **reuses** an existing
fragment — no new ids, and correctly so.

## What already works in our favour

- `updateVisualsFromSameKind:` copies the old fragment's scope
  (`scope_slot: oldFragment scope`, **17 sites**). Ids are therefore already stable
  across re-renders *within* a client; the cross-client problem is confined to
  first creation — which is the whole of a late-joining client's experience.
- `LazySequenceComposer` is handed `count:elementAt:`, so the row index is right
  there at both realization sites. No new plumbing is needed to obtain the key.
- Croquet event scopes are opaque strings on the JS side, and
  `newspeakSubscriptions` is keyed by `scope + eventSpec`, so path-shaped scopes
  need no JS change. Replay continues to work unmodified.

## Risks to check during implementation

1. **Fragments constructed outside a render.** Anything built in an event handler
   or lazily, after the enclosing render has returned, sees whatever scope is
   current — probably the root. Audit for this; it is the way the skew would
   silently return.
2. **`fragmentId` becomes a String.** Grep for arithmetic or `printString` on it;
   `newWindowId` in particular is used for the shell's `scope`.
3. **Row index stability.** Indices are only stable if the underlying sequence is
   the same on every client. If it is not, application state already diverges and
   this is not the fix for that.
4. **Persisted scopes.** Existing sessions' stored event histories carry old
   integer scopes; a client with new code replaying an old session will not match.
   Treat this as a breaking change — start fresh sessions.
5. **Menus** (`newMenuId`) already had non-determinism trouble in 2025; check
   whether menu fragments are created inside a render or on demand.

## Suggested order

1. Introduce `withFragmentScope:do:` as a no-op in `HopscotchForHTML5` and wrap the
   four hook points. No behaviour change anywhere; verify the non-Croquet IDE is
   unaffected.
2. Implement scoped numbering in `HopscotchForCroquet`, `fragmentId` as String.
   Verify the counter and TodoMVC still sync — neither uses lazy lists, so ids
   should differ only in shape.
3. Test the IDE with a lazy list: two clients, different window sizes, scroll one
   so the realized windows differ, then interact with a row visible to both.
4. Then a late joiner against a session with history — the case that motivated this.

## Alternatives considered

- **Pre-resolve before first display** (as the startup gate does for the session).
  Works for transclusion, where content is statically known, but not for lazy lists:
  their whole point is not realizing everything.
- **Mediate through a Croquet event**, as file loading does. Right for files because
  the *data* is client-local; unnecessary here, since every client fetches identical
  bytes. Only the timing needs containing, which scoping does more cheaply.
- **Position-derived ids** (a path through the fragment tree, no counters at all).
  The most principled, and it would subsume all of this; far larger a change, and
  the scoping approach can be seen as a step toward it.
