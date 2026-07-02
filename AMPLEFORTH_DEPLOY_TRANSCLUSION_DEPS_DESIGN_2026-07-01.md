# Web Deploy — transclusion dependencies & cycles: clean design

**Date:** 2026-07-01 (evening) · **Status:** IMPLEMENTED + verified 2026-07-02. Decisions §6: (1) evaluate-without-render (eagerTransclusionsOf:); (2) Save precise — confirmed; (3) live cycle-ban kept. §7 shallow hack replaced by precise eager embedding. Two-step (Phase B) save added for the deploy timeout.

## 1. What broke and why (root cause)

`deployForWeb: Home` hung inside `createFolder Papers` with infinite recursion:
`createFolder Papers → createFolder Home → createFolder Papers → …`.

Chain of causes:
- Each doc's zip is built by `DocumentSubject>>createFolder`, which via
  `processObjectsFromDom:` → `dependenciesUsing:` embeds every "dependency" it
  finds into `documents/`, **recursively**.
- `dependenciesUsing:` detects dependencies **textually**: `gatherMessagesOf:…using: dom`
  scans amplet expressions (those containing `:`) for names that exist in `Root`.
- The **deploy-aware nav** amplet is `navBar: {{'Home'. 'Home'. false}. {'Papers'. 'Papers'. false}. …}`.
  The doc names sit there as **string literals**, so the textual scan flags
  Home, Papers, Talks, … as "dependencies" of *every* page.
- So every nav page "depends on" every other nav page → mutual embedding →
  infinite recursion. There is **no cycle guard** in `createFolder` because the
  live system *bans* transclusion cycles and catches them at transclusion time —
  but these aren't transclusions, they're nav links, so the ban never fires.

**The textual detector conflates three different relationships:**

| Relationship | Example | Is it a dependency to embed? |
|---|---|---|
| **Eager transclusion** | `transclude: 'B'` | **Yes** — B is inlined at render; the doc can't render without it |
| **Lazy transclusion** | `transcludeFromServer: 'B'` | **No** — B is fetched on demand from the server (a separate doc) |
| **Nav link** | `navBar: {… 'B' …}` / `pageLink:` | **No** — a hyperlink, not content |
| **Class use** | `Counter new` | **Yes** — class must be present to run |

Textual detection embeds *all four*. That's the wart. (It also means plain **Save**
over-embeds nav/lazy docs today, and would hang exactly like deploy if two
mutually-nav-linked docs are both loaded — a latent Save bug.)

## 2. Key insight

**Eager transclusion already works by embedding.** `transclude: 'B'` renders
synchronously via `Root at: 'B'`; B is in `Root` at render time precisely because
the doc's zip embeds `documents/B.zip` and `loadDocument:` loads it. So embedding
is the *right* mechanism for eager deps — we must keep it. The bug is only that
detection is **too broad** (embeds nav + lazy too) and **not cycle-guarded**.

So we don't need a new transclusion model. We need **precise classification** +
a **cycle guard**.

## 3. The clean solution

**Classify by the fragment the amplet produces, not by scanning text.** We already
have this: evaluating an amplet yields `NavBarFragment` (nav), or
`WebTransclusionFragment` with `lazyTransclusion` true/false (lazy/eager). The
deploy's `deployStaticFormOfFragment:` already walks the fragment tree and knows
each case exactly — including *indirect* amplets (`postToggle:`, `row:{transclude:…}`)
that prefix-matching can't handle.

Rules, applied uniformly to Save and Deploy:
- **Eager transclusion → embed** the target in the doc's `documents/` (recursively).
- **Lazy transclusion → do NOT embed.** Deploy: bundle it as a **sibling**
  (`B.html`+`B.zip`) loaded on demand via `loadFromServerNamed:`. Save: nothing to
  embed (it lives on the server).
- **Nav link → do NOT embed.** Deploy: sibling. Save: nothing.
- **Class → embed** (keep the existing textual class detection; classes aren't
  referenced as bare string literals, so they don't suffer the nav problem).

**Cycle guard (defensive, robust):** thread an ancestor set through the recursive
embed. Before embedding X while X is already an ancestor, **don't recurse** —
degrade that occurrence to a link (treat as lazy). Note eager cycles are
*inherently unrenderable* (infinite inline), which is why the live system bans
them; the guard just guarantees the *packaging* can never hang even if a cycle
somehow exists. With precise detection there is no nav-mesh cycle to begin with,
so the guard should never fire in practice — it's belt-and-suspenders, exactly
the "check for cycles, avoid recursing" you asked for.

## 4. How this fixes every case

- **Site (nav only):** nav → no embedding, pages are siblings. No deps, no cycle. ✓
- **Blog (all lazy):** posts → siblings, loaded on demand. Doc zips shallow. ✓
- **Eager transclusion:** target embedded in the doc's zip → live view resolves
  `Root at: 'B'` after hydration. ✓  (This is the case the current shallow hack breaks.)
- **Eager cycle:** banned live (unrenderable); guard prevents any packaging hang;
  deploy already renders the static back-edge as a link. ✓
- **Save:** stops over-embedding nav/lazy; embeds only genuine eager+class deps;
  can't hang. ✓ (Behavior change — see §6.)

## 5. Implementation plan

1. **Split dependency detection** in `DocumentSubject`:
   - keep `classDependenciesUsing: dom` (textual ∩ Root classes);
   - add `eagerTransclusionsOf: doc ^<List[String]>` = evaluate each amplet,
     walk the fragment tree, collect `transcludedDocName` of every **eager**
     `WebTransclusionFragment` (reuse the deploy's walk logic; handles indirect
     amplets and composites like `row:{transclude:…}`).
2. **Rework `processObjectsFromDom:`** to embed `classDependencies` + the eager
   transclusions (recursively), **threading an ancestor set**; skip any target
   already in the set (cycle → link). Retire the textual *document* detection.
3. **`createFolder` threads `ancestors:`** (default `{self name}`); recursion
   passes `ancestors ∪ {childName}`.
4. **Deploy uses the same `createFolder`** — no more `createFolderIncludingDocuments:`
   shallow hack. Doc zips embed eager deps (precise); the deploy's sibling walk
   still collects lazy+nav children into the bundle. Remove the shallow variant
   and the `[page]/[zip]` debug markers (keep the concise progress log).
5. **Verify:** site (5 siblings, no embedding), blog (Room101 + post siblings,
   shallow zips), and a **new eager test doc** (A `transclude: B` → A.zip embeds
   B; live hydration shows B inline; no hang), plus an intentional eager cycle
   (guard degrades to a link, no hang).

## 6. Decisions to confirm in the morning

1. **Evaluate amplets during Save?** Precise eager detection needs to evaluate
   amplets (the only accurate way for indirect amplets). Amplets are already
   evaluated on render, so this is consistent — but Save currently is a passive
   textual scan. OK to evaluate during Save, or keep Save on textual detection
   *with just the cycle guard added* (fixes the hang, keeps today's over-embedding)
   and make only Deploy precise? (Unified/precise is cleaner; the split is less work.)
2. **Save behavior change:** precise detection means a saved doc **no longer
   embeds** nav-linked or lazy-transcluded docs (only eager + classes). This is
   more correct (a doc shouldn't bundle the whole site), and matches your earlier
   stripping of Room101's `documents/`. Confirm that's the intent.
3. **Retire the live cycle *ban* in favor of graceful degradation?** (Your earlier
   idea, plan P6.) Not required for this fix; the ban can stay. Unifying live +
   deploy under one "eager cycle → link" rule is a separate, optional follow-up.

## 7. Current interim state (to be replaced)

- `createFolderIncludingDocuments: false` (shallow) + deploy uses it. Site & all-lazy
  blog deploy correctly; **eager transclusion's live view is broken** (target not
  embedded, not a sibling). Debug markers `[page …]`/`[zip …]` still in
  `WebSiteDeployer`. All this is replaced by §5.
- Committed deploy feature (solid): `bba7414`, `527f5ef`, `7eabec7`, `85c867e`.
  The `WebSiteDeployer` + shallow work is **uncommitted** (WIP).
