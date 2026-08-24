# Map/Set iteration-order sweep — findings, 2026-08-22

## RESOLUTION (same day): insertion order is now the contract on both platforms

Gilad's call: spot fixes are the wrong shape — Maps and Sets should commit to
insertion-order iteration. It turned out psoup already had: commit `18f6afa`
(2024-05-20) "Make Map and Set ordered. Eliminate explicit Ordered versions"
— in `CollectionsForPrimordialSoup.ns`, which the psoup runtimes use. The JS
runtimes use `Collections.ns`, which never got the change: every finding below
was at bottom THIS platform-parity gap (and it is why psoup always "just
behaved").

Done:
- psoup's ordered `Map` and `Set` transplanted verbatim into `Collections.ns`,
  replacing `HashedCollection`/`MutableHashedMap`/old `Set`/`IdentityMutableHashedMap`/
  `IdentitySet`-class and the never-used `OrderedMap`/`OrderedSet`;
  `IdentityMap`/`IdentitySet` are accessors answering `Map`/`Set`, as on psoup.
- Semantic changes riding along (all psoup-canonical): `keys`/`values` answer
  insertion-ordered Arrays (were Set/List); `at:` on a missing key signals
  `NotFound` (an Exception, NOT an Error — `on: Error` handlers do not catch
  it); plain `Set>>include:` is gone (`add:`; `include:ifNew:` remains).
- `CollectionsTesting.ns` updated to the ordered contract plus new
  `testMapInsertionOrder`/`testSetInsertionOrder` (order stability on re-put,
  remove/re-add moves to last, order survives rehash). 49/49 pass.
- **Kernel Array protocol parity** (found the hard way — the Croquet counter
  app failed to boot): psoup Arrays inherit the kernel `Collection` protocol;
  `KernelForJS`'s Array lacked `detect:`/`detect:ifNone:`/`allSatisfy:`/
  `anySatisfy:`/`noneSatisfy:`/`reduce:`/`reduce:ifEmpty:`, and
  `equalVisitOr:` sends `detect:ifNone:` to `Map keys` (now an Array). The
  seven methods are now on `KernelForJS` Array, bodies mirrored from the psoup
  kernel.
- Benchmarks (BenchmarkRunner under jsc, 3 runs, medians): neutral — all
  deltas within the documented noise band; Splay +21%; the deploy shrank
  ~100KB (the ordered classes are leaner than the HashedCollection tower).
- Croquet re-verification on the rebuilt/redeployed artifacts: counter
  3-browser suite and the full Ozymandias document flow ALL-PASS, Document
  view correct on seeder and late joiner, clean consoles.

Consequences for the findings below: the HIGH items and nearly all MEDIUMs
are resolved by the contract (type errors iterate in discovery order,
exemplars in parse order, emitted JS mixins in compile order, the chat menu
comment is now true, zip layouts are insertion-ordered, etc.). Still open as
POLICY choices, not correctness: whether changeset member rows should be
lexically sorted like the class level (finding 6), and the LOW/intrinsic
items. The equalVisitOr: first-match (finding 2) now deterministically picks
the OLDEST equal visit. Caveat that remains: a map whose INSERTION order is
itself async-dependent (on-demand caches under Croquet replay) still diverges
per client — insertion order makes iteration deterministic as a function of
insertion history, no more.

The original findings list follows, for reference.

Follow-up to the default-view fix (`9ed1489`): every place where Map/Set
iteration order reaches user-visible order, a default pick, or generated
output. Background: Newspeak Map/Set iterate object-keyed entries in
identity-hash order; on NS2JS identity hashes are allocation-sequence numbers,
so object-keyed order diverges per client whenever boot interleaves with async
work (Croquet replay above all). String/Symbol-keyed maps are per-run stable
(String>>hash is content-derived) but arbitrary and psoup-vs-NS2JS divergent.

## The spot fixes, re-judged under the insertion-order contract

- **`savedViews` priority order (committed `9ed1489`): KEPT.** viewCache is
  filled on demand, so its insertion order is cache-fill history, which can
  diverge from priority (a view registered after the presenter exists, or an
  evict-and-re-add, inserts a high-priority view after a low-priority one).
  Priority is an explicit concept — availableViewClasses order — and the fix
  derives from it directly. Not a special case of the Map bug.
- **An `objectViewKinds` registration-order list for availableViewClasses was
  briefly added, then REVERTED as redundant**: objectViews is populated once
  at registration, so under the contract its insertion order IS registration
  order — a parallel list would be a second source of truth contradicting
  "rely on the contract".

## HIGH — object-keyed, diverges per client/browser

1. **Type-error order** — `Browsing.ns:543/1164/2295/2859`,
   `HopscotchWebIDE.ns:266`: the typechecker returns `Set[TypeError]` of
   freshly allocated errors; draining the Set builds the banner/report row
   order → error listing order differs per client. Candidate fix: sort by
   source position (`start`) when building the messages — better than report
   order and trivially deterministic.
2. **Navigation visit collapse** — `HopscotchForHTML5.ns:3329`
   `equalVisitOr:` does first-match `detect:` over `ids keys`
   (`Map[Presenter, Integer]`): with several `=` presenters registered, WHICH
   history entry a navigation collapses onto is hash-ordered. Candidate fix:
   pick the candidate with the smallest registered id (oldest visit).

## MEDIUM — string/symbol-keyed: stable per run, but arbitrary and platform-divergent

3. **Default exemplar + Debug menu order** — `Browsing.ns:2497/3150`: keys
   `exemplar1`, `exemplar2`, … are *numbered to express order* but iterated as
   a Map; `es first` is the evaluator/debugger receiver. Fix: sort keys by
   numeric suffix.
4. **Deployment configurations menu** — `DeploymentManager.ns` `configurations`
   = `knownConfigurations values` → menu order.
5. **Chat switcher menu** — `AI_IDE_Support.ns:1552`: comment claims "Root's
   insertion order"; Namespace is Symbol-keyed Map — no such order.
6. **Changeset member/nested rows** — `Repositories.ns:4954/4990/4251/4376/3554/3785`:
   member-level rows in hash order while `classDiffsList` deliberately sorts
   (`lexicallyLessOrEqual:`) — make the lower levels sort the same way.
7. **Compile-error banners** — `Browsing.ns:2113/2691`: `errorMessages` is a
   `Set[String]` — report order lost even per-run; a List preserves it.
8. **Minitest** — `Minitest.ns:385/396`: test execution order and suite-list
   order from `Map[String, TestSuite]`.
9. **Generated JS mixin order** — `Newspeak2JSCompilation.ns:2813`
   `deduplicateMixins` replaces compile order with Map-hash order in emitted
   programs. Fix (first-occurrence order via seen-set) is trivial BUT changes
   emitted-code shape — flagged per the benchmark-before-shape-change gate.
10. **Install order from Maps** — `Repositories.ns:1448`,
    `AI_IDE_Support.ns:2394`, `HopscotchWebIDE.ns:933` feed
    `installFromBuilders:` in Map order (AtomicInstaller itself sorts where it
    knows order matters).
11. **Deploy bundle layout** — `Documents.ns:2014/2083/2174/2342`: zip entry
    order is hash order → non-reproducible bundle bytes across platforms.
12. **Namespace-derived UI lists** — `Repositories.ns:2376/2516`,
    `Browsing.ns:3508/5727` (which names survive the 20-char summary
    truncation is hash-determined), `Namespacing.ns:130` (latent; results
    re-sorted downstream).
13. **AI tool listings** — `AI_IDE_Support.ns:2822/3237/3704`: namespace/media/
    object listings handed to the model in hash order.
14. **JSON key order** — psoup `JSON.ns:351`: harmless for parsers; matters
    anywhere serialized bytes are compared/persisted.

## LOW / arguably intrinsic

- Inspector rows for a Map under inspection (`Browsing.ns:6349`,
  `Inspecting.ns:425`) — inspecting an unordered collection; still a visible
  cross-client divergence under Croquet.
- `NoteTaker.ns:70` note order round-trips as hash order.
- `Documents.ns:2540/2564` deliberately rely on `values` and
  `keysAndValuesDo:` agreeing positionally (documented; fragile, not wrong).
- Squeak-side mirrors (`MirrorsForSqueak.ns`, `NewspeakBrowsing.ns:728`) —
  same shape, not on the NS2JS/Croquet path.

## Verified clean

Sites that already sort/index explicitly: `Browsing.ns:5325/7385/7390/7405`,
`MiscBrowsing.ns:751/1444`, `Repositories.ns:3342`,
`Newspeak2JSCompilation.ns:1182` (sentSelectors sorted),
`AtomicInstaller.ns:253`, `MirrorsForPrimordialSoup.ns:503`.
