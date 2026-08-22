# Croquet on the NS2JS platform — integration record

2026-08-20. Companion to `CROQUET_NOTES.md`. Status: **working, verified
headlessly in three browsers** (seeder round-trips, late-joiner catch-up via
replay, bidirectional propagation, second late joiner, clean consoles).
Awaiting Gilad's interactive verification; nothing committed.

## What was built

- **`RuntimeForCroquetJS.ns`** (new): the JS analogue of `RuntimeForCroquet`.
  A copy of `RuntimeForJSWithMirrorBuilders` differing in exactly two slots —
  `js` (wrapped per-session via `JSForCroquet`, which is platform-neutral and
  reused as-is, handed `AliensForJS` instead of `JSForPrimordialSoup`) and
  `hopscotch` (`HopscotchForCroquet` layered over `HopscotchForHTML5`) — plus
  `isKindOfPlatformWithCroquet`.
- **`DeploymentManager.ns`**: `packageCroquetApplicationConfiguration:...`
  packages a fourth file, `<name>.croquet.js` (`JSPackager>>croquetSupportScript`)
  — the NS2JS port of psoup's `meta/croquet-post.js`: model, view,
  nsPublish/nsSubscribe funnels with the large-payload detour, retrying replay,
  per-session storage, getURIParam. Kept section-identical to the psoup copy
  (which stays CANONICAL for the shared parts) minus the Emscripten gate, the
  download helpers (the generated program already has them) and the
  pre-detour-vfuel compatibility shim. `croquetPageNamed:` emits the Croquet
  page; `JSDeployment` grew a `croquetSupport` slot.
- **`Browsing.ns`**: deploy menu gained *as Croquet Web Page*.
- **`HopscotchWebIDE.ns`**: Root-registry entries for `RuntimeForCroquetJS`,
  `HopscotchForCroquet`, `JSForCroquet` (import slots + both `at:put:` cascades
  + the Newspeak bootstrap name list). **Rebuild-required; do not hot-load.**

**The startup gate needed zero compiler changes.** The Croquet page loads the
support script *instead of* the program; the support script's
`Croquet.Session.join(...).then(...)` injects the program `<script>` tag
(`nsProgramSrc`, defined inline by the page). The program's synchronous
top-level boot then finds `theView` already set — the same guarantee psoup gets
from its Emscripten run dependency.

The feared psoup-last-arg vs NS2JS-true-order callback landmine is moot:
every JS-facing handler block in `HopscotchForCroquet` takes a single
parameter, where the two semantics coincide (audited).

## Three real bugs found and fixed

1. **Enumerable prototype augmentation** (`KernelForJS.ns`,
   `augment:withPropertiesOf:`): Newspeak protocol copied onto
   `Array.prototype` (and Boolean/Function/Number/String/Uint8Array) was
   enumerable, so any third-party `for...in` — Croquet's snapshot writer walks
   the model's event array exactly that way — saw hundreds of methods. Now
   assigned then `defineProperty enumerable: false`, matching what the selector
   registry already did for the Object.prototype catchers (and matching
   commented-out code in that very method that anticipated this).

2. **Croquet's serializer sentinels collide with NS2JS `$`-mangling** — the
   critical one. Stock `@croquet/croquet` probes decoded objects with bare
   reads: `const { $class, $model, $ref } = value; if ($model) return
   this.readModel(...)`. On NS2JS, `$model`, `$class`, `$ref`, `$id`, `$value`
   are the mangled forms of the Newspeak selectors `model`/`class`/`ref`/`id`/
   `value`, so `Object.prototype` carries a doesNotUnderstand *catcher
   function* under each. Every decoded plain object therefore "had" a truthy
   `$model` and was misrouted into `readModel`, which stringified the catcher
   into `Model class "function() {...}" in snapshot, but not registered?` —
   killing every late joiner at its first snapshot, and poisoning the ref
   machinery on the write side too (`state.$id || (state.$id = ...)`).
   This is `reference_ns2js_prototype_dnucatcher_pollution` biting inside a
   third-party library: **never a bare read of a `$`-prefixed key in the NS2JS
   realm**. Fixed by patching the Croquet client (below).

3. **`rootView <-: replay` never fires on NS2JS**
   (`HopscotchForCroquet.ns`, `HopscotchShell>>displayPresenter:`): the
   post-first-display replay trigger was an *eventual send* to a JS alien,
   which the JS platform's aliens do not understand — an uncaught
   MessageNotUnderstood on every client, invisible on the seeder (nothing to
   replay) and fatal for joiners (catch-up never ran; the constructor-time
   replay correctly no-ops with zero subscriptions). Now a direct
   `rootView replay`: the handlers' all-Newspeak-processing-for-the-turn-done
   assumption is honored by the dispatch chain itself (thunks run as
   microtasks after the current turn, with 15s subscriber retries).
   **Note: this changes the psoup Croquet builds too** (direct call instead of
   eventual send) — psoup IDE sync deserves a retest.

## The self-hosted patched Croquet client

`out/croquet.min.js` is built from the checkout at `../croquet`
(`packages/croquet`), with an `NS-PATCH` block in `teatime/src/vm.js`: two
helpers (`hasOwnProp`/`ownProp`) and every serializer-sentinel probe
(`$model`, `$class`, `$ref`, `$id`, `$value`, `$compiledFuncs`,
`$debugWriteProxyHandler`, and the `"$value" in state` test) converted to
own-property reads, read path and write path both. The patch is a no-op in a
clean realm, so it is safe anywhere (the psoup page could adopt it too;
currently it still loads the CDN build, which is fine there).

Building it (deps are intentionally not saved to package.json —
`../croquet/packages/croquet` is a plain clone):

```sh
cd ../croquet/packages/croquet
npm install --no-save ./math crypto-js@4.2.0 pako@1.0.11   # unresolved imports
npm run build-prod-pub                                     # pub/croquet.min.js
cp pub/croquet.min.js $NEWSPEAK/out/croquet.min.js
```

Unresolved imports otherwise become silent globals ("guessing" warnings) and
the bundle dies at runtime (`WordArray is not defined`, CroquetMath undefined).
**The vm.js patch is uncommitted in the croquet checkout** — commit it there
before touching that tree.

The generated Croquet page references `croquet.min.js` *relatively*, like
CodeMirror and vendor/: it is an environment file the deploy target must
provide (it lives in `out/`; deploy scripts that mirror `out/` pick it up).

## Deploying and running a Croquet JS app

In the IDE: an application configuration's `[deploy]` menu → *as Croquet Web
Page* → saves `<Name>_js_app.zip` with four files. Serve beside the usual
environment files (CodeMirror/, vendor/, jszip, croquet.min.js) and open with
the standard Croquet parameters (all required, see CROQUET_NOTES.md):

```
CroquetCounterApp.html?sessionId=<fresh>&pwd=x&appId=org.newspeaklanguage.counter
    &apiKey=none&reflector=ws://localhost:9090&files=/files
```

A deployed set for `CroquetCounterApp` is staged in `out/` for immediate use.

## Verified / not yet verified

- Verified (headless, 3 browsers): boot gate, live button round-trips,
  snapshot + replay catch-up for two late joiners at different depths,
  joiner→seeder propagation, clean consoles.
- **The Croquet JS IDE works** (2026-08-21): `HopscotchWebIDE` deployed with
  `RuntimeForCroquetJS` *from the psoup IDE* (31.3MB program; the WeakRef
  ceiling of `SELF_HOSTED_DEPLOY_WEAKREF_CEILING_2026-08-17.md` bites only
  when the NS2JS platform does the *packaging* — running the deployed IDE is
  fine). Two-browser headless test: seeder boots, navigates to Workspaces via
  the reflector; late joiner replays the navigation to the same page; zero
  console noise. Staged as `out/CroquetJSIDE.{html,js,sources.js,croquet.js}`
  (names prefixed so the plain `HopscotchWebIDE.*` JS deploy is untouched).
- psoup replay after the direct-send change: the psoup IDE catch-up harness
  (`croquet-repro.js`: navigation + deferred toggle + oversized detoured
  event, 60s joiner) ran twice against the rebuilt vfuels — both runs
  converged byte-identically (8384=8384) with only the intentionally-bogus
  event skipped after its designed 15s retry.
- **Ozymandias end-to-end on the JS IDE** (2026-08-21, `ozymandias-js-test.js`):
  namespace menu → Load Document(s) → file chooser fed `out/Ozymandias.zip` →
  Data-API upload → croquet round-trip install → document opened; a late
  joiner replays the whole sequence to a byte-identical page. Also verified
  directly: a raw DataHandle in an event payload survives publish → model
  history → snapshot → late-joiner deserialization → fetch, identically on
  psoup (CDN client) and NS2JS (patched client) — `datahandle-probe.js`.
  Workspace editor edits replay to late joiners too (`croquet-ide-js-test2`).
- Still not exercised on NS2JS: the large-payload detour at editor scale,
  drag-and-drop, menus beyond the namespace menu.
- **Failure signature worth knowing**: a Croquet JS deploy made from a STALE
  IDE image (pre-2026-08-20, CDN client, no sentinel patch) works live but
  fails replay/late-join catastrophically with `Model class "function() {...}"
  in snapshot, but not registered` — that is the unpatched-client sentinel
  collision, not a replay bug. Check the deploy's page references
  `croquet.min.js` (relative), not the CDN, and that the IDE that produced it
  reports the stamped version.

## The nondeterministic default view (found 2026-08-21, fixed in Browsing.ns)

Gilad observed documents opening in the BASIC object view instead of the
Document view — in some browsers only (Chrome-JS bad, Firefox-JS and psoup
good). Mechanism: `ObjectPresenter>>objectDetails` took its view list from
`savedViews values` — `viewCache` is a `Map[Presenter class, Presenter]`, and
Map iteration over *object* keys follows their identity hashes, which are
allocation-sequence numbers. The carefully computed priority order of
`availableViewClasses` (registration order, BasicView last) was thrown away by
the rekeying, so "first view" — the default — depended on each client's
allocation history. Under Croquet, replay and the async join interleave with
boot, so that history diverges per client, per join order, per browser timing:
a nondeterminism wearing a browser-difference costume. Fixed by having
`savedViews` answer the presenters in `availableViewClasses` order
(`syncViewCache` fills/prunes and returns the ordered classes). Also fixed
there: `views detect: ... ifNone: [views first title]` handed `holder:` a
title STRING when `preferredViewName` matched no view (easy to hit — Document
view titles embed the document name); now `views first`.

The general lesson: **never derive a user-visible default from Map iteration
order over object keys** — on NS2JS identity hashes are allocation-sequence
numbers, and any async interleaving (Croquet replay above all) makes that
order client-dependent. Note `preferredViewName` is sticky per subject
(`updateStateFrom:` carries it forward), so a session that already defaulted
wrongly keeps showing Basic until a fresh session/reload.

Verified post-fix: the Ozymandias flow shows the Document view on BOTH seeder
and late joiner, byte-identical (`ozymandias-js-test.js`, all green).

## Rebuild hygiene (lesson, 2026-08-21)

Ad-hoc vfuel rebuilds (running the WebCompiler line without build.sh's step
4e) ship the committed `BuildInfo.ns` placeholder, so the IDE reports
"development build" and builds become indistinguishable — never do that.
Stamp first (SHA + date + dirty flag), compile, restore the placeholder;
`scratchpad/rebuild-vfuels.sh` does the full sequence. Also: a vfuel rebuild
landing under LIVE Croquet sessions is a stale-session amplifier — the stored
event history replays into clients running different code, so fragment ids
can no longer match (CROQUET_NOTES: fresh sessionId per test run). Three
rebuilds landed in out/ on 2026-08-20 while testing was in progress, which is
the leading suspect for that day's "replay got unreliable" impression.

## Headless harnesses (scratchpad, reusable patterns)

- `deploy-driver.js`: boots the psoup IDE headlessly, opens a workspace,
  installs app classes from source via `ClassDeclarationBuilder fromUnitSource:`
  + `ide installFromBuilders:into:`, runs the Croquet packager, and PUTs the
  four files to the file server (`/files/deploy/`).
- `croquet-js-test.js`: three-browser seeder/joiner/late-joiner counter test
  with PASS/FAIL checks and console-hygiene assertion.
