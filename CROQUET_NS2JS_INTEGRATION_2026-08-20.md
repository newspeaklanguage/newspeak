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

## The editor echo storm (found 2026-08-22 by Gilad, fixed)

Typing fast in a large editor (Ozymandias raw view) with two browsers attached
melted the session: `Sends to reflector at or above recommended limit`,
disconnect, auto-rejoin, replay re-firing thousands of events, re-disconnect —
an unending spiral (his session `143` is permanently poisoned; its stored
history IS the storm).

Mechanism, visible in the stack traces: the `reflecting` flag suppresses
republishing only during the SYNCHRONOUS window of applying a remote event,
but CodeMirror delivers some signals — `beforeSelectionChange` from a cursor
adjustment above all — at the END of its operation/display update, after the
flag is restored. So every applied remote change made the receiving client
publish selection events: N-fold amplification of every keystroke (latent on
psoup too; his psoup tests simply stayed under the reflector's ~20 msg/s
budget). Once the rate limit tripped, replay-of-history re-fired the deferred
echoes en masse — self-sustaining.

Fixes:
- **Origin-based echo suppression** (HopscotchForCroquet CodeMirrorFragment):
  programmatic cursor/selection adjustments are tagged
  `{origin: 'croquet'}` (`croquetOrigin`), and the publish hooks
  (`respondToChange:`, `respondToBeforeChange:`,
  `respondToBeforeSelectionChange:`) skip signals whose origin is `croquet`
  or `setValue` (`isSyncOrigin:` — `setValue` covers both remote application
  and reconciliation refreshes). Timing-independent, unlike the flag, which
  remains as a second layer.
- **Detached-view guards** in both glue copies (psoup `meta/croquet-post.js`,
  spliced into both `croquetpsoup.js` copies, and
  `DeploymentManager>>croquetSupportScript`): `nsPublish` drops with a warning
  and `nsResolvePayload` throws cleanly when `theView.session` is gone,
  instead of the `TypeError (reading 'data')` flood.

Verified headlessly: 40 keystrokes with a second client attached produce
exactly 121 events (40 × ~3, no amplification), no rate-limit warnings, and
both editors converge to identical text; a deliberate over-rate burst now
recovers after a single reconnect instead of spiraling.

**Remaining, needs a design decision**: each keystroke publishes ~3 events
(codeMirror_keydown + beforeChange + change, two carrying the FULL buffer
text), so sustained typing over ~7 chars/second exceeds the reflector's
20 msg/s recommendation by itself; the resulting reconnect now recovers
cleanly but can drop the couple of keystrokes in flight (observed: 38/40 at
8 cps). Candidate mitigations: stop publishing keydown per keypress, coalesce
beforeChange+change into one event, or publish diffs rather than full text.
Also unexplained: that reconnect rejoins under a DIFFERENT croquet session id
(observed twice); both clients migrate together and stay consistent, but it
deserves a follow-up.

## The method-editor cascade on the JS platform (traced & fixed 2026-08-23)

Clicking a method name in the inspector on the JS IDE collapsed into a broken
debugger. Peeling it found FOUR stacked JS-platform discrepancies (psoup
canonical throughout); all fixed:

1. **Debugger activation walkers trusted suspendedActivation's type**
   (Debugging.ns): canResume, includesActivation:, refreshActivationChain and
   the lazy-slot adjuster now guard with isKindOfActivationMirror — walk only
   as far as the chain consists of activations. (The JS eager thread's
   suspendedActivation was an ObjectMirror; sending #sender to it took the
   debugger down, and the debugger-on-debugger masked everything else.)
2. **`sendSuspended:with:` broke the psoup contract** (MirrorsForJS): it ran
   eagerly and stashed the receiver's ObjectMirror as suspendedActivation
   (evaluator scope only). Now simulator-backed via debugSuspended:with: — a
   thread genuinely suspended before the first instruction with a real
   ActivationMirror carrying scope AND method identity; the eager body
   remains as eagerSendSuspended:with:, the explicit fallback when the
   simulator is not packaged.
3. **`ClassMirror>>isMeta` lied** (MirrorsForJS → KernelForJS): it delegated
   to the legacy kernel `Class` stand-in whose isMeta was unconditionally
   true. Consequence: `classObjectScopeFor:` (Browsing) saw every instance's
   class as "already a metaclass" and handed the INSTANCE as the receiver for
   class-side exemplar sends — `version` sent to a BuildInfo instance, MNU.
   psoup never surfaces the wrong send because its suspend executes nothing;
   the JS simulator's entry does lookup and raised mid-render. Both isMetas
   now use the runtime-structure convention (a meta mixin has no `.meta` of
   its own — KernelForJS Mixin>>isMeta), the JS analogue of psoup
   ClassMirror's `Metaclass = classOf: reflectee`. This also repairs
   Debugging.ns:176's receiverClassMirror isMeta branch.
4. Verified end-to-end after the fixes: inspector → class → method click
   opens the method editor (CodeMirror with the method source), and typing
   with two clients attached keeps cursor and text correct. Core suites and
   both Croquet regression suites all green.

Diagnostic technique worth keeping: hook console.error in the page and unwrap
the Newspeak MNU's `$message$slot.$mangledSelector$slot` + `.trace` — turns
"KernelForJS`MessageNotUnderstood" into selector, receiver constructor and
the exact send site.

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
