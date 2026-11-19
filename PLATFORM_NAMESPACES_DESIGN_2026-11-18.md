# Platform modules: one set of names, one namespace per platform

**Date:** 2026-11-18
**Status:** Accepted 2026-11-18 as recommended. Steps 1–3 committed; step 4 done, uncommitted (section 7).

## 1. The problem

Each platform has its own versions of the same modules, under different
names:

| Role | psoup | JS (NS2JS) | Eurasia |
|---|---|---|---|
| Internal kernel | KernelForPrimordialSoup | KernelForJS | EurasiaKernel |
| Collections | CollectionsForPrimordialSoup | Collections | CollectionsForPrimordialSoup |
| Actors | ActorsForPrimordialSoup | ActorsForJS | EurasiaActors |
| Mirrors | MirrorsForPrimordialSoup | MirrorsForJS | EurasiaMirrors |
| Host objects | JSForPrimordialSoup | AliensForJS | nested in EurasiaRuntime |
| Runtime | RuntimeForPrimordialSoup | RuntimeForJS | EurasiaRuntime |
| Runtime with mirrors | RuntimeWithMirrorsForPrimordialSoup | RuntimeForJSWithMirrorBuilders | EurasiaReflectiveRuntime |
| Web runtime | RuntimeForHopscotchForHTML | (RuntimeForJS) | EurasiaWebRuntime |
| Croquet runtime | RuntimeForCroquet | RuntimeForCroquetJS | — |

The platform object hides this from ordinary code (`platform collections`).
Several places do see the names:

- **Types.** A type names a module: `<CollectionsForPrimordialSoup Map>`
  (12 such types in the typechecker's tests), or `<Collections List>`,
  which is right only on JS (52 uses).
- **The typechecker.** It finds the kernel as `namespace at:
  #KernelForPrimordialSoup`, which fails on Eurasia.
- **The IDE.** It fills Root from the running runtime's slots, by each
  class's own name. It also lists module names by hand in three places
  (`populateNamespaceUsingPlatform:`, `namespaceGivenPlatform:` and the
  bootstrap name lists).
- **Deployment.** DeploymentManager and NS2JS packaging look modules up in
  Root by name, and generate runtime source that names them.
- **Builds.** WebCompiler keys each loaded module by its class name.
  `manifest Foo` answers the class named `Foo`.

Writing `platform collections Map` everywhere (the first option) helps
code but not types, and not the IDE. The IDE holds several platforms'
modules at once, since it deploys to JS and Croquet. One flat namespace
cannot give two classes the same name. So the names must become the same,
and the platforms must live in separate namespaces (the second option).

## 2. The proposal

1. **One name per role, on every platform**, as below.
2. **One namespace per platform.** Its modules live in a directory of their
   own, and that directory is the namespace.
3. **Name lookup goes through the platform's namespace first, then Root.**
   This holds in builds (`manifest Collections`), in the IDE, and in
   deployment.
4. **In a running IDE, Root's entries for the roles are the running
   platform's modules.** The other platforms' modules stay reachable in
   their namespaces (`Root JS Collections`), so deployment to JS still works.

### 2.1 Names

| Role | Name |
|---|---|
| Internal kernel | `InternalKernel` (runtimes already bind it under that slot name; `Kernel` is the platform-neutral wrapper, `Kernel wrapping: internalKernel`) |
| Collections | `Collections` |
| Actors | `Actors` |
| Mirrors | `Mirrors` |
| Host objects | `Aliens` (psoup's `JSForPrimordialSoup`, JS's `AliensForJS`; Eurasia makes its nested class a module). Not `JS`, as first proposed: that is the JS platform's namespace, and both live in Root. |
| Intermediates | `Intermediates` (only psoup and Eurasia share one today) |
| Runtimes | `Runtime`, `RuntimeWithMirrors`, `WebRuntime`, `CroquetRuntime` |

Modules that are already the same on every platform keep their names:
`Kernel`, HopscotchForHTML5, GraphicsForHTML5, FontsForHTML5, Host, and
the compiler modules. HopscotchForCroquet and HostForCroquet are Croquet
variants, not platforms, and keep theirs.

### 2.2 Namespaces and directories

| Namespace | Directory | Holds |
|---|---|---|
| `PrimordialSoup` | `primordialsoup/newspeak/platform/` | psoup's modules, in the psoup repository, which its own build uses |
| `JS` | `newspeak/platform/JS/` | NS2JS's modules |
| `Eurasia` | `newspeak/platform/Eurasia/` | Eurasia's modules (the fork scripts write here) |

A file's category line (line 2) names its namespace. The directory is the
authority, and the category is checked against it.

## 3. What changes, by component

1. **WebCompiler** (psoup). A module loaded from a platform directory is
   keyed `Platform/Name`. Each `runtime` argument on the command line may be
   qualified (`PrimordialSoup/WebRuntime`). That runtime's manifest looks up
   `Platform/Name` first, then `Name`. The Preloader records the qualified
   key.
2. **Builds.**
   - `tool/build.sh` stages `out/` with the platform directories kept, not
     flattened.
   - `check-duplicate-modules.py` checks uniqueness per namespace.
   - Every script that names a runtime is updated (the survey found about
     ten).
   - The two copies of `AliensForJS.ns` become one.
3. **Namespacing and the IDE.**
   - Root gets a sub-namespace per platform, filled from the platform
     directories that were compiled in.
   - `augmentNamespace:withPlatform:` puts the running platform's modules
     at Root under their role names.
   - The hand-written lists in `populateNamespaceUsingPlatform:` and
     `namespaceGivenPlatform:` shrink to the platform-independent modules.
   - The existing `PrimordialSoup` sub-namespace means "came from the psoup
     repository". It is renamed (section 6, question 3).
4. **The typechecker.** It looks up `#InternalKernel` in Root. Types are
   written `<Collections Map>` everywhere; the 12
   `CollectionsForPrimordialSoup` types in its tests change.
5. **Deployment.**
   - DeploymentManager and NS2JS packaging resolve a target platform's
     imports in that platform's namespace first.
   - The runtime source DeploymentManager generates uses the new names.
   - NS2JS's bootstrap names `KernelForJS` in 32 places (`mixins.$KernelForJS…`
     and a string), which become `InternalKernel`. A deployed JS app holds
     one platform only, so its generated names need no qualifier.
6. **Version control.**
   - Repositories write `<key>.ns` at the top level and treat only
     top-level files as in scope; they learn subdirectories.
   - IDE drafts paths (`<TopLevel>/…`) get the namespace as a prefix.
7. **Eurasia.**
   - The fork scripts emit `platform/Eurasia/InternalKernel.ns`,
     `Actors.ns` and `Mirrors.ns`.
   - The packager's module table and slot filling key by namespace and
     name.
   - `generate-ide-entry.py` resolves names through the namespace.
   - App entries' slots use the role names.

## 4. Order of work

Each step builds and passes every suite before the next.

1. **Infrastructure, with no renames.** Qualified keys and
   namespace-first lookup in WebCompiler; directory-preserving staging;
   per-namespace duplicate checks; Root sub-namespaces; Repositories and
   drafts paths. Nothing moves yet, so behaviour is unchanged.
2. **Eurasia.** It has no users yet, and everything about it is ours.
   Rename its modules and move them to `platform/Eurasia`. The typechecker
   then works on Eurasia through `InternalKernel`, with a temporary
   fallback to `KernelForPrimordialSoup` for psoup.
3. **JS.** Rename and move; change the NS2JS bootstrap and DeploymentManager;
   redeploy and run the JS IDE and the deployed-app checks.
4. **psoup.** Rename and move in the primordialsoup repository; update
   SConstruct and BUILD.gn; rebuild the vfuels. Remove the typechecker's
   fallback.
5. **Types and comments.** Rewrite the remaining `XForPlatform` names in
   types and comments.

## 5. Risks

- **Saved state keyed by old names.**
  - Users' Repositories and drafts recorded under old class names, which a
    one-time rename map in Repositories handles.
  - Workspaces that name modules.
  - `localStorage` backups keyed by class name.
- **psoup upstream.** Renaming files in the psoup repository makes merges
  from rmacnak/primordialsoup harder. We port by meaning already, so this
  is a cost, not a blocker.
- **Two classes with the same name in one image.** The IDE image holds
  psoup's `Collections` and JS's `Collections` at once. Newspeak allows
  this, but anything that prints or looks up classes by name alone (mirrors'
  `name`, error messages, the class browser) shows them alike. The class
  browser should show the namespace.

## 6. Decisions needed

1. **Names.** `InternalKernel` for the internal kernel (keeping `Kernel` for
   the wrapper), and the runtime names of section 2.1? *Recommended.*
2. **Where psoup's modules live.** Keep them in the primordialsoup
   repository (`newspeak/platform/`), which psoup's own build needs?
   *Recommended*, over moving them into the newspeak repository.
3. **The existing `PrimordialSoup` sub-namespace**, meaning "came from the
   psoup repository". Rename it to `PrimordialSoupRepository`, so that
   `PrimordialSoup` means the platform? *Recommended.*
4. **Squeak** (`newspeak/squeak/`). Leave it out? *Recommended.*
5. **Order.** Infrastructure first, then Eurasia, JS and psoup, as in
   section 4? *Recommended.*

## 7. Progress (2026-11-18)

### Step 1: infrastructure

**WebCompiler** (psoup, `newspeak/WebCompiler.ns`):
- A module in `platform/P/` is keyed `P/Name`.
- A runtime named `P/Runtime` gives its manifests, and its application's,
  platform P: `manifest X` answers `P/X`, else `X`.
- `manifest P` answers a strict manifest of P's modules.
- The deployed Preloader resolves names the same way.
- Unqualified runtimes behave as before.
- Checked with a small namespaced build: an unqualified runtime, a
  qualified one, and `manifest Beta Thing`. A psoup IDE built with it boots
  and evaluates.
- The rebuilt `WebCompiler.vfuel` is installed in
  `primordialsoup/out/snapshots`, and the newspeak build needs it. The
  previous one is kept in the session scratchpad.

**`tool/build.sh`** stages `platform/` directories from both repositories
into `out/platform/` and compiles them.

**`tool/check-duplicate-modules.py`**:
- checks each platform directory as a namespace of its own;
- requires each file's category to be its platform.

**`Namespacing`'s manifest** answers a sub-namespace with a manifest
(`manifest JS Runtime`).

### Step 2: Eurasia

Its modules are now `platform/Eurasia/`:
- InternalKernel;
- Actors;
- Mirrors;
- Runtime;
- RuntimeWithMirrors;
- WebRuntime, which holds the kernel class in its `InternalKernel` slot, so
  the IDE registers it in Root.

The fork scripts write them there with category `'Eurasia'`.

The typechecker looks up `#InternalKernel`, falling back to
`#KernelForPrimordialSoup` until step 4.

Eurasia's packager gives a module of another platform the slot named by
platform and name (`JSActors`), and keeps the natives table off it.

All Eurasia suites pass:
- kernel;
- reflection;
- genesis;
- web;
- IDE;
- replay.

The Eurasia IDE's typechecker finds the kernel.

### Step 3: JS

The JS modules are now in `platform/JS/`:

| New name | Old name |
|---|---|
| InternalKernel | KernelForJS |
| Actors | ActorsForJS |
| Mirrors | MirrorsForJS |
| Aliens | AliensForJS |
| Runtime | RuntimeForJS |
| RuntimeWithMirrors | RuntimeForJSWithMirrorBuilders |
| CroquetRuntime | RuntimeForCroquetJS |

psoup's stray, untracked copy of `AliensForJS.ns` was moved out (to the
session scratchpad).

What changed with them:
- **NS2JS bootstrap.** It uses `$InternalKernel`, and a deployed app's
  manifest answers `JS` with itself.
- **The IDE.** It imports `manifest JS …` into slots named `JS…` and
  registers them in Root's `JS` namespace.
- **DeploymentManager.** It takes the JS runtimes from that namespace, and
  resolves a JS deploy's imports in it first.
- **Eurasia's IDE entry generator.** It packages `manifest P X` imports
  into slots named `PX` and answers `manifest P` with a manifest of them.

Checks:
- A psoup IDE built from the new layout packages a JS deploy of the IDE
  (js-deploy-boot-probe). The deploy behaves exactly as the control does:
  the same pre-existing debugger-hook message, the same rendered text.
- The bundle uses `$InternalKernel` and JS's own `Actors`.
- The typechecker suite gives the same 337/340 as before (three pre-existing
  failures).

### Not done

- **Repositories (MemoryHole)** write and read only top-level `<Name>.ns`
  files. They leave `platform/` files alone, but do not yet manage them.
- **`NS2JSApplicationPackaging`**, the Squeak-hosted packager, resolves
  imports flat. Squeak is out of scope.
- **Step 4 (psoup)**:
  - `newspeak/Collections.ns`, the generic collections that JS and Squeak
    shared, becomes JS's `Collections`. Squeak no longer matters, and
    Minitest's `manifest Collections LinkedList` is not used on the current
    platforms (Gilad, 2026-11-18).
  - The existing `PrimordialSoup` sub-namespace in Root, meaning the psoup
    repository, is renamed then.
  - **Known issue, deferred (Gilad, 2026-11-18).** NS2JS deduplicates
    mixins by qualified name (`Newspeak2JSCompilation deduplicateMixins`)
    and keys a deployment's modules by class name, so a JS deploy carrying
    two platforms' modules of the same name (psoup's and JS's
    `InternalKernel`) would keep only one. It has to be fixed before such a
    deploy is made.

### Step 4: psoup (2026-11-18)

**Moved and renamed:**
- psoup's modules are now `primordialsoup/newspeak/platform/PrimordialSoup/`:

  | New name | Old name |
  |---|---|
  | InternalKernel | KernelForPrimordialSoup |
  | Collections | CollectionsForPrimordialSoup |
  | Actors | ActorsForPrimordialSoup |
  | Mirrors | MirrorsForPrimordialSoup |
  | Aliens | JSForPrimordialSoup |
  | Runtime | RuntimeForPrimordialSoup |
  | RuntimeWithMirrors | RuntimeWithMirrorsForPrimordialSoup |

- psoup's web and Croquet runtimes, which live in the newspeak repository,
  are now `newspeak/platform/PrimordialSoup/WebRuntime` (was
  RuntimeForHopscotchForHTML) and `CroquetRuntime` (was RuntimeForCroquet).
- The generic `newspeak/Collections.ns` became `platform/JS/Collections.ns`.
- `IntermediatesForPrimordialSoup` keeps its name: it is shared by psoup,
  Eurasia and NS2JS's dual emission.

**psoup's own build** (SConstruct, BUILD.gn) compiles the platform
directory with the bootstrap compiler, keyed flat. The platform files go
first: `snapshots/compiler.vfuel` fails, in some orders of its input files,
with a doesNotUnderstand in its Snapshotter or a hang. That is
deterministic for a given order and also happens with psoup's sources
unrenamed. Its cause is not known.

**Builds that use WebCompiler** compile the platform directory and name
psoup's runtimes `PrimordialSoup/RuntimeWithMirrors`,
`PrimordialSoup/WebRuntime` and `PrimordialSoup/CroquetRuntime`. This
covers:
- `tool/build.sh` and the other tool scripts;
- Eurasia's scripts.

The rebuilt psoup snapshots and newspeak tool snapshots are installed in
`primordialsoup/out/snapshots`; the previous ones are kept in the session
scratchpad.

**The IDE:**
- It imports psoup's runtimes as `manifest PrimordialSoup …` and registers
  them in Root's `PrimordialSoup` namespace.
- The namespace that meant "came from the psoup repository" is now
  `PrimordialSoupRepository`. Saved repositories bound to the old key are
  rebound to it on restore.
- The typechecker's fallback is gone.

**Deployment:**
- **To psoup:** DeploymentManager records resources as WebCompiler does
  (`P/X` for another platform's modules, psoup's runtimes as
  `PrimordialSoup/X`), with a Preloader for platform `PrimordialSoup`.
- **To JS:** a deployment leaves other platforms out. `manifest
  PrimordialSoup X` answers nil, both at packaging and in the deployed app
  (`ProgramBuilder addAbsentPlatform:`). psoup deploys need psoup anyway.

**Eurasia:**
- It uses psoup's `Collections` as its own, through the slot
  `PrimordialSoupCollections`.
- The IDE entry generator answers `manifest Collections` with it.

**Checks:**
- **psoup's own build:** HelloApp runs. TestRunner stops where it stopped
  before, because CollectionsTesting needs an `OrderedMap` that psoup's
  collections lack.
- **Pretty-printer and parser:** both give identical output to the old
  tools on 54 files.
- **Typechecker suite:** 337/340, the same three pre-existing failures.
- **Eurasia's suites:** kernel, reflection, genesis, web and IDE all pass.
- **A psoup IDE built from the new layout:**
  - It boots; Workspaces open and evaluate; and Root holds the running
    platform's modules under their role names, beside the `PrimordialSoup`,
    `JS` and `PrimordialSoupRepository` namespaces.
  - **JS deploy:** its deploy of the IDE boots exactly as the control does.
    The deploy's sources lost only psoup's three runtimes: 11,510 bytes,
    against 11,468 bytes of source.
  - **psoup deploy:** its deploy of the IDE boots, and the deployed IDE's
    `JS` namespace holds JS's own modules.
- **The JS deploy probe** (`croquet-probes/js-deploy-boot-probe.js`) now
  counts only what packaging logs as a failure. It used to count the IDE's
  boot-time debugger-hook message whenever packaging took longer than one
  poll.
