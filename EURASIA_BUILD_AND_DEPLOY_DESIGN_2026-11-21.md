# Building and deploying Eurasia images: design

**Date:** 2026-11-21
**Status:** Approved (Gilad, 2026-11-21). Steps 1 and 2 (section 5) done,
uncommitted: `EurasiaBuild.ns`, `EurasiaBuildList.ns`,
`platform/Eurasia/EurasiaNatives.ns`, `eurasia/scripts/build.sh`,
`eurasia/scripts/natives-module.py`, and changes to `EurasiaPackager.ns`,
`platform/Eurasia/Runtime.ns` and `RuntimeWithMirrors.ns`.
- Step 1: every genesis image is byte-identical to packaging that application
  alone; the generated entries were text-identical to the Python generators'.
- Step 2: entries are top-level (2.1), however they are packaged. Nesting
  one in the kernel is a grant the caller makes explicitly, by the packager's
  `--entry-in-kernel`, and only the kernel's own tests, probes and benchmarks
  that use its members (`vm print:` and the like) get it: each such
  invocation in the eurasia scripts names it. The IDE's and CounterApp's
  entries in `ide.sh` and `web-tests.sh` are now top-level too; four platform definitions (base, with
  mirrors, with Hopscotch, with both), keepsSources from the runtime module's
  class, honoured by the packager; applications find their modules by
  scanning their main module and, transitively, every module handed the
  manifest (`manifest X packageUsing: manifest`), so the build list names
  only main modules; the natives catalog is the module EurasiaNatives,
  checked against natives.tsv by `scripts/check.sh`.
- The build list holds the IDE, five tools, CounterApp and TodoMVC. All run:
  the tools give psoup's output, the IDE boots with its sources, the two demos
  work, without sources (CounterApp's image 441 KB, against 1.1 MB with
  them). Packaging all eight takes 13.5 s.
- Step 3: Build IDE image on Eurasia. The native VmGenesisImage
  (`genesisImageFrom:replacing:keepingSources:`, 4.3) and VmDeliverImage
  (`deliverImage:named:`, 2.5), on Eurasia's Mirrors (added by
  `kernel/fork-mirrors.py` step 8): `genesisImageOf:replacing:keepingSources:`,
  `genesisImageOfApplicationReplacing:keepingSources:` and
  `buildImageOfApplicationNamed:replacing:keepingSources:`. The page runs
  genesis in a VM of its own (`eurasia.mjs` `genesis`) and keeps the base
  image with the saved images. The IDE's toolbar had Build IDE image beside
  Save Image; the built IDE had a fresh BuildInfo, marked "built from a live
  image". (Removed 2026-11-21: deploying HopscotchWebIDE to Eurasia with
  mirrors does the same; the Mirrors API stays.) `eurasia --methods` and `eurasia --census` compare images (4.4).
  Results: an IDE built in the browser holds the same 30,966 methods and the
  same objects, class by class, as `ide.sh`'s, except BuildInfo's stamp; it
  boots. `reflection-tests.sh` has an application deploy itself and checks
  its methods against the packaged image's and that it runs afresh; a
  one-method change shows up in the comparison (negative control). The new
  natives join kernel version 2, not yet released.
- Step 4: deploying from an IDE's sources, built in shared IDE code and
  tested in the Eurasia IDE (the JS IDE, its target, is being repaired; the
  code does not depend on which IDE runs it, but the JS IDE's page cannot
  run genesis yet, so the deploy refuses there for now). EurasiaBuild's
  descriptions, platform definitions and entry generator moved to
  `EurasiaDeployment.ns`, over a source provider: EurasiaBuild's `Files` on
  the command line, DeploymentManager's `EurasiaSources` (the IDE's Root and
  its platform namespaces; image resources by a HEAD request to the page)
  in an IDE. The IDE registers Eurasia's platform modules (Root's Eurasia
  namespace), EurasiaDeployment, EurasiaPackager and psoup's Kernel; an
  application's `manifest Eurasia X` is Eurasia's own module X (one slot,
  packaged once), and `manifest Eurasia InternalKernel` the image's own
  kernel class (packager); a borrowed name (Collections) is never a module.
  Platform definitions list the images their runtime loads. The class
  inspector's [deploy] menu has "to Eurasia" and "to Eurasia with Mirrors"
  (DeploymentManager `deployToEurasia:withMirrors:`, a #Eurasia base with
  two default configurations); the page runs genesis and zips (it saves
  nothing itself: genesis and the zip outlast a click's activation, so the
  page answers a promise, `window.eurasiaDelivery`, and the IDE opens the
  usual Save confirmation when it is ready, whose click saves). Since
  2026-11-21 an IDE on Eurasia deploys from its live classes, not its
  sources (DeploymentManager `liveGenesisImageOf:in:`): the entry is
  compiled from the entry source (one small class), its slots are filled
  with the classes Root holds for its modules (Application `moduleSlots`;
  the kernel slot from Root's Eurasia namespace) and Mirrors
  `genesisImageOf:replacing:keepingSources:` takes what it reaches; sources
  are kept as the live runtime class says (PlatformDefinition
  `runtimeModule`). The manifest is Root's; a namespace of the
  application's own, inheriting from its enclosing namespaces, may serve
  later. HopscotchWebIDE with mirrors: 0.47 s to the image (9.6 s from
  sources), 0.3 s for genesis and the zip; its methods are those of
  `build.sh ide`'s image exactly (28,741), objects nearly the same (the
  entry's nested classes are made on first use, not by a packager); it
  boots. Deploying from sources stays the command line's (and the JS IDE's,
  when its page runs genesis). Its bundle:
  base.eus, the VM, a page (`eurasia/web/app.html`), and what the platform
  needs. `ide.sh` now builds the IDE with `build.sh`; `EurasiaIDE.ns` and
  `generate-ide-entry.py` are no longer used. Results: CounterApp deployed
  from the IDE (installed there as accepted code) holds the same 5,235
  methods and objects as `build.sh`'s, and runs from its bundle; the IDE
  deployed from its own sources holds the same 31,310 methods, except two
  (below), and boots from its bundle. psoup still compiles the IDE.
- No primitives on Eurasia (Gilad, 2026-11-21): primitive pragmas are
  only metadata, so the parsers stay as they are; no module Eurasia runs
  carries one, and a module psoup and Eurasia share that uses primitives has
  a Eurasia fork without them.
  - Eurasia's Mirrors and Actors: the pragmas, copied from psoup, become
    plain comments (fork-mirrors.py's last step; Actors.ns edited directly,
    since fork-actors.py no longer reproduces it: Save Image and callback
    reporting were added to Actors.ns by hand).
  - The genesis packager and psoup's five tools: Eurasia forks in
    `platform/Eurasia/`, generated by `eurasia/kernel/fork-apps.py`
    (`--check` in `scripts/check.sh`), whose file methods are Eurasia's
    natives VmReadFile and VmWriteFile by the natives table. EurasiaBuild
    and EurasiaDeployProbe, Eurasia-only, likewise. The build list and the
    IDE use the forks.
  - The packager refuses a module with a primitive pragma (a comment outside
    string literals), instead of stripping it; psoupPrimitiveNatives is gone.
    So Eurasia images keep their sources as written.
  - An application finds Eurasia's fork of a module first. A module with a
    primitive and no fork is absent (its manifest answers nil, as a JS
    deployment's does): in the IDE, psoup's WebCompiler and psoup's own
    platform modules. So that the IDE deploys from its sources as the build
    does, an unresolved module name (capitalized), or platform module,
    answers nil as well.
  - The IDE runs without them: psoup's deploy entries and configurations
    only where it can deploy to psoup (DeploymentManager `deploysToPsoup`),
    its Preloader lazy, WebCompiler entered in Root only when present.
  - Results: the IDE built from files, and the IDE deployed from the IDE's
    own sources, hold the same 28,742 methods and objects; both boot. The
    forked tools give psoup's output; psoup still compiles the IDE.
**Context:** `eurasia/docs/COMMAND_LINE.md` (command-line Eurasia and its
measurements), `EurasiaPackager.ns`, `eurasia/scripts/ide.sh`,
`eurasia/scripts/tool-image.py`, `DeploymentManager.ns`,
`tool/build.sh`.

## 1. Summary

Two subsystems, sharing parts:

1. **Building from source** (section 3): a command-line build, run on
   Eurasia, that makes the images of a list of applications (the IDE, the
   command-line tools, the demos) from the source files. It replaces the
   psoup steps of `tool/build.sh` and `eurasia/scripts/ide.sh`.
2. **Deploying from the IDE** (section 4), which splits by the platform the
   IDE runs on:
   - the **JS IDE** (staying) deploys Eurasia images **from its in-IDE
     sources**, compiling them with the packager, as the build does;
   - the **Eurasia IDE** deploys **from its compiled bytecode**, with no
     parsing or compilation: it cuts an application's image out of the
     running one. Building the IDE itself is the main case.
   - the **psoup IDE** is going away: it keeps its vfuel deploys and gets
     nothing new.

The parts both subsystems use (section 2): the application description, a
Newspeak entry generator, the natives catalog, a genesis runner, and the
bundle writer. Only how the genesis image is made differs: compiled from
source (the packager) or cut from the live heap (a rooted snapshot).

## 2. Shared parts

### 2.1 What an application image is

An application image is made in two steps, as today:

- **The genesis image**: the kernel's classes (InternalKernel), the
  application's module classes, and a generated entry (2.3). The kernel
  module is the image's entry; its slots hold its nested classes, the VM
  mirror, the symbol table (a WeakArray) and a reference to the entry, in its
  slot `application`.

  The application's modules are top-level classes: their enclosing object is
  nil, so they see nothing of the kernel. They reach the platform only through
  what `main: platform args:` hands them, as on psoup. The entry is different
  today: the packager compiles it nested in the kernel
  (`buildGenesisFrom:...`, `mixinTreeFor: app enclosing: kTree`), so its code
  could name the kernel's members (`vm` among them) by implicit-receiver
  sends. It needs none of that: genesis hands it the kernel as the argument
  of `platformOver:`. **Change:** the packager compiles the entry top-level
  as well, referenced from the kernel's `application` slot and nothing
  more. The kernel then holds a reference to the entry, and no application
  code is nested in it. Acceptance: the Eurasia gates and the IDE image run
  with the entry top-level.
- **Genesis**: Eurasia runs the genesis image once. `InternalKernel>>main:args:`
  builds the platform (`application platformOver:`), the message loop and
  the platform template, then writes the heap without frames
  (`vm snapshot`). That is the base image (`base.eus`) a page or the
  command line runs.

Classes carry no instance state (Newspeak has no class-side slots), so a
genesis image holds code and no session state, however it is made.

### 2.2 The application description

What every path takes: a value object, of a class written in Newspeak (as
are the entry generator, the build and the packager; "Newspeak" below always
means code written in Newspeak):

- the application's module (a top-level class with `packageUsing:` and
  `main:args:`), given unambiguously (below);
- its platform: a platform definition (below);
- the modules it takes from its manifest, each bound to the name the
  manifest answers it by, and its resources (images the manifest answers as
  file names the page serves);
- the output name.

Whether methods keep their sources is not the description's choice but the
platform's (below).

**Naming things unambiguously.** Two modules may share a name: in different
platform namespaces (Eurasia's Actors, JS's Actors), or in different
directories. A description never finds a module by looking a name up; it
holds the module itself:

- in an IDE, the class object, taken from the namespace path the user
  chose (`Root HopscotchWebIDE`, `Eurasia Runtime`);
- on the command line, the source file's path; the build list names files,
  not class names.

What is name-based is the manifest protocol (`manifest Collections`), and
within one application that must be unambiguous. So the description binds
each manifest name to one module, and packaging fails when two modules of an
application have the same simple name, or one has a kernel class's name (the
packager already refuses the latter; `tool/check-duplicate-modules.py` checks
psoup's build for the former).

**Platform definitions.** A description names a platform definition rather
than a set of flags, because there will be more variations than DeploymentManager's
`hasMirrors` / `hasHopscotch` / `hasNode` / `hasZircon`. A platform
definition is itself a Newspeak object, one per variation: the platform modules
it needs (each given as above), the expression the entry's `platformOver:`
builds it with, the bundle files it needs (2.6) and the host services it
assumes (DOM, files). Eurasia's three today (base; with mirrors; with mirrors
and Hopscotch) are three definitions; a Croquet, Node or Zircon platform
is a new definition, not a new flag, and nothing else in the pipeline
changes.

**Sources follow mirrors.** As originally designed, a platform says whether
an image keeps its methods' sources: the runtime module's class answers
`keepsSources`. psoup's `RuntimeForPrimordialSoup` answered false and
`RuntimeWithMirrorsForPrimordialSoup` true (psoup 3869a20); DeploymentManager
still generates the same method for its runtime classes, and
`PSoupPackager` passes it to the snapshotter. The rule: with mirrors, sources;
without, none. Eurasia's `Runtime` and `RuntimeWithMirrors` get the
class-side `keepsSources` (false and true), every platform definition takes
it from its runtime module, and every path honours it: the packager writes
nil source fields when it is false, and the rooted snapshot is passed it
(4.3).

The module list comes from a **recording manifest**, as PSoupPackager's
`RecordingManifest` does today: run `packageUsing:` against a manifest that
records each name asked for. This replaces the regex scans of
`generate-ide-entry.py` and the hand-written module lists of
`tool-image.py`.

### 2.3 The entry generator (Newspeak)

`generate-ide-entry.py` and `tool-image.py` each generate the same shape of
entry module: a slot per module, a Manifest class answering each module (and
each resource) by name, a `main:args:` that packages the application and runs
it, and a `platformOver:` that builds the platform the description names.

The generator writes only this small entry class's source. It builds no
platform classes. "Builds the platform" means that, at genesis, the entry's
`platformOver:` instantiates the platform's modules (`Runtime kernel: ...
collections: ... actors:`, then `RuntimeWithMirrors ... over:`), making
the platform objects the application runs with. Where the platform's
classes come from depends on the path:

- the command-line build (section 3) compiles everything from source,
  platform modules included;
- the Eurasia IDE (4.2) takes the platform's classes live, already compiled,
  like the application's;
- the JS IDE (4.1) must compile them: its own live platform classes are the
  JS platform's, compiled to JavaScript, not Eurasia's bytecode. So it
  compiles Eurasia's platform modules from their sources, which it holds
  (the Eurasia platform namespace).
One Newspeak method, `EntryGenerator>>sourceFor: description`, replaces both.
The command-line build uses it too, so the IDE and the build make the same
entries.

### 2.4 The natives catalog

`eurasia/kernel/natives.tsv` names the kernel's natives and their ids; an
image is bound to it through the kernel version (now 2). The packager reads it
today from a file. It becomes a generated Newspeak module, `EurasiaNatives`
(class, side, selector, native id), generated by the eurasia build from the
`.tsv` and checked in beside InternalKernel. The packager takes it as a
module, so it works the same in the IDE and on the command line. A test fails
when the module and the `.tsv` differ.

### 2.5 The genesis runner

- Command line: `eurasia genesis.eus base.eus` (native), or `run-node.mjs`.
- In a page: a second Eurasia wasm instance, started through `eurasia.mjs`
  with a `files` option that captures what the genesis entry writes, so the
  base image comes back as bytes. It is a separate VM, so the new platform
  never mixes with the IDE's actors. The JS IDE and the Eurasia IDE both
  have it: it is JS and wasm, whatever runs the IDE.

Genesis runs at deploy time, not at the application's first load: the
deployed page starts from a base image, as the IDE's does.

### 2.6 The bundle writer

A deployed application is a folder, as JS deploys are: the base image, the
`eurasia_web.wasm` and `eurasia.mjs` it was made for, a loader page,
`custom-post.js`, the vendor scripts its platform needs (CodeMirror and the
others for Hopscotch applications) and its resources. The image runs only on
a VM of its kernel and format versions, so the bundle always ships the VM it
was made for: from the IDE, the wasm the page itself loaded; from the build,
the one it built.

## 3. Building from source

### 3.1 Today

| step | where | time |
|---|---|---|
| psoup app snapshots (`build.sh`, 20 vfuels from 296 files) | psoup | 140 s |
| psoup tool snapshots (5) | psoup | ~15 s |
| EurasiaPackager.vfuel (`ide.sh`) | psoup | ~3 s |
| packaging the IDE (104 modules) | psoup | 9.5 s |
| genesis | Eurasia native | 0.07 s |

The packager already runs on Eurasia and writes the same genesis image byte
for byte: 10.7 s on wasm with the compiler, 17.3 s native interpreted
(`COMMAND_LINE.md`).

### 3.2 The build

`EurasiaBuild`, a Newspeak application on Eurasia (Node now; the native VM
later), run by `eurasia/scripts/build.sh`:

- Input: a build list: Newspeak code, a module answering application
  descriptions (the IDE, the parser, the pretty-printer, the round-trip
  check, the attachment diff, the test runner, the demos).
- It parses and compiles each source file **once** and packages every
  application from the shared compiled modules, then runs genesis for each.
  Today each application is packaged from scratch.
- It stamps BuildInfo (sources' commits, VM commit, dirty), as `ide.sh` does.
- Output: one directory per application (section 2.6), and the tool images
  `tool/` scripts run (`parse-validate.sh`, `pretty-print.sh`,
  `round-trip-check.sh`, `run-tests.sh` switch to Eurasia by a flag, then by
  default).

Expected time: about the IDE's 10 s for the compilation everything shares,
plus each application's layout and genesis, against `build.sh`'s 155 s. This
is an estimate until 3.4's first step measures it.

### 3.3 Bootstrapping

The build is itself an image, which must be built. Stage 0 is a pinned pair:
a Eurasia VM (wasm, and the native binary when it exists) and the build image
it runs, checked in under `eurasia/stage0/` (Gilad, 2026-11-21). The stage-0
build compiles the current sources, including the current packager, whose
header writer and natives module decide the new image's kernel version. So a
kernel-version change is built by the previous VM. After a build the new pair
may replace stage 0 (an explicit step, not automatic). While psoup exists it
remains the fallback for making a stage 0 from nothing.

### 3.4 Steps

1. `EurasiaBuild` driver over the existing packager: a build list, one
   compilation shared by all applications, genesis for each. Acceptance: the
   IDE's base image equals `ide.sh`'s, byte for byte (BuildInfo aside), and
   every tool image passes its suite (typechecker tests 337/340 as on
   psoup).
2. The entry generator (2.3) and the natives module (2.4), replacing the
   Python generators and the `.tsv` read.
3. Stage 0 (3.3); `ide.sh` and `tool-image.py` become calls of the build.
4. The `tool/` scripts on Eurasia images. psoup's `build.sh` keeps building
   vfuels until the psoup IDE is retired.

## 4. Deploying from the IDE

DeploymentManager gets a base `#Eurasia` beside `#Psoup` and `#Javascript`,
with the platform options of 2.2, and a **build list** action: deploy each
application of a list (and "Build IDE image", the list holding only the IDE).

### 4.1 From the JS IDE: compile the in-IDE sources

The JS IDE already carries the V5 compiler (DeploymentManager's dual
emission). It gains the packager and Eurasia's platform modules (import slots
in HopscotchWebIDE.ns, the IDE's registry: InternalKernel, Runtime,
RuntimeWithMirrors, Mirrors, Actors and the Hopscotch runtime of the Eurasia
namespace, EurasiaPackager, EurasiaNatives). Then:

1. the description's modules from a recording manifest (2.2);
2. each module's current source, as the IDE assembles it for a save: what
   has been accepted in the IDE, whether or not it has been saved to disk.
   A method being edited and not yet accepted is not included;
3. the entry (2.3), and the packager's `buildGenesisFrom:...` over these
   strings, with the natives module;
4. genesis in a second wasm instance (2.5), and the bundle (2.6).

Time: the packager's compilation, which is the whole cost; a few seconds for
an application, more for the IDE.

### 4.2 From the Eurasia IDE: deploy the bytecode

The running image already holds every class compiled to the running VM's
bytecode: the IDE's modules, the platform's, and every accept. A genesis
image needs the kernel's classes, the application's module classes and an
entry; all of them are live. So the Eurasia IDE makes the genesis image
without parsing or compiling:

1. the description's modules from a recording manifest, as live classes;
2. the entry, compiled by the IDE (one small class, by mirrors);
3. a **rooted snapshot** (4.3): the heap reachable from the kernel module,
   with the kernel module's `application` slot replaced by the entry;
4. genesis in a second wasm instance, and the bundle.

The bytecode matches the running VM by construction. Expected time: writing
the image (about 8 MB for the IDE) and genesis, on the order of a second for
the IDE; to be measured.

Building the IDE itself is the main case: it is Save Image without the
session (the IDE's classes and the platform, with fresh state).

### 4.3 The rooted snapshot (VM)

A native beside `vm snapshot` (operation list, section 6):

    vm snapshotFrom: root replacing: pairs keepSources: aBoolean

answers, as a ByteArray, a genesis image of the objects `root` reaches,
where each reference to the first object of a pair is written as the second.
It writes no frames and no actors (as `vm snapshot` writes no frames). It
keeps each object's sequence number, so identity hashes are unchanged, and the
roles that name reached objects (kernel classes); roles 17, 32, 36 and 41 are
left for genesis to set. The symbol table is a WeakArray, so symbols nothing
reached are written as nil. `keepSources:` is the platform's
`keepsSources` (2.2); with false, methods' source
fields are written as nil. Rust, in `eurasia-snapshot` (the reachability walk
of the collector, then the image writer), with replay coverage like
`vm snapshot`'s.

The kernel module copied with the replaced slot is a copy made in Newspeak
(`vm clone:`) before the call, so the live kernel is untouched.

### 4.4 Guarding against the live image

Deploying from bytecode captures what is loaded, not what is in the files:

- **Drift.** Accepted changes not yet saved to disk are included (as in
  4.1), but so is anything a
  hot-load left behind that a fresh build would not have. The from-source
  build (section 3) stays the reference. A **bytecode comparison** checks a
  deploy against it: for each method of the two genesis images, the same
  selector and the same bytecode and literals. It runs in the build's tests,
  and as an option of the deploy.
- **Leaks.** A method literal planted by an evaluator or the debugger can
  reach IDE objects, and then the image holds them. The native answers, with
  the bytes, the count and size of what it wrote; the deploy reports it, and
  reports any reached object that is an instance of an application module
  class (a module instance means session state got in).
- **Provenance.** BuildInfo says the image was built from a live image (the
  IDE's own version, and `live` for dirty), not a commit it cannot vouch
  for.

### 4.5 One code path for both IDEs

4.1 and 4.2 differ only in step 3, making the genesis image. The
description, the recording manifest, the entry generator, the genesis runner
and the bundle writer are shared. The Eurasia IDE can also deploy from
source (4.1), which is how the comparison of 4.4 runs in the IDE.

## 5. Order of work

1. **3.4 step 1**: the command-line build driver. The quickest measurable
   gain, and it proves the shared-compilation build.
2. **2.1's change, 2.2's descriptions and platform definitions, 2.3 and
   2.4**: the entry compiled top-level, the description, platform
   definitions with `keepsSources`, the entry generator and the natives
   module, which every later step uses.
3. **4.3 and "Build IDE image" on Eurasia** (4.2 for the IDE alone), with
   4.4's comparison against the build's IDE image.
4. **4.1**: Eurasia deploys from the JS IDE.
5. Build lists in the IDE, stage 0 (3.3), and the `tool/` scripts on
   Eurasia.

Steps 3 and 4 are independent once step 2 lands.

## 6. Limits and decisions

- **Granularity.** Images include whole modules; dropping unused classes or
  methods is later work.
- **Platforms.** Applications that need psoup's PrimordialFuel or the Croquet
  runtime cannot target Eurasia yet. Of psoup's primitive pragmas, only the
  file primitives (130, 128) are mapped.
- **JS deploys from the command line.** The JS IDE itself is deployed from an
  IDE today. A command-line JS build (JSPackager run by `EurasiaBuild`) would
  fit section 3, but is not part of this design.
- **Decided (Gilad, 2026-11-21):** stage 0 is checked in (3.3); sources
  follow mirrors, by the platform's `keepsSources` (2.2); the build list is
  Newspeak code (3.2). Staging the IDE image for a server (what
  `serve-web.sh` serves, and a developer's setup generally) is left out of
  "Build IDE image" for now, to be designed before Eurasia is published on
  the Newspeak site.
