# Deploying applications on Eurasia from the IDE: plan

**Date:** 2026-11-19
**Status:** Plan; nothing done yet. To be picked up after the compiler work
starts, or alongside it.
**Proposed by:** Gilad: the deployment manager should offer Eurasia as a
deployment target, with options (with or without reflection).

## 1. What exists

- **The packager is Newspeak** (`EurasiaPackager.ns`): it compiles modules
  with the V5 compiler (`Newspeak2V5BytecodeCompilation`) and writes
  snapshot format 8. It runs on psoup today, and the compiler also runs on
  Eurasia (the reflection tests), so it can run inside the IDE on either.
- **It already builds from source text.** `buildGenesisFrom: kernelSource
  app: appSource modules: sources prefixes: platformPrefixes platform:`
  takes strings; only `main:args:` (the command-line entry) reads files and
  writes the result. The natives table is read from a file
  (`readNativesTable:platform:`).
- **The IDE has the parts:**
  - the V5 compiler, for the deploys' dual emission;
  - `Eurasia` as a platform namespace, so the `platform/Eurasia` modules
    (the kernel fork `InternalKernel`, Actors, Runtime, Mirrors,
    RuntimeWithMirrors) are available as drafts and installs;
  - import recording (`RecordingManifest`, `importsRecorder`), which the JS
    deploys use to find the modules an application needs.
- **The deployment manager's model fits.** A `DeploymentConfiguration` has
  a `base` (`#Psoup`, `#Javascript`) and the options `hasHopscotch`,
  `hasMirrors`, `hasNode`, `hasZircon`; `deploy:on:` dispatches on the
  base. A third base, `#Eurasia`, with `hasMirrors` for reflection, is the
  shape Gilad proposed.
- **Multi-file deploys exist**: the JS deploys build a zip with JSZip.
- **The command-line path** is the reference: `scripts/ide.sh` (and
  `scripts/generate-ide-entry.py`) generates a genesis entry for an
  application, finds its modules, packages them, runs genesis natively
  (`eurasia genesis.eus base.eus`), and stages the page (`web/ide.html`,
  `web/eurasia.mjs`, `eurasia_web.wasm`).

## 2. What is missing

1. **The entry, generated in the IDE.** An application deployed from the IDE
   is a class following the app conventions (`packageUsing:`, `main:args:`
   with a platform). The packager's genesis takes an application *module*
   whose `main:args:` runs on the Eurasia runtime. The IDE must generate that
   module, as `generate-ide-entry.py` does today: its slots the modules the
   application imports (found by import recording, as for JS deploys), its
   `platformOver:` building the platform from Runtime (or
   RuntimeWithMirrors), its `main:args:` instantiating the application.
   Porting the Python generator to Newspeak inside the deployment manager is
   the main piece of work.
2. **The natives table in the IDE.** `kernel/natives.tsv` (214 entries) lives
   in the eurasia repository. Options:
   - generate a small Newspeak module from it (`EurasiaNatives.ns`) as part of
     the eurasia build, checked against `natives.rs` by the same test that
     checks the table today; the IDE imports it like any module;
   - or carry the table as metadata in the kernel fork.
   Recommended: the generated module, since the table must change with the
   VM and the check already exists.
3. **Genesis.** The packager produces a genesis image; the native VM runs it
   once to produce the base image. The IDE on psoup cannot run Eurasia.
   Options:
   - ship the genesis image, and let the deployed page run genesis at its
     first load (the web host loads any snapshot; genesis's own saving step
     would be skipped or done to the origin's storage);
   - the IDE on Eurasia runs genesis itself (later).
   Recommended: ship the genesis image; first measure how long genesis takes
   for a typical Hopscotch application in the browser.
4. **The VM artifacts.** A deploy carries `eurasia_web.wasm`, `eurasia.mjs` and
   a loader page whose snapshot format, kernel version and bytecode version
   match the image (the wasm exports the versions; the page should check
   them). The build must stage them where the IDE is served (`out/`), and the
   deployment manager fetch them from there, as it fetches the JS deploys'
   environment files.
5. **The configurations and the UI.** Base `#Eurasia`, with:
   - **reflection**: none (Runtime), mirrors (Mirrors, RuntimeWithMirrors),
     or mirrors and the compiler (adds the compiler modules, for
     applications that compile at run time: workspaces, REPLs; much larger);
   - **Hopscotch**, as for the other bases.
   The configuration presenter gains the base and the reflection choice; the
   known configurations gain 'Eurasia Web App' and 'Eurasia Web App with
   Reflection'.

## 3. Steps

1. **The natives module**: generated from `natives.tsv` by the eurasia build;
   the table test checks it too. The packager reads the table from it when
   given one, from the file otherwise (the command line keeps working).
2. **The packager's in-memory entry**: `packageGenesisFor: app modules:
   modules natives: table ^<ByteArray>`, used by `main:args:` and by the IDE.
3. **The entry generator in Newspeak** (port of `generate-ide-entry.py`),
   with the module set from import recording. Check: for the IDE itself, it
   generates the same entry as the Python script (`EurasiaIDE.ns`).
4. **The deployment**: `deploy:on:` for `#Eurasia`: entry, packaging, the
   genesis image, the loader page and the VM files in a zip, downloaded as
   the JS deploys are.
5. **Genesis at first load** in the loader page; measure it.
6. **The configuration UI and known configurations.**
7. **Checks**: deploy a small Hopscotch application and the benchmark app from
   the IDE; run them in the browser pane; compare the benchmark app's image
   with the one `scripts/benchmarks.sh` builds (same modules, same image
   but for the entry's source).

Estimate: one to two weeks; steps 3 and 4 are most of it.

## 4. Open questions

- Should the IDE on Eurasia run genesis itself, so that a deploy ships the
  base image (faster first load, no genesis code in the deployment)?
- Should the loader page offer saving images and restoring them (the IDE's
  own page does, through the origin's storage), or is that the
  application's business?
- Speed: deployed applications run at the interpreter's speed until the
  compiler lands (about 1.7x behind psoup; NS2JS is far faster in a
  browser). Eurasia deploys are for what Eurasia gives (one VM everywhere,
  snapshots, replay, actors); the compiler changes the trade-off.
