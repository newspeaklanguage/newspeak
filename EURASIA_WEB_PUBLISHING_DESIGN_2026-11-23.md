# Publishing the Newspeak web sites on Eurasia

Design, 2026-11-23. Status: draft; open questions decided (§5).

Goal: serve bracha.org, blog.bracha.org and newspeaklanguage.org from Eurasia
instead of psoup, from a build anyone can run from the repositories (not one
tied to Gilad's machine), with every page, recursively, a Eurasia page: the
blog's index links each post, and each post is its own page that boots its own
document, live as well as static.

Related: `EURASIA_BUILD_AND_DEPLOY_DESIGN_2026-11-21.md` (the build, stage 0),
`AMPLEFORTH_WEB_DEPLOY_PLAN_2026-06-30.md` and
`AMPLEFORTH_DEPLOY_TRANSCLUSION_DEPS_DESIGN_2026-07-01.md` (Deploy for Web).

## 1. Where things stand

### 1.1 The sites

All three are GitHub Pages repositories, published by pushing:

| Site | Checkout | Documents |
|---|---|---|
| blog.bracha.org | `~/gbracha.github.io` | 92 zips, 88 pages |
| bracha.org | `~/professional/web-site/AmpleforthSite` (repo `gbracha/site`) | 12 zips, 14 pages |
| newspeaklanguage.org | `~/newspeak/dev/newspeaklanguage.github.io` | 12 zips, 15 pages, plus `webIDE/` (a PWA) and `CounterApp.vfuel` |

Each site holds its documents and a runtime beside them: `AmpleforthViewer.vfuel`,
`primordialsoup.{html,js,wasm}`, `deploy-boot.js`, `jszip.min.js`, `vendor/`,
`CodeMirror/`, the PNGs, and `CroquetAmpleforthViewer.vfuel` with
`croquetpsoup.*`.

A page made by Deploy for Web (`Documents>>deployPageFor:`) is

```html
<body data-ampleforth-doc="Name">
  <div id="ampleforth-ssr"> ...the document's static text... </div>
  <script src="deploy-boot.js"></script>
</body>
```

`deploy-boot.js` rewrites the URL to `?snapshot=AmpleforthViewer.vfuel&docName=Name`,
fetches `primordialsoup.html` and replays its scripts (the VM last), and removes
the static text once the live UI mounts. No page names psoup itself: in the
blog, 85 of 88 pages are document pages that go through `deploy-boot.js` (the
others are `primordialsoup.html`, `croquetpsoup.html` and
`reified-generics.html`). **Replacing `deploy-boot.js` switches a whole site
without regenerating a page.**

### 1.2 Recursion today

- Static: correct. The blog's index (`index.html`, document Room101) links
  each post as `<a href="Post.html">`; each post page boots its own document.
  Lazy transclusions and `ampleforthLink:`s deploy as such links, eager
  transclusions inline (with eager cycles degraded to links).
- Live: not correct. Opening a post from the index (a post toggle, an
  `ampleforthLink:`) loads `Post.zip` in the page and enters it. Hopscotch's
  history pushes an id with no URL (`HopscotchForHTML5.ns`, `pushState:title:`),
  so the address bar still names Room101: reloading, bookmarking or sharing
  goes back to the index.

### 1.3 Eurasia

- `eurasia/scripts/ide.sh` builds the IDE and the document viewer
  (`EurasiaBuildList.ns`: `viewer` is AmpleforthViewer on
  `withMirrorsAndHopscotch`, so it has the compiler and the host) and stages
  them in `newspeak/out/` beside psoup's: `eurasia-ide.html`,
  `eurasia-viewer.html?docName=...` (`eurasia/web/viewer.html`).
- Sizes against psoup's:

  | | Eurasia | psoup |
  |---|---|---|
  | VM | `eurasia_web.wasm` 826 KB (245 KB gzipped) | `primordialsoup.wasm` 350 KB (123 KB) + `.js` 74 KB |
  | viewer image | `viewer/base.eus` 7.8 MB (2.3 MB gzipped) | `AmpleforthViewer.vfuel` 7.3 MB (2.2 MB) |

### 1.4 What makes the build machine-specific

1. **psoup.** `scripts/build.sh` makes EurasiaBuild's own image with
   `tool-image.py`, which runs psoup's x86-64 binary
   (`primordialsoup/out/ReleaseX64/primordialsoup`, under Rosetta on Apple
   Silicon). Building psoup needs scons and Emscripten 4.0.11.
2. **Untracked libraries.** The pages load `CodeMirror/`, `jszip.min.js`,
   `vendor/buffer-6.0.3.bundle.min.js` and `vendor/diff_match_patch-2019-07.js`
   from `newspeak/out/`, which is ignored. Only the isomorphic-git and
   lightning-fs files are tracked (`newspeak/vendor/`); single-file copies of
   CodeMirror and jszip are tracked under `platforms/webIDE/public/assets/lib/`.
   Some PNGs `ide.sh` copies come from `out/` (`privateImage.png`,
   `protectedImage.png`, `publicImage.png`).
3. **Layout.** The scripts expect `newspeak` and `primordialsoup` beside
   `eurasia` (overridable with `NEWSPEAK` and `PRIMORDIALSOUP`), and `ide.sh`
   reads from `newspeak/out/`.
4. **Deploy scripts.** `tool/deploy-*.sh` are untracked and name Gilad's
   checkouts.

## 2. Design

### 2.1 A site runtime built from the repositories

One script, `eurasia/scripts/site-runtime.sh OUTDIR`, writes everything a site
serves besides its documents:

```
OUTDIR/
  deploy-boot.js          the Eurasia boot (2.2)
  eurasia.mjs             the loader
  eurasia_web.wasm        the VM
  viewer/base.eus         the document viewer
  custom-post.js          page helpers (safeDownloadBlob)
  jszip.min.js  CodeMirror/  vendor/
  *.png                   the images the viewer's platform loads
```

It builds with `scripts/build.sh viewer` and copies only tracked files:

- The libraries are vendored in the eurasia repository (`web/vendor/`), at
  pinned versions, with their licences: CodeMirror (the `lib/` and
  `addon/display/autorefresh.js` files the pages load), JSZip, buffer,
  isomorphic-git, lightning-fs, diff_match_patch.
- The image list is the platform's: `PlatformDefinition` already answers the
  images its WebRuntime resolves (EurasiaDeployment.ns, the `resolveImage:`
  scan); the script copies those PNGs from the newspeak checkout, all of which
  must then be tracked there.

Prerequisites, documented in `eurasia/BUILDING.md`: git checkouts of
`eurasia` and `newspeak` side by side (or `NEWSPEAK` set), rustup (the
toolchain is pinned in `rust-toolchain.toml`; it installs itself), Node 22 or
later, python3. Until stage 0 (2.5) also psoup, built per
`newspeak/BUILD_NOTES.md`; `BUILDING.md` says so plainly rather than hiding it.

A GitHub Actions workflow in the eurasia repository runs `site-runtime.sh` on
Linux from clean checkouts and fails unless `viewer/base.eus` matches the
image built locally (BuildInfo aside: the build stamps it; the workflow
compares `eurasia --methods` and `--census`, which ignore it). This is the
proof the build is not machine-specific; the packaging is already byte for
byte deterministic (`docs/COMMAND_LINE.md`).

### 2.2 The Eurasia boot

`deploy-boot.js` is rewritten to boot Eurasia directly:

1. Read the document name from `data-ampleforth-doc`.
2. Load the libraries (in order, each before the VM), then `eurasia.mjs`'s
   `run` with `eurasia_web.wasm` and `viewer/base.eus`, compiler on.
3. Keep the static text until the live UI mounts (the MutationObserver as
   today).
4. Leave the URL alone: no `?snapshot=&docName=` rewrite.

The viewer (`AmpleforthViewer>>main:args:`) takes the document name from
`data-ampleforth-doc` when the page has one, else from `docName` in the URL
(as now, for `eurasia-viewer.html`).

Rollback: the psoup runtime stays on each site for a release, and
`?psoup` (or `data-ampleforth-runtime="psoup"` on the body) makes
`deploy-boot.js` replay `primordialsoup.html` as it does today. It is removed
once the sites have run on Eurasia without trouble.

`viewer.html` and the boot share their loading code, so there is one list of
libraries: `deploy-boot.js` is the canonical loader and `viewer.html` a page
that uses it with `docName` from the URL.

### 2.3 Live navigation names its page

When the viewer enters a document it loaded from the server, it pushes the
URL of that document's page, `<Doc>.html`, relative to the site root (for a
server path `dir/Name`, `dir/Name.html`), with Hopscotch's history id as the
state; going back restores the previous URL with the page. The rule is the
deploy rule: a document reached through a link or a lazy transclusion has its
own page, so its URL is that page; an eagerly transcluded document is part of
its parent's page and pushes nothing.

So the live site and the static site name the same pages: a post opened from
the index shows `Post.html`; reloading it boots that post's page; its own
links push their pages in turn, to any depth.

Where: Hopscotch's history (`HopscotchForHTML5.ns`) gets an optional URL per
pushed state; Documents supplies it when it enters a document from
`loadFromServerNamed:` in a deployed page (a page with
`data-ampleforth-doc`). In the IDE nothing changes.

### 2.4 Deploying the sites from Eurasia

Deploy for Web (`deployForWeb:whenReady:`, the document menu) must run in the
Eurasia IDE: it walks links and transclusions, loads unopened documents from
the server, zips the bundle and saves it through its two-step dialog. It has
not been run on Eurasia. Room101 (92 documents) is the case to test.

`tool/deploy-site.sh TARGET [BUNDLE]` (tracked, in the newspeak repository)
replaces the untracked scripts: it copies the site runtime (2.1) into TARGET
and, given a `deploy.<Root>.zip`, unzips its pages and documents there. It
names no checkout; the targets are arguments. It does not commit or push.

### 2.5 Stage 0

`EURASIA_BUILD_AND_DEPLOY_DESIGN_2026-11-21.md` section 3.3: a pinned VM and
build image checked in under `eurasia/stage0/`, so the build runs without
psoup. It is independent of the sites: they can move to Eurasia before it
lands, with psoup a documented prerequisite of the build until then.

### 2.6 Per site

- **bracha.org:** runtime and boot. Smallest; first.
- **blog.bracha.org:** runtime and boot, then live URLs (2.3), which matter
  most here, then a redeploy of Room101 from the Eurasia IDE (2.4).
- **newspeaklanguage.org:** the document pages as above. The demos
  (`CounterApp.vfuel`) become Eurasia builds served by `app.html`. The
  `webIDE/` PWA is a separate decision (open question 1).

## 3. Steps

1. Vendor the libraries; `site-runtime.sh`; `BUILDING.md`. Acceptance: the
   runtime built from fresh clones in a temporary directory serves
   `eurasia-viewer.html?docName=Room101` from a local server.
2. The Eurasia `deploy-boot.js` with the psoup fallback; the viewer reads
   `data-ampleforth-doc`. Acceptance: a copy of bracha.org, served locally,
   shows every page on Eurasia, and `?psoup` shows it on psoup.
3. Live URLs (2.3). Acceptance: on a local copy of the blog, open a post from
   the index, reload, and the post is shown; back returns to the index with
   its URL; a post linked from a post works the same.
4. Deploy for Web on Eurasia (2.4); `deploy-site.sh`. Acceptance: Room101
   deployed from the Eurasia IDE gives the same pages as the current site
   (diff of the unzipped bundles).
5. Publish bracha.org, then the blog, then newspeaklanguage.org's documents.
   Each is checked live before the next.
6. The CI workflow (2.1).
7. Stage 0 (2.5); psoup leaves `BUILDING.md`.

## 4. Risks and checks

- **Browsers.** Eurasia's compiler generates wasm modules at run time. Test
  Chrome, Firefox and Safari, desktop and iOS, before step 5; if Safari fails
  to compile, the boot passes `jit: 0` there (the viewer is usable
  interpreted, slower).
- **First render.** Time a large post (an Emmanuel-era document) on Eurasia
  against psoup; large documents edit slowly on Eurasia today, though the
  sites mostly view.
- **Compression.** Whether GitHub Pages gzips `.eus` (and `.vfuel`) is not
  checked. It is no worse than today either way; if it does not, a smaller
  viewer image (open question 2) matters more.
- **Caching.** Pages and the image change together on a deploy; the boot
  fetches `viewer/base.eus` with a version query (the build stamp) so a
  browser does not pair a new page with a stale image.

## 5. Decisions (Gilad, 2026-11-23)

The four open questions of the first draft are settled:

1. **newspeaklanguage.org's webIDE moves with the site.** When
   newspeaklanguage.org moves to Eurasia, its PWA moves to the Eurasia IDE
   too (the service worker's file list becomes `eurasia.mjs`,
   `eurasia_web.wasm`, `ide/base.eus`). An interim step is allowed: offer
   Eurasia on the sites alongside psoup, without swapping psoup out yet. The
   `?psoup` / `data-ampleforth-runtime` switch of §2.2 then runs the other way
   during that period: psoup stays the default and Eurasia is opt-in
   (`?eurasia`), until the swap.
2. **No smaller viewer for now.** A viewer without sources is interesting as
   an option, but documents could not be edited in it, so it would be a third
   variant beside the IDE and today's viewer. Skipped.
3. **Croquet moves to Eurasia.** Croquet on Eurasia is untested, and there are
   no Eurasia Croquet pages yet. Setting them up is the next piece of work,
   ahead of the site steps of §3: build a Croquet viewer image
   (`CroquetAmpleforthViewer` on Eurasia), stage pages for it beside
   `eurasia-viewer.html`, and test a shared session between two tabs.
   **Status (2026-11-23):** working locally. See "On Eurasia" in CROQUET_NOTES.md:
   `eurasia-croquet.html?app=viewer|ide` (platform/Eurasia/CroquetRuntime.ns).
   Not yet on any site.
4. **Old `?docName=` URLs stay as they are.** The new boot honours `docName`
   in the URL as described above; no redirect to `<Doc>.html`.
