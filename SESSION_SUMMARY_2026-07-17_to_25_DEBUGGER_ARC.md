# Session Summary 2026-07-17 → 2026-07-25: The Debugger Arc + Platform Helper Parity + Full Deployment

## Scope

One long session (multiple context compactions) taking the NS2JS platform from
"broken-thread links that sometimes render" to a working post-mortem debugger with
accurate positions, block frames, restored locals, and statement-level Continue —
then platform-helper parity with psoup, a repo mirror, and a full rebuild + deploy
to every target.

## The authoritative technical record

**`DEBUGGER_STATE_2026-07-22.md`** (committed `a36be3d`) is the deep handoff: what
works, the architecture map, the gap analysis vs. a true Smalltalk debugger with
structural causes (capture-at-unwind vs. suspend-at-raise; the generator
compilation axis as the true-resume endpoint), the recommended next-step queue
(closure metadata → intrinsic stub frames → per-frame restartBci → generator
feasibility spike), and — critically — **§5, the hard-won rules**: the three
coordinate systems, uniform-precedence left-associative binary operators, the
Stage-2 "on:do: can never catch a *thrown* NS exception" rule, sentinel blind
spots, wrapper-scope visibility, the harness/spy toolkit. Read it before touching
any debugger code. Round-by-round bug history with root causes lives in the
Claude auto-memory (`project_ns_to_js_transpiler.md`).

## Commits (newspeak repo, master; mirrored to webide-ai-access via `6102c59`)

- `78647b6` — the debugger arc itself (8 files; see its commit message for the
  full feature list: eval boundary + chain cut, raw-catch simulator guards,
  transplant resolution incl. primitive receivers and DoIt-homed records,
  send-site bci instrumentation, block shadow wrappers, locals capture/restore,
  statement-level Continue).
- `a36be3d` — DEBUGGER_STATE handoff report.
- `945b81e` — platform helper parity (below).

## Post-report work (2026-07-23 → 25), NOT covered by DEBUGGER_STATE

### Platform JS helper parity (`945b81e` + primordialsoup `cd66263`)

Gilad hit: saving an Ampleforth document from the **JS** IDE failed —
`safeDownloadBlob()` (called by `WebFiles.ns` as `window safeDownloadBlob: n
blob: b`) exists only in the psoup deployment, injected via emscripten `--post-js`
from `primordialsoup/meta/custom-post.js`. NS2JS deploys never got it.

- Verified scope: `safeDownloadBlob` is the ONLY custom helper — custom-post.js
  contains just it, the deployed psoup JS tail has no other non-emscripten
  globals, and a sweep of every `window …:` send in the .ns sources found no
  other non-standard names.
- Fix: the NS2JS compiler prelude (`Newspeak2JSCompilation.ns`) now has a
  **"Platform helper parity"** verbatim section mirroring custom-post.js —
  top-level classic-script functions, so they land on `window`. Every NS2JS
  deploy is self-contained.
- Drift guard: both copies cross-reference each other; custom-post.js (canonical,
  psoup-is-canonical doctrine) states that new helpers must be mirrored into the
  prelude in the same change. **custom-post.js was previously UNTRACKED** — it is
  now under version control for the first time (primordialsoup repo, branch
  `extraRevs`, commit `cd66263`).
- NS string literals embed the JS with doubled apostrophes; the embedded JS was
  extracted and syntax-checked in the harness before committing.

### Mirror, rebuild, deploy-everywhere (2026-07-23 → 24)

- **webide-ai-access is a WORKTREE** at `~/newspeak/dev/web/webide-ai-access`
  (checkout of the branch in the main tree fails with "already used by
  worktree"). Mirror = `git merge master` **run in that worktree**, one
  directional, matching prior practice. Done: `6102c59`.
- Full `tool/build.sh` rebuild; verified the fresh `HopscotchWebIDE.vfuel`
  carries the helper source (deploys made FROM it will emit it).
- Deployed to **four** targets (the deploy-scripts memory previously knew two):
  1. `tool/deploy-newspeak-org-webIDE.sh` → `~/newspeak/dev/newspeaklanguage.github.io/webIDE/`
     (auto-bumps `sw.js` pwaVersion; now 908).
  2. `tool/deploy-gbracha-github-io.sh` → `~/gbracha.github.io/` (flat).
  3. `tool/deploy-ampleforth-runtime.sh <target>` → refreshes ONLY the shared
     Ampleforth runtime (viewer vfuel + VM + deploy-boot.js) in a deployed
     content site; content untouched. Applied to the newspeaklanguage.github.io
     site root AND to **bracha.org's checkout:
     `~/professional/web-site/AmpleforthSite`** (repo `gbracha/site`, branch
     `main`) — this path was undocumented and had to be hunted.
  4. `tool/deploy-ampleforth-site.sh` exists for CONTENT publishing (site
     bundles) — not needed for code-only refreshes.
- All target repos committed (`6818748`, `0e1aaf8`, `4c111fa`).
- **The agent shell cannot push to GitHub**: no keychain credential is readable
  non-interactively, no SSH key. Copies + commits are automatable; `git push` in
  each target repo is Gilad's step. (His pushes of the previous day's commits
  confirmed his side works.)
- Still pending at session end: Gilad's pushes of the three target-repo commits,
  and a fresh JS-IDE deploy from the new psoup IDE (the deployed
  `HopscotchWebIDE.js` on the sites predates the helper until then).

## Meta-lessons (Gilad's own framing)

1. **Knowing the Newspeak rules properly is essential** — the final Continue bug
   was pure language precedence (`a <= b - c` ≡ `(a <= b) - c`), now a standing
   memory rule.
2. **JS coercions hide type errors** — `true - 0 → 1` silently; the failure
   surfaced as a `0 ifTrue:` DNU far from the cause, swallowed by a backstop.
   When a backstopped computation silently misbehaves, spy the live deployed
   methods (class objects expose them under the protected mangling `_$sel$`) and
   look for `r === NLRSentinel` with `NLRPayload.value` = a backstop handler's
   return value.
3. Validation layering that worked: parse-validate → compile the edited .ns with
   the DEPLOYED compiler + Writer + `new Function` → psoup test suite →
   harness behavioral probes with monkey-patch injection to prove downstream
   machinery before shipping a fix.

## State at session end

Debugger: working and Gilad-verified (accurate highlights, block frames, locals
in slots, statement-level Continue that provably skips completed statements).
All sources committed and mirrored; all vfuels rebuilt and deployed everywhere;
benchmarks: full debug apparatus costs −17%/−11% on the two send-dense
fibonacci micros, ≤~4% on realistic workloads, zero on the production axis
(`emitShadowFrames` / `emitSendSites` off). Next work queue: DEBUGGER_STATE §4.
