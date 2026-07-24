# NS2JS Debugger: State, Gaps vs. a True Smalltalk Debugger, and Hard-Won Knowledge
### 2026-07-22 — handoff report (committed as 78647b6)

This report is written for a future session starting with no context. It records
(1) what the JS-platform debugger can do today and how the machinery fits together,
(2) precisely what still falls short of a true Smalltalk debugger and the *structural
reason* for each gap, and (3) knowledge that was expensive to acquire and would be
silently lost in a fresh context. Read section 5 before touching anything.

---

## 1. What works today (verified by Gilad in the IDE, 2026-07-22)

- **Unhandled exception → debugger with a real stack.** An unhandled signal — in an
  evaluator doIt or in event-driven code — engages a *reconstruction unwind*: the
  throw builds a shadow stack through per-method catch wrappers, and the boundary
  (the evaluator's own catch, or the expatriate boundary + `NSDebugHook`) transplants
  it into a broken simulated thread the Debugging UI presents like any other.
- **Frames**: methods, closures (`[] in …` positioned *inside* the block), the doIt
  itself, DNU frames on primitive receivers. Restart-quality: receiver + arguments
  captured, plus (new) **method-level locals restored by name** — the slots pane
  shows real at-failure values.
- **Accurate bcis**: each frame highlights the actual failing send, via
  callee-selector derivation (free for selectors sent once per method) plus
  send-site instrumentation for ambiguous selectors (`emitSendSites`).
- **Continue = statement-level restart**: the outermost frame re-enters at the start
  of the *failing top-level statement* with locals restored; earlier statements'
  side effects do not repeat. Sound-entry derivation from decoded bytecode
  boundaries; degrades to full restart when soundness can't be guaranteed.
  The per-frame **restart button** intentionally keeps full-restart semantics.
- **Frame evaluation, inspection, stepping** (post-restart), `return:from:`,
  terminate — the Stage-1 simulator debugger, unchanged.
- **Define-and-continue** works: MNU → define the method → Continue → completes
  without re-running earlier statements.

Cost (Chrome, vs clean 2026-07-20 baseline): MethodFibonacci −17%,
ClosureDefFibonacci −11% (send-dense micros with ambiguous selectors / hot closure
creation); realistic benchmarks (DeltaBlue, Richards, ParserCombinators, Splay)
within ~4% of parity. NLRImmediate/NLRLoop swing wildly run-to-run — never trust a
single sample of those two. All overhead sits behind two compiler flags
(`emitShadowFrames`, `emitSendSites`, both default ON) = the debug deployment axis;
a production deploy flips them off and pays nothing.

## 2. Architecture map (where everything lives)

| Piece | File | Key names |
|---|---|---|
| Per-method + per-block shadow wrappers, send-site stores, temp hoisting, prelude | `Newspeak2JSCompilation.ns` | `shadowWrap:methodNode:`, `blockShadowWrap:…`, `noteSendSiteOf:`, `methodNode:` (two-pass; owns all per-method state), `emitShadowFrames`, `emitSendSites`, prelude `NSShadowPush/NSReconstructing/NSDebugHook/NSShadowFrames` |
| Unhandled-signal fallback, handler chain, eval-boundary chain cut | `KernelForJS.ns` | `signal` (sets `NSReconstructing` + throws when unhandled & hook armed), `handlerChainCut/handlerChainRestore:`, `protectedBodyOf:` (rethrows *thrown* NS exceptions past every on:do: — read its comment before touching any guard) |
| Transplant, bci derivation, statement entry, restart machinery | `BytecodeSimulatorForJS.ns` | `transplantMethodMixinNamed:…` (+ class-chain fallback), `transplantFrameFor:…`, `ordinarySendSitesOf:`, `transplantBciFor:callee:site:`, `bciAtOrAfterSourceStart:in:`, `statementEntryAmong:in:`, `SimulatedActivation restartBci` / `resetForStatementRestart`, `SimulatedThread resume` (statement restart on #broken), `guarded:` (dual guard) |
| Eval boundary, transplant orchestration, locals restore, statement matcher | `MirrorsForJS.ns` | `evaluate:with:` (chain cut + boundary catch), `threadForShadowFrames:exception:doItSource:receiver:scope:`, `doItSimMethodFor:…`, `restoreLocalsOf:from:method:in:`, `transplantDebugInfoFor:…`, `statementRestartBciFor:in:`, `calleeSelectorFor:exception:` |
| Debugger arming, UI | `HopscotchWebIDE.ns` (`armDebuggerFor:platform:`), `Debugging.ns` (Continue → `subject resume`), `Browsing.ns` |
| Emission shape tests | `Newspeak2JSDualEmissionTesting.ns` (21 tests) |

Shadow record shape (prelude `NSShadowPush`, innermost first):
`{mixin, selector, receiver, args, site, blk, localNames, locals}` —
`site` = source offset stored by ambiguous-send instrumentation (0 = none);
`blk` = block's source start (>0 marks a closure activation of the home method);
`localNames`/`locals` = source names + values of the method's hoisted temps
(null when the method has no temps; block wrappers pass none).

## 3. Gaps vs. a true Smalltalk debugger — and *why*

Ordered roughly by user-visible impact. Each entry states the structural cause; the
distinction that matters is **capture-at-unwind** (what we have) vs.
**suspend-at-raise** (what psoup/Smalltalk have).

### 3.1 No true resume from the raise point
psoup suspends the thread *at* the signal with the whole activation state live;
`resume` just returns from `signal`. We reconstruct *during the unwind*, after the
JS frames are already dying: operand stacks (partially evaluated expressions) exist
only implicitly in dead JS frames, and nothing can recover them. Hence Continue is
*statement-level restart*: sound, but the failing statement's own side effects
repeat, and resuming "after the failing send with value X" (Smalltalk's
`resume: X` / proceed-with-value) is impossible.
**The only genuine fix** is the *generator compilation axis*: compile the debug
deployment's methods as JS generator functions with sends via `yield*`, giving real
suspendable continuations — any frame can suspend the logical stack; the debugger
resumes it; no reconstruction at all. This is a major compilation fork with an
unmeasured per-send cost; it was explicitly identified as the honest endpoint and
deferred. If pursued: it replaces the entire shadow-stack apparatus for that axis,
and Gilad has already rejected *re-run–based* trampolines (S2) — generators are
acceptable because they are true suspension, not re-execution.

### 3.2 Kernel `_js`-intrinsic frames are invisible
`Exception>>signal`, `Array>>do:` (the M4 `_js for:` index loop), and every other
intrinsic-bearing kernel method have no V5 bytecode twin, so their frames are
captured (mixin+selector in the record) but skipped at transplant. In
`{1.2.3} do: [:e | e zork]` the `do:` frame is missing between the block frame and
the DNU frames. **Why**: dual emission attaches bytecode only to intrinsic-free
methods; the M4 kernel loops *must* be `_js` (a block's `^` returns the NLR
sentinel, which native iteration would swallow — and pure-NS phrasings cost speed).
**Options** (proposed, undecided): display-only stub frames — the source *text* is
available via the record's metadata source index, so a frame could show `do:` with
receiver/args but no highlight, no stepping, no restart; needs record-nil guards on
`numArgs`/restart paths. Or accept the gap.

### 3.3 Loop state inside intrinsic kernel frames is unrecoverable
Even with 3.2's stubs, re-running `do:` from its start is the only continuation
option — the loop index lived in a dead JS frame. Statement restart of a doIt whose
single statement is a `do:` therefore re-processes all elements. Structural; only
the generator axis fixes it.

### 3.4 Block frames are approximate
They exist and are positioned correctly, but: labeled as the home method
(psoup shows `[] in foo` — our `[] in DoIt` label comes from psoup-side doIt
presentation, not from block records); block *arguments* are captured in the record
but **not mounted** (they would land in the home method's arg slots and the slot
mapper would present them under wrong names); block-level temps and copied values
are neither captured nor restored (a block's own `| t |` lives block-scoped inside
the closure function — same catch-visibility problem method temps had, fixable the
same way via block-wrapper-scope hoisting); restart of a block frame silently
restarts the *home method* from bci 1. **Next concrete step**: closure metadata —
capture block params/temps in the block wrapper, synthesize a `SimulatedClosure`
with the real `initialBCI` (the V5 side knows it at dual-emission time; would need
to be baked into the block wrapper like `blk` is), mount args/temps in the block
frame's own coordinate space, and label frames with a closure marker. The old
`squeak/Newspeak2V8Compilation.ns` was flagged as a precedent worth mining.

### 3.5 Locals restore skips closure-captured temps
A method temp captured by any closure lives in a **remote vector** on the V5 side
(one frame slot holds an Array; `pushIndirectLocal` indexes it), while the JS
capture holds the plain value. Writing the raw value into the vector's slot would
corrupt it, so those temps stay nil in the debugger, and any method using remote
vectors is also excluded from statement restart (`statementEntryAmong:` bails on
opcodes 245–247 because the transplant cannot recreate the vectors the skipped
prologue would have built). **Fix path**: at restore time, allocate the vectors
(the recompiled DebugInfo knows `remoteVector`/offsets) and populate them; then the
245–247 bail can be lifted. Moderate, well-scoped.

### 3.6 Statement restart only for the outermost frame; inner frames restart fully
`restartBci` is computed only for the bottom frame (Continue's target). The
per-frame restart button always does `resetForRestart` (bci 1, locals cleared) —
which is *correct* Smalltalk restart semantics, but "restart this frame at its
current statement" for arbitrary frames would need `restartBci` computed per frame
(cheap to add — same matcher, run per mounted frame; parse cost per frame was the
only reason it's bottom-only).

### 3.7 Multi-frame Continue re-executes the callee chain
Continue restarts the outermost frame's failing statement, which re-invokes
everything below it. Restarting the *innermost* frame instead and returning its
value into the caller is impossible without caller operand stacks (see 3.1).
This is inherent to capture-at-unwind; do not attempt "resume innermost then
resume caller" — it double-executes the callee (analyzed and rejected).

### 3.8 Raw JS errors don't reconstruct
`NSReconstructing` is set only by the unhandled-*signal* path. A raw TypeError
thrown by emitted code (a compiler bug, an alien) unwinds without building shadow
frames and presents as a frameless broken thread with a normalized reason.
Fixable in principle (boundary could set a "reconstruct raw errors" mode and
rethrow once), but the value is low — NS-level failures all route through `signal`.

### 3.9 Exception semantics inside the simulator are pre-Stage-2
Simulated code gets the surrogate-frame handler walk (`run:protectedBy:handler:` by
method identity), with simulated signals rerouted to JS throws. Full unification
with the kernel's resumable handler stack is designed but blocked: a handler shell
invoked from a full-speed signal would need its wrapper's NLR to unwind across a
*nested* `runToCompletion:` loop into the outer chain, which the walk cannot do.
Also parked in this family: `restartWithLookup:` unsupported; unwinding across a
pending unwind-protect frame refuses (psoup parity).

### 3.10 Known parked bugs / debts
- **JS-side hot-load of MirrorsForJS doesn't swap methods** (reflective
  self-update; NS-Mixin↔runtimeMixin wiring inconsistencies). Workflow is
  psoup-reload + fresh deploy; fine in practice, confusing if forgotten.
- **Audit debt**: `escape:`'s private/protected branches capture raw `apply`
  results (an in-flight NLR sentinel from a full-speed handler completion would
  become a simulated value); `HopscotchForHTML5` raw-call scan; kernel `sort:`
  comparator handoff. None observed failing yet.
- **`evaluate:with:` a non-empty scope Map** hit
  `Assertion failed: Invalid enclosing object index` in the harness (receiver =
  the runtime module). Untriaged — possibly harness-receiver-specific; the IDE's
  workspace evals go through a different path. Worth a look before relying on
  scope-carrying evals.
- **Sentinel flythrough of simulated unwind-protect frames**: an NLR passing from
  full-speed code through the simulator abandons simulated protector frames
  without running them (documented, accepted).
- DoIt frames show synthetic `t1`/`t2`-style slots for the psoup-style
  ctxt/scope arguments (observed round 1, cosmetic, never chased).

## 4. Recommended next-step queue

1. **Closure metadata round** (3.4 + 3.5 together): block wrapper captures its own
   params/temps + baked `initialBCI`; remote-vector reconstruction at restore;
   lift the 245–247 statement-restart bail; `[] in foo` labels.
2. **Stub frames for intrinsic kernel methods** (3.2) — small, high display value;
   needs Gilad's call on fidelity.
3. **Per-frame `restartBci`** (3.6) — trivial extension if wanted.
4. **Generator compilation axis feasibility spike** (3.1/3.3/3.7): measure V8
   generator-per-send cost on the benchmark suite before designing anything.
5. Simulator exception unification (3.9) when the nested-loop unwind problem gets
   a design.

## 5. KNOWLEDGE THAT WILL BE LOST WITHOUT THIS SECTION — read before editing

**Language / platform rules that cost debugging rounds this arc:**
- **Newspeak binary operators are uniform-precedence, LEFT-ASSOCIATIVE.**
  `a <= b - c` is `(a <= b) - c`. Emitted JS then *silently coerces* bool−num
  (`true - 0 → 1`) and the failure surfaces far away as `0 ifTrue:` DNU — swallowed
  by any `on: Exception` backstop into a silent wrong result. Parenthesize all
  arithmetic feeding comparisons.
- **Three coordinate systems, do not mix:**
  (a) *bytecode locals space*: `pushLocal k` is locals-only; simulator
  `localToTemp:` = `numArgs + k + 1`.
  (b) *DebugInfo `zeroOriginOffset`*: **combined space** (params 0..numArgs−1,
  locals from numArgs); `DebugMapper getValueOf:` reads `tempAt: offset + 1`
  directly — write restores exactly where the mapper reads (`offset + 1`,
  NO numArgs).
  (c) *source coordinates*: bciMap interval starts ARE parser node starts
  (1-based, `addDebugInfo: node message` → the *message* node, not the send);
  a doIt's map is a standalone parse of the bare expression (`sourceStart` 0,
  bias 0 vs a fresh parse); a deployed method's map is class-source based
  (subtract `sourceStart`, and subtract the fresh parse root's own start as bias).
- **The bciMap marks only sends and stores** — never a statement's first
  instruction. A sound statement entry = start of the maximal pure-single-push run
  into the statement's first *method-level* send/store (closure bodies are inline
  in the bytes but skipped at method level — instruction-boundary decoding must
  skip `pushClosure` bodies via bytes 3–4).
- **Since Stage 2, `on:do:` can NEVER catch a *thrown* NS exception** —
  `protectedBodyOf:` deliberately rethrows them ("past every matching
  opportunity"). Any guard meant to catch throws (simulator drivers, boundaries)
  must be a raw `_js try:catch:with:`. Three separate bugs came from this.
- **Raw `_js call:` sites are sentinel blind spots**: a Stage-2 handler completing
  is a non-local *return*; check `=== NLRSentinel` on a FRESH temp (never a
  variable a handler also writes) and propagate.
- **`zeroOriginOffset`-style method temps are block-scoped inside the wrapper's
  try** — anything the catch must see (site slot, hoisted temps) must be declared
  in the wrapper block; a stray inner `let` silently shadows and the catch captures
  stale nils.
- **Simulator display queries must never raise** — `simulatorLimitation:` raises
  are for execution paths; presentation uses nil-returning variants
  (`newspeakClassApplying:startingAt:`).
- **Primitive receivers**: the kernel is patched FLAT onto JS prototypes; named
  mixin applications don't exist as prototypes. Resolution falls back to the NS
  class chain (`newspeakClass` / `superclass`), reading MM records off the mixin.
- **`ex message selector` for `doesNotUnderstand:` callees**: dNU is invoked by the
  DNU catcher, so its selector never appears at the call site — map it to the MNU's
  message selector when deriving the caller's bci.
- **Common selectors (V5 176–207: + - value value: at: size , and: or: … )** are
  excluded from both send-site instrumentation and callee derivation — by design.
- **`methodNode:` is two-pass** (pass 1 discarded, computes NLR flag + send
  counts); per-method translator state (`sendSiteAmbiguous`, `shadowSelector`,
  `hoistTempsFrom`) must be sig-set at entry and nil'd at exit or DoIts/initializers
  emit garbage. `currentSelector` is STALE during body passes (pattern applies
  after) — that's why `shadowSelector` exists.
- **The doIt is a synthetic `DoItWith:` method** (JS side) compiled from the *bare*
  expression; the V5 side compiles the same bare expression as `#DoIt`
  (`DoItIn:With:` pattern, 2 args ctxt+scope). Shadow records homed there are
  unresolvable by name and must mount on the freshly V5-compiled doIt method.
- **`parsing` API**: `parsing CommonParser new parseExpression:` /
  `parseMethodDeclaration:` — the module itself does NOT respond to parse messages
  (a DNU here was silently eaten by a backstop for a full round).

**Harness / validation techniques (scratchpad `idetest/`, session-portable):**
- Headless IDE: truncate the deploy at `var app = ns.$HopscotchWebIDE()` →
  `IDECore.js`; load with `HopscotchWebIDE.sources.js` **and, since ~2026-07-21,
  the vendor scripts** (buffer, jszip, isomorphic-git, lightning-fs,
  diff_match_patch, CodeMirror) or the renderer hangs silently at load.
- Validate .ns edits beyond parse-validate: compile the file with the DEPLOYED
  compiler (`P.$mirrors().$compiler().$compileClassSource$within$(src, nil)` — NS
  `nil`, never JS null) + run the `JavascriptGeneration` Writer + `new Function(js)`
  to catch invalid emissions (the `return throw` class of bug).
- Emission-level tests run headlessly via
  `tool/run-tests.sh Newspeak2JSDualEmissionTestingConfiguration` + explicit dep
  files: CombinatorialParsing NewspeakGrammar NewspeakASTs NewspeakParsing
  JavascriptGeneration IntermediatesForPrimordialSoup NewspeakCompilation
  Newspeak2SqueakCompilation Newspeak2V5BytecodeCompilation Newspeak2JSCompilation.
- **Live spying on deployed private/protected methods**: class-side methods are
  reachable on the class object under the *protected* mangling
  (`AM["_$statementRestartBciFor$in$"]`) and are replaceable — wrap to log
  args/results, or stub to inject correct values and prove downstream machinery
  end-to-end before shipping a fix. Public methods live on prototypes
  (`Error.prototype.$signal` — but beware flattened copies shadowing patches;
  patch the MNU *factory* `MNU["$receiver$message$"]` to see DNUs, with
  `new Error().stack` for mangled-name JS stacks).
- An in-flight NLR is identified by `r === NLRSentinel` with payload in
  `NLRPayload` (`homeId`, `value`) — payload value 1 = a `[:e | 1]`-style backstop
  handler completing somewhere below.
- Behavioral side-effect probes without eval scope: patch a method onto
  `Number.prototype` (`$probeTick` bumping a JS global) and use it in the evaluated
  expression; scope-Map evals to the runtime receiver hit the untriaged assertion
  in 3.10.
- Benchmarks headless: `bench/` harness (BenchmarkRunner.js + sources, NO
  virtual-time-budget, perl-alarm kill, alternate variants A/B, strip
  instrumentation textually for controlled comparisons). macOS has no `timeout`.
- Corpus analysis: `multiplicity.py` in the scratchpad decodes all `new MM(...)`
  records in a deploy (V5 opcode lengths: ≤215→1, 216–237→2, 238–253→3,
  254–255→4; ordinary sends 64–111 short / 250–254 ext,
  sel = b2 | ((b3 & 15) << 8)).

**Process rules in force:** psoup-reload + fresh deploy (JS hot-load of mirrors is
broken); full rebuild required for compiler changes; benchmark gate before any
emitted-code-shape change (Gilad baselines with psoup `BenchmarkRunner.ns`);
NLR benchmark pair swings — median of several runs; commit only on Gilad's
explicit request; the deployed-IDE harness can only test what is deployed — fixes
to mirrors/simulator need Gilad's loop, but monkey-patch injection can pre-verify
the surrounding chain.

## 6. Where the details live

Session summaries and design docs in this directory:
`NLR_DEBUGGER_DESIGN_2026-07-16.md` (§6 sentinel NLR, §8 resumable exceptions,
Stage-3 lazy shadow stack), `M4_SENTINEL_NLR_IMPL_PLAN_2026-07-17.md`,
`BYTECODES_V5_SPEC_2026-07-13.md` (opcode tables §3, commons §4).
Auto-memory (`~/.claude/.../memory/project_ns_to_js_transpiler.md`) has the
round-by-round history of this arc with per-bug root causes.
