# primordialsoup crash triage — 2026-11-09

## Status update (same day): fixes ported — COMMITTED `50e66ff` on primordialsoup `extraRevs` (IDE-tested by Gilad); H4 below committed as `bb7ccb3`

| Fix | Change | Verified by |
|---|---|---|
| F1 mark-stack overflow | `heap.cc/.h`: spill to a growable side stack instead of FATAL; freed after marking | 3M and 10M probes: old VM aborts, fixed Release+Debug pass |
| F2 float safepoint (upstream `2e39917`) | `FLOAT_FUNCTION_1/2` read the value before allocating | GC stress: old VM SIGBUS on `sin` and `**`, fixed passes |
| F3 string NUL (upstream `38521c8`) | applied as-is, except `Module.HEAPU8` → module-local `HEAPU8` (emcc 4.x doesn't export it; avoids upstream's build-flag change `01798dd`) | browser: NUL inside a string reaching JS: old length 1, fixed 3 |
| F4 oddballs (upstream `338f0bb`) | `_JS_peekType` pops null/false/true | browser: callback args correct; alien stack 10→260 over 50 calls (old) vs 6→6 (fixed) |
| F5 timers in callbacks (upstream `efccdd5`) | `scheduleTurn(timeout)`, guarded by `typeof scheduleTurn === "function"`; every host page in both repos defines it globally | browser: timer started in a `setTimeout`-driven callback never fires (old), fires (fixed) |
| F6 interrupts (upstream `85290ab`) | interrupt poll on negative-delta jumps (bytecode 242) | SIGINT on `[true] whileTrue: []`: old keeps spinning, fixed prints stack and exits |
| NEW F7 int64→JS (upstream `dc52875`, **missed in the first pass**) | `_JS_pushInteger` takes int32; others go as doubles. Upstream's range test `(v >> 32 << 32) == v` is inverted (sends multiples of 2^32 down the int32 path → 0); ported with `v == (int32_t)v` | browser: 2^31→`-2147483648`, 2^32→`0`, 1.7e12→`-807049216` (old); all exact (fixed) |
| Apple Silicon mprotect | `__aarch64__ && !__APPLE__` | GC-stress controls go red only with it |

Regression: 10 native suites identical to baseline on the fixed VM, both plain and
under scavenge-every-allocation (ActivationMirror's pre-existing formatting
failures only). Real IDE booted headless on the fixed WASM (overlaying only
`primordialsoup.js/.wasm` over `newspeak/out`) and opened the class browser:
identical DOM to the old VM (7423 chars, 3677 nodes). Croquet build not tested.
`out/` not rebuilt.

**H4 is now CONFIRMED, not hypothetical.** `out/AsyncBridgeProbeAll.vfuel`
reproduces the August abort on both old and fixed VMs, and the console now shows
the VM's own last line: `vm/interpreter.cc:1159: error: Unused bytecode`, then
`Aborted(native code called abort())`, then `memory access out of bounds`. Probe 8
wraps `arr forEach: [...]` in an outer `on: Exception do:`; the callback raises
ArgumentError inside the synchronous expat, and *both* the nested turn's handler
("Exception in turn without resolver") and the outer turn's handler
("FAIL 8 ... forEach raised") run. The outer handler unwinds a turn that is
suspended inside a C primitive; the interpreter later resumes on that unwound
stack and executes garbage. Not addressed by the port.

### H4 fix — COMMITTED `bb7ccb3` (VM + kernel; needs VM *and* snapshots rebuilt together)

Invariant restored: **a dispatch activation is the bottom of its turn.**
- Marker primitive **168** (`dispatchBoundary`, always fails, our table) on
  `MessageLoop>>dispatchHandle:status:signals:count:` and `dispatchMessage:port:`,
  following the 113/116/142 marker idiom.
- Exception search (`Exception>>invokeNextHandler`) stops at it as if the stack
  ended: unhandled → handler of last resort.
- Non-local return (VM fast + slow path, and the mirror simulator) refuses to
  cross it: `cannotReturn:`.
- `finish:` from below the dispatch frame (the unhandled path) now unwinds to the
  innermost boundary and resumes exactly what was under it (the suspended outer
  frame, or the idle state with `ip_ = nil`), instead of popping one frame.
- That abandon sets `Module.dispatchAbandoned`; `expat()` then throws a JS
  `Error` instead of popping a result that was never pushed (H2). The caller's
  call-out primitive fails cleanly and Newspeak raises `Error` *in the calling
  turn, after the primitive has returned*.
- `unhandledException:` inside a synchronous callback with no last-resort
  handler abandons the callback instead of exiting the VM; top level unchanged.

Verified (scratch builds; out/ untouched):
- H4 probe, old → new: outer handler catching across the boundary → caller gets a
  clean Error and the last resort gets the original exception; NLR escaping →
  refused (CannotReturn); old VM then aborts (`Unused bytecode`, `Cannot find
  mixin application`), new runs clean. Handled-in-callback and two-level nesting work.
- AsyncBridgeProbe: no abort; probe 8 now fails cleanly and the run reaches
  probe 9, whose deliberate top-level raise exits by design (the probe says so).
- Bridge probe 14/14; IDE with new kernel boots and opens the class browser
  identically; native suites + GC stress identical to baseline (ActivationMirror
  output byte-identical); top-level last-resort and no-handler paths unchanged
  natively; old-kernel snapshots run fine on the new VM.

Compatibility: **new snapshots need the new VM** (the old VM has no primitive 168
and dies with `unimplemented code` when activating a dispatch). Old snapshots run
on the new VM unchanged. Deploys must ship VM and snapshots together.

Behavior changes to know about:
- `^` from a synchronous JS callback to a method in the calling turn is now
  `CannotReturn` (it was memory-unsafe before).
- An exception escaping a synchronous callback reaches the caller as a plain
  `Error` ("Newspeak callback ended with an unhandled exception") rather than the
  original exception, so `on: SpecificError do:` around a call-out no longer sees
  it. The original goes to the handler of last resort.
- Not handled: debugger *manipulation* (restart/return) of frames below a
  callback boundary; and resuming, from a debugger, a callback activation that
  was abandoned (its dispatch's sender has since finished). Not tested in the
  interactive IDE debugger.

Side finding: one-shot timer callbacks are run under
`on: Exception do: [:ex | (* unhandledException: ex *) ]`
(`ActorsForPrimordialSoup.ns:506-513`). Errors in timer callbacks vanish silently.
(Addressed in round 3.)

### Round 3 — COMMITTED `e6aa17c` (IDE-tested by Gilad 2026-11-09)

- **Object-valued callback arguments clobbered earlier ones** (the July bug,
  PSOUP_EXPAT_CALLBACK_ARGS_2026-07-13.md). `Module.aliens` was both the operand
  stack and the handle table, so an object argument had to stay where it was.
  Now `Module.alienTable` holds handles (grows only) and `Module.aliens` is a pure
  operand stack. Primitive 158 moves an object into the table and answers its
  handle. `expat()` restores the stack to its entry height, dropping junk from a
  marshal that failed inside the callback. `alienTableSize` moves to new
  primitive 169, since on 158 it would now consume an operand. Browser probe,
  old → new: 1/8 → 8/8 (scalar-then-object, two objects, forEach shape, five
  mixed, alien survives, stack empty between operations (old: 22 entries), clean
  after a failed marshal). The audited multi-argument callback sites are all
  compatible with true order.
- **Timer callback errors** are now reported (`Exception in timer callback:`) and
  passed on, as `EventualSend>>deliver` does for turns, so the handler of last
  resort sees them (old: silent). With no handler the VM exits, like any
  unhandled turn: a behavior change for such apps.
- **Debugger across a callback boundary.** `ThreadMirror>>isBottom:` now stops
  above a dispatch frame (168), like the 142 simulation root, and `hasSender:`
  stops at the bottom, so restart/return/step cannot reach another turn (it is
  still displayed for context). This also fixes top-level resume: native probe,
  old → new, `resume` never returned to the debugger (the resumed thread ran
  into the dispatch's `finish:` and longjmped out of the caller's turn) →
  returns, fulfilled. VM guard: `finish:` over a dispatch whose underlying turn
  has finished goes idle instead of rebuilding a dead activation.
- Regression: native suites plain + GC stress identical to baseline
  (ActivationMirror byte-identical); H4 probe 6/6, bridge probe 14/14; IDE boots
  and opens the class browser identically. NOT exercised headless: CodeMirror
  editing, whose handlers are 2-argument callbacks and now get true order.
- Found, not changed: **callback arity.** psoup applies every JS argument, so
  `forEach:` with a 2-parameter block raises ArgumentError (3 arguments); JS and
  NS2JS ignore extras. AsyncBridgeProbe probe 8 trips on exactly this.

Purpose: find out *what kinds* of bugs make the current VM crash, to inform the
new-VM design (and to decide what, if anything, is worth fixing in the C++ VM
meanwhile). Nothing in either repo was changed; all builds and probes live in
the session scratchpad and are reproduced below.

## Evidence base

1. **Project notes** (all session summaries, design docs, memory; both worktrees).
   Every recorded VM-level failure is in the **WASM build in Chrome**. No native
   crash is recorded anywhere.
2. **Sanitizers.** Debug + ASan + UBSan native ARM64 build; 16 test suites run.
   Zero sanitizer reports. (Caveat: ASan cannot see stale pointers *inside* the
   VM's own mmap'd heap — see 3.)
3. **GC-stress harness** (new; patch in the appendix). Scavenge before *every*
   new-space allocation, and actually protect from-space so a stale pointer
   faults. Validated with a positive control (known bug → SIGBUS) and a fix-flip
   (same probe, upstream fix applied → green). 10 suites then run under it:
   all pass except ActivationMirror, whose failures (`'[^2]'` vs `'[ ^2 ]'`) are
   source-formatting expectations, identical without stress.
4. **rmacnak/primordialsoup upstream.** Our fork diverged at `7af2c52`
   (2020-06-08). Upstream is still active (last commit 2026-09-26); 195 upstream
   commits since, 89 touching `vm/`. Our fork has 214 of its own.

## Findings

### Confirmed bugs, reproduced

**F1. GC mark-stack overflow is a hard FATAL** — `vm/heap.cc:67`. *Same in upstream.*
The mark stack borrows from-space (capacity = semispace/word: 128K entries at
the initial 512 KB wasm32 semispace, 2M max on 64-bit). Marking pushes every
unmarked child before popping, so any sufficiently *wide* live graph kills the VM.
- Repro (native, release VM): an `Array` of 3M fresh objects, then allocation
  churn to force a mark-sweep → `vm/heap.cc:67: error: Mark stack overflow`,
  SIGABRT, 0.7 s. Negative control: same with 1M elements → passes.
- This is the 2026-06-08 "mark-stack overflow" incident (changeset presenter
  cascade), and the likely explanation for some of the unexplained
  `Aborted(native code called abort())` reports: `FATAL` → `abort()` in WASM.
- Fix in C++ is standard: on overflow, set a flag and rescan the heap for
  marked-but-unscanned objects (or use a growable side stack).

**F2. Float primitives read a moved object after a safepoint** — `vm/primitives.cc:1104-1123`.
*Fixed upstream in `2e39917` (2024-10-26); we don't have it.*
`FLOAT_FUNCTION_1/2` cast the receiver to a local, then `RETURN_FLOAT` allocates
the result (may scavenge) and only *then* evaluates `rcvr->value()`. The
receiver has moved; the read hits from-space. Affects floor, ceiling, rounded,
sin, cos, tan, asin, acos, … and the two-argument functions.
- Repro: `(i asFloat / 7) sin` in a loop under GC stress → SIGBUS. With
  upstream's fix applied → passes.
- In production this is mostly **silent wrong answers**, not crashes: from-space
  still holds the stale bytes until reused. A crash needs the from-space to have
  been grown/freed in between.
- Audit: these are the only `RETURN_FLOAT`/`RETURN_MINT` call sites whose
  argument dereferences a heap object. The other 37 primitive safepoints follow
  the re-read-from-`I->Stack(n)` discipline correctly.

### Confirmed bugs, by code comparison with upstream (not yet reproduced)

**F3. JS→WASM string copy writes a NUL past the String object** — `vm/primitives.cc:3163`.
*Fixed upstream in `38521c8` (2024-08-17).* WASM only.
`stringToUTF8(string, addr, size + 1)` writes a terminator one byte past the
string body. When body + header exactly fill the 8-byte alignment unit, that byte
is the low byte of the *next object's header* — on 32-bit that's the mark,
remembered and canonical bits. Usually harmless (fresh string at new-space top),
but when the string is allocated in old space (large, or new space full) it
silently clears another object's flags: a lost remembered-set bit is a
classic source of later "random" heap corruption. Every JS string crossing into
Newspeak goes through here, so this fires constantly in the IDE.

**F4. Oddballs (null/false/true) are never popped from the alien stack** — `vm/primitives.cc:3130-3141`.
*Fixed upstream in `338f0bb` (2026-05-03).* WASM only.
`_JS_peekType` identifies them but leaves them on `Module.aliens`; the following
pop re-reads the same slot. This is the documented "expat callback arguments
clobbered" bug (PSOUP_EXPAT_CALLBACK_ARGS_2026-07-13.md), which was worked around
in Newspeak code rather than fixed.

**F5. Timers started inside a synchronous expat callback are never scheduled** — `vm/primitives.cc:3125`.
*Fixed upstream in `efccdd5` (2020-11-01).* WASM only.
`expat()` discards `_handle_signal`'s return value (the next timeout); upstream
passes it to `scheduleTurn`. Symptom: work queued from inside a callback stalls
until some unrelated event arrives — a plausible contributor to the "lost
rejection / hang" seen with AsyncBridgeProbe.

**F6. Send-free loops cannot be interrupted** — `vm/interpreter.cc:1633-1638`.
*Fixed upstream in `85290ab` (2023-05-20)* (different bytecode set, same fix).
Backward jumps don't check `checked_stack_limit_`, so an inlined loop with no
sends never sees an interrupt. A hang, not a crash.

### Structural hazards in the alien/callback bridge (code reading; WASM)

These are not single bugs but design properties, and they're where all the
recorded crashes cluster. Both forks share them.

- **H1. One JS array is both the handle table and the operand stack.**
  Object aliens *stay* on `Module.aliens`, and their stack position becomes their
  handle (`_JS_peekAlien` returns `aliens.length - 1`). So any push/pop imbalance
  doesn't just misdeliver one value — an extra pop deletes the most recently
  created handle, and later pushes reuse its index for a different JS object.
  This is the mechanism behind "JS sees `document.documentElement`" (A2 in the
  notes). The table also never shrinks: there is no alien GC.
- **H2. The callback result protocol assumes the handler always pushes exactly one value.**
  `pushExpat:` ends with `rawPush: (closure valueWithArguments: arguments)`; if
  that raises, the turn's `on:do:` swallows it, nothing is pushed, and `expat()`
  still does `aliens.pop()` — which, by H1, pops a *handle*. This is the
  documented "never raise inside JS callbacks" rule; the VM should enforce it
  (push `undefined` / an error marker in an ensure block) instead of relying on
  discipline.
- **H3. A synchronous callback runs the whole event queue re-entrantly.**
  `dispatchHandle:` enqueues the handler, then `finish: drainQueue` drains *every*
  pending actor, inside a nested `Enter()` while the outer turn is suspended
  mid-primitive. Turns are no longer atomic; an unrelated turn can make further
  JS calls (and callbacks) underneath someone else's half-finished primitive.
- **H4. Nested dispatch frames chain onto the suspended outer frames.**
  `ActivateSignal` → `ActivateDispatch` pushes on the current stack, so the
  callback's sender chain runs into the outer turn. Exception handler search
  (`KernelForPrimordialSoup.ns:1050-1070`) and the debugger walk straight across
  the C re-entry boundary. If a handler in the *outer* turn ever catches an
  exception from the inner one, Newspeak unwinds past a live `setjmp` frame; the
  later `finish:` longjmps to the wrong environment and the outer primitive
  resumes on an unwound stack. **Hypothesis** for the AsyncBridgeProbe abort
  (two raises in flight → `memory access out of bounds`), not yet reproduced.
- **H5. 128 KB C stack under WASM** (`TOTAL_STACK=131072`) with unbounded
  callback nesting (H3). Each level is `handle_signal → Interpret → setjmp`
  plus JS frames. Emscripten's stack lives in linear memory, so overflow
  scribbles on the heap rather than trapping. **Hypothesis**, unverified.

### Environment/test-infrastructure findings

- **On Apple Silicon, debug builds never protect from-space**
  (`vm/virtual_memory_posix.cc:74-76`, a DragonBoard workaround applied to all
  ARM64). So the Debug VM's main stale-pointer safeguard is silently off on the
  machine we develop on; it just reads `kUnallocatedByte` fill. Worth a one-line
  fix (`&& !defined(__APPLE__)`).
- `TestRunner.vfuel` is stale against the current kernel (`MessageNotUnderstood:
  OrderedMap`), and several configurations (Regex, Mirror, MemoryHole,
  AtomicInstall, V5BytecodeSimulation, Kernel) fail at load time with `NotFound`
  for dependencies `run-tests.sh` doesn't discover — those suites weren't
  exercised.
- `primitives.cc:2017-2020`: `CollectInstances` debug-asserts that the instance
  count is unchanged across a safepoint that its own comment says can change it.
  A debug-only false alarm.

## What this means for the new VM

1. **The interpreter core is not the problem.** Under GC stress at every
   allocation, the bytecode engine and the 37 other primitive safepoints are
   clean. The moving-GC rooting discipline mostly holds; its one hole (F2) was
   in a macro, which is exactly where Rust's borrow checker *wouldn't* help —
   handle discipline must be structural (e.g. primitives receive arguments only
   as handles/indices, never raw pointers, so a read after a safepoint can't
   be written).
2. **The crashes live at the boundaries**: GC resource limits (F1), the JS bridge
   (F3-F5, H1-H5). The bridge design — a shared handle/operand stack, synchronous
   re-entry that drains the queue, frames chained across the C boundary — is the
   part to *not* carry forward. The new VM's FFI/alien layer wants: a separate
   handle table with GC, a typed marshalling frame per call, callbacks that run
   only their own turn, and a hard frame boundary at re-entry that exceptions
   and the debugger respect.
3. **Fail soft.** F1 and the 2 GB WASM abort show the VM dying where it should
   raise a Newspeak-level `OutOfMemory` / degrade.
4. **Keep the GC-stress harness as a permanent test mode** — and point the same
   kind of harness at the new VM from day one; it found F2 in minutes.

## Cheap interim fixes for the C++ VM (if wanted)

Port upstream `2e39917`, `38521c8`, `338f0bb`, `efccdd5`, `85290ab`; fix the
ARM64 mprotect guard; replace the mark-stack FATAL with overflow-rescan. Each
is small. H2 could get a minimal guard (always push a result in an ensure
block). H1/H3/H4 are design-level and belong to the new VM.

## Appendix: reproduction

Scratchpad (session-local):
`/private/tmp/claude-503/-Users-gbracha-newspeak-dev-web-newspeak/471b0922-2af2-4538-8d4e-6ee3c3e8a875/scratchpad/`
— `asan/` (sanitizer build), `stress/` (GC-stress build), `probe/` (probes).

GC-stress patch (run with `PSOUP_GC_STRESS=N` to scavenge every N allocations;
build Debug):

```diff
--- vm/heap.cc
+++ vm/heap.cc
@@ -1,3 +1,4 @@
+#include <stdlib.h>
@@ -156,8 +157,18 @@
+static intptr_t stress_counter = 0;
+static intptr_t StressInterval() {
+  static intptr_t v = -1;
+  if (v < 0) { const char* e = getenv("PSOUP_GC_STRESS"); v = e ? atol(e) : 0; }
+  return v;
+}
 uword Heap::AllocateNew(intptr_t size) {
   ASSERT(size < kLargeAllocation);
+  if (StressInterval() > 0 && interpreter_ != nullptr &&
+      (++stress_counter % StressInterval()) == 0) {
+    Scavenge(kNewSpace);
+  }
   uword addr = TryAllocateNew(size);
--- vm/virtual_memory_posix.cc
+++ vm/virtual_memory_posix.cc
-#if defined(__aarch64__)
+#if defined(__aarch64__) && !defined(__APPLE__)
```

Mark-stack probe (run via `NewspeakTestRunner.vfuel` with a one-line config):

```
public class MarkStackTests new = TestContext new () (
	churn = ( 1 to: 400 do: [:i | Array new: 100000] )
	fill: n = (
		| a |
		a:: Array new: n.
		1 to: n do: [:i | a at: i put: (Array new: 1)].
		churn.
		^a size
	)
	public testWideArray3M = ( assert: (fill: 3000000) equals: 3000000 )
) : ( TEST_CONTEXT = () )
```

Float probe: `1 to: 1000 do: [:i | sum:: sum + (i asFloat / 7) sin]` under
`PSOUP_GC_STRESS=1`.

### Decision 2026-11-09: callback exceptions are reported at the innermost boundary
An exception escaping a synchronous callback is reported there (debugger with the
live stack), the callback is abandoned, and the caller's call-out fails with a
generic `Error: Newspeak callback ended with an unhandled exception`. Consequence:
an `on:do:` around a call-out cannot catch the callback's original exception.
Gilad chose this over JS-style propagation (re-signal the original exception in the
caller) because propagation must unwind the callback's frames, losing the live stack.

## H5 investigated 2026-11-09: the real limit is the HANDLE TABLE, not the C stack

Probes (scratchpad `h5/`): `D2ProbeApp` nests JS→Newspeak callbacks N deep
(`helper nest: [...]` recursively), optionally with Newspeak recursion per level
(`?pad=`); an instrumented WASM VM exports `emscripten_stack_get_current`.

- **Handle table overflow at nesting depth ~5 — silent memory corruption in release.**
  `Heap::handles_` has capacity 8 (`heap.h:439`). Every primitive call holds a
  HandleScope for its method (`interpreter.cc:809`) for as long as it runs, and a JS
  call-out waiting for its callback is still running, so each nesting level holds
  handles. The debug WASM asserts at depth 5 (`heap.h:461`). Release has no check:
  `handles_[8]` overwrites `handles_size_` (the next field), then
  `ephemeron_list_`, `weak_list_`, then writes go to an arbitrary address. Release
  probes "survive" to depth 63 or 276 by luck, then die with
  `Cannot find mixin application` / `Unused bytecode`. Likely contributor to the
  unexplained WASM crashes and the AsyncBridgeProbe abort.
- **C (shadow) stack:** 416 bytes per nesting level in release (6.3 KB in debug);
  128 KB allows about 314 levels. Under this emscripten version the stack occupies
  addresses 0..128K and grows toward 0, so an overflow wraps out of bounds and
  **traps** rather than scribbling on the heap (the original H5 fear is wrong).
  With `STACK_OVERFLOW_CHECK=2` it aborts with a clear message.
- **V8's native stack** (wasm frames live there) runs out first, at about 276
  levels with default Chrome. Raising V8's stack (`--js-flags=--stack-size=4000`)
  lets it reach 312 and hit the C-stack check instead. A RangeError thrown out of
  the middle of wasm leaves the nested `Enter()` state (environment_, handles,
  fp_/sp_/ip_) unrestored, which also corrupts.
- GC during nested callbacks is fine (GcProbeApp). Newspeak-stack overflow and
  flush inside a callback is fine at depth 1.

### H5 fix — COMMITTED `86f0ec9`

- `vm/heap.h`: `kHandlesCapacity` 8 → 512, and `HandleScope` checks for overflow in
  release too (`FATAL("Handle table overflow")`), so it can never silently overwrite.
- `vm/primitives.cc` expat: tracks `Module.callbackDepth` (restored in a `finally`).
  At depth 64 it throws `Error("Newspeak callbacks nested too deeply")` before
  re-entering wasm, so the caller's call-out fails cleanly.
- `SConstruct`: `TOTAL_STACK` 128 KB → 1 MB (debug builds use 6.3 KB per level;
  build-croquet.sh derives from SConstruct).
- Verified: `D3ProbeApp` (catching at every level, pad 0/200, three runs) corrupts on
  the old VM and reaches exactly 64 then refuses on release and debug fixed VMs, with
  a sanity workload afterwards; the uncaught chain (`D2ProbeApp`, 65 reports) has no VM
  errors; Bridge 14/14, Arg 8/8, H4 6/6, AsyncBridgeProbe identical to the pre-fix VM;
  IDE boots and opens Newspeak Source identically (7423 chars / 3677 nodes); native
  suites match baseline.
- Needs a VM rebuild only; no snapshot change.

Original proposal: (1) make the handle capacity ample (e.g. 256) and check
it in release (FATAL, never a silent overwrite); (2) cap callback nesting in the
expat (for example 64), throwing a JS Error before re-entering wasm so the caller's
call-out fails cleanly; (3) optionally raise TOTAL_STACK to 1 MB for headroom.
