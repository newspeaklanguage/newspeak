# Eurasia: a baseline compiler, design

**Date:** 2026-11-19
**Status:** Approved (Gilad, 2026-11-19: Rust compiler, native interpreted
for now). Stage 1, the spike, done (section 9). Stage 2, every instruction,
done, with the first of stage 3's inline caches (section 10). Stage 3, sends
without the general path (section 11), done; more inline caches (section
12), uncommitted.
**Context:** `EURASIA_PERFORMANCE_2026-11-19.md` (the interpreter is about
1.7x behind psoup; sections 6 to 12 say interpreter tuning has run its
course), the arena and nursery designs (objects addressable as base plus
offset; a write barrier in one place), `EURASIA_M7_SNAPSHOTS_REPLAY_DESIGN`
(replay and checkpoints).

## 1. Goals and constraints

- **Speed where it matters most: the browser.** The IDE and deployed
  applications run on the wasm build. The first target is code generated
  as WebAssembly at run time; native comes second.
- **Nothing a program can observe changes.** Compiled code makes the same
  natives calls in the same order, allocates the same objects in the same
  order, and reaches the same safepoints, so replay logs, checkpoints and
  collections are the interpreter's. What replay records is host
  operations, callbacks, prints, times, random bytes and checkpoints, all
  through natives or at safepoints; interrupt polling is not recorded, so
  compiled code may poll less often (at calls and back edges).
- **The interpreter stays** for cold code, the debugger (detached
  activations, stepping, `continueAt:`), a step limit, simulation roots and
  anything the compiler does not handle; switching between them must be
  cheap and possible at any call or safepoint.
- **Safe Rust in the VM.** The generated code runs in the wasm sandbox (on
  the web, and natively if section 4's option holds); the only `unsafe` is
  where the host calls a generated function, which the web host already
  allows for its exports.

## 2. The model: a baseline compiler over the interpreter's frames

A **baseline** (template) compiler: each V5 instruction becomes a fixed
sequence of wasm, with no cross-instruction optimization at first. What
it removes is the interpreter's own cost (the profile's loop and dispatch,
about half of the time): fetching and decoding, the dispatch branch,
keeping the instruction pointer and the stack length in memory, and the
calls into `send` and `activate_with`.

**Compiled code keeps the interpreter's frames.** A compiled method runs on
the VM's operand stack (`Vm::stack`) and pushes the same `Frame`s, with
the same layout: receiver, arguments, locals, operands. It writes the
frame's instruction pointer (the bytecode index) before any call out or
safepoint. Consequences:

- **Collections and checkpoints see interpreter state.** The roots are the
  same; a checkpoint's machine state is the same; a restored image runs in
  the interpreter until its methods are compiled again.
- **Deoptimization is a jump to the interpreter**: at any call out or
  safepoint, the frame is already an interpreter frame at a known bytecode
  index. The debugger and the Simulator need nothing new.
- **Mixed stacks are free**: a compiled method may call an interpreted one
  and the reverse, through the same frame stack.

The price is memory traffic (the operand stack in linear memory, not wasm
locals). It is the right first step: correct by construction, and a later
stage can keep the top of the stack in wasm locals between calls.

## 3. What compiled code does, instruction by instruction

- **Pushes, stores, literals, branches**: as `run_simple`, on the operand
  stack in linear memory; literal Values are read from the method's
  literals (a heap read: the arena moves only at collections, so its base
  is reloaded after any call that can allocate).
- **SmallInteger arithmetic and comparisons**: inline, with the overflow
  checks `small_integer_op` makes; otherwise a call to the runtime.
- **Sends**: a per-site inline cache in the compiled code's data (class,
  then a tag: getter slot, setter slot, or method), checked inline:
  - getter or setter hit: the slot is read or written inline (with the
    write barrier inline: a comparison with the nursery boundary and a bit
    test, the runtime only when it remembers);
  - method hit: a call to the runtime's activation (`activate_with`), which
    runs the callee compiled if it is compiled, interpreted otherwise;
  - miss: a call to the runtime's full send, which also fills the site's
    cache.
- **Returns**: inline for a local return; non-local return, closures'
  creation and activation, `thisContext` and eventual sends through the
  runtime.
- **Safepoints**: after every instruction that can allocate (sends, closure
  creation, array creation), compare the allocation counter with the
  safepoint threshold, as the event loop does, and return to the
  interpreter's loop when it is due. The countdown for interrupts runs at
  calls and back edges.

## 4. Running generated wasm

**On the web.** The VM is a wasm module; generated code is a separate wasm
module per compiled method (or per batch), built by the VM in Rust (a small
emitter; the encoding is simple) and instantiated by the host's JavaScript:
`WebAssembly.Module(bytes)`, imports the VM's memory and its runtime
functions (exports of `eurasia_web.wasm`), its exported function added to
the VM's function table. The VM calls compiled code through that table
(`call_indirect`); cross-module calls in V8 and SpiderMonkey are cheap.
Compiling is synchronous (`new WebAssembly.Module`) for small modules;
large batches can use the asynchronous API between turns.

**Natively. Decide:**
- **A. Run the VM itself as wasm under an embedded wasm engine
  (wasmtime)**, so native and web are one target and one compiler. The cost
  is the wasm build's speed natively; the interpreter on wasm (Node) runs at
  about 0.65x the native build. With compiled code, the gap matters less.
- **B. A second backend with Cranelift**, from the same compiler front end,
  generating native code directly. Faster natively; two backends to keep
  identical, and a JIT's executable memory (MAP_JIT on Apple silicon).
- **C. Native stays interpreted** for now; the browser is what matters.
Recommended: **C now, A or B decided after the web compiler works**, with
measurements (the wasm build under wasmtime against native).

## 5. When to compile, and invalidation

- **Tiering**: a per-method counter of activations and back edges; at a
  threshold (to be tuned, about 1000) the method is compiled; until then it
  is interpreted. Methods compile one at a time at first.
- **The code cache** maps a method (by its sequence number, which
  collections do not change) to its compiled function. Compiled code holds
  no heap references of its own: literals are read through the method, and
  inline caches hold class Values that the cache's epoch (as the global
  lookup cache's, cleared at every collection, commit and program change)
  invalidates.
- **A method changes** only while unfrozen (`Method>>bytecode:`) or by a
  commit; both clear the code cache and the inline caches. Frames already
  running compiled code continue in the interpreter at their bytecode
  index.

## 6. Determinism, checked

- The replay tests run with compilation on (a threshold of 1, to compile
  everything) and must replay identically.
- A **differential mode**: run with compilation off and on and compare
  outputs, the kernel tests in particular (as debug against release now).
- `GC_STRESS` with compilation on (collections in the middle of compiled
  code's calls).

## 7. Stages

1. **Spike (a few days)**: the emitter, the runtime ABI and the host's
   instantiation, for a handful of instructions (pushes, SmallInteger
   arithmetic, branches, self sends of methods, returns): enough to run
   MethodFibonacci compiled in Node and in the browser, measure it against
   the interpreter, and measure the call overhead between compiled code and
   the VM. Go or no-go on section 4's web design.
2. **Every instruction**, with the runtime fallbacks; compilation on for the
   whole test suite (threshold 1), differential and replay checks green.
3. **Inline caches and inline accessors, the write barrier inline**;
   benchmarks.
4. **Tiering and the code cache**; the IDE on it.
5. **Native: section 4's decision.**
6. **Later**: the top of the operand stack in wasm locals; inlining of small
   methods; type feedback from the inline caches.

## 8. Open questions

- **Decide:** section 4 (native).
- **Decide:** the compiler's language: Rust, inside the VM (proposed: no
  bootstrapping questions, and it runs where the VM runs), or Newspeak
  (closer to the project's spirit, but it would run on the interpreter it
  replaces, and compile itself).
- Code size and compile time in the browser: per method, or per class or
  batch; measure in stage 1.
- The interaction with the IDE's own hot code (the editor, the
  colorizer): which methods tier up first, and whether a snapshot should
  carry compiled code or recompile after a restore (proposed: recompile; a
  snapshot stays VM-independent).

## 9. Stage 1, the spike: results

**What it is.**
- `eurasia-core/src/compiler.rs`: a wasm encoder and a template compiler for
  a subset (pushes and stores of parameters, locals and constants, `self`,
  `nil`, `true`, `false`, `pop`, `dup`, every branch, the inline common
  selectors `+ - < > <= >= = & |` on SmallIntegers, ordinary, self and
  implicit-receiver sends, and returns). A method using anything else is not
  compiled. Control flow is a loop around a `br_table` over the basic blocks.
- **The trampoline**: the event loop answers `Completion::Compiled(i)` when the
  top frame is a fresh activation of a compiled method (at the top level only;
  a callback's loop stays interpreted); the web host calls function `i` of its
  table with the VM's address, then `Vm::continue_after_compiled`. Compiled
  code calls the runtime through `eurasia_rt_*` exports, each borrowing the
  VM for its own duration: sound without the event loop's borrow.
- **Sends** go through `eurasia_rt_send`, which makes the send as the
  interpreter does (same lookup, same frames) and answers whether it
  completed, whether it pushed a compiled callee's fresh frame (then called
  directly, inside wasm), or that the interpreter must continue. Before a
  compiled callee, a due safepoint sends it to the interpreter's loop, so
  collections fall where they would. Non-SmallInteger operands, a
  non-Boolean condition and anything else unusual leave the frame at that
  instruction for the interpreter.
- **Tiering**: beside each method's bytecode in the heap's code table, its
  activation count or its compiled function's index; not saved in
  snapshots. (A first version kept it as a ninth word in every method
  object, which made the native interpreter 10% to 13% slower on DeltaBlue
  and Richards: method objects are scanned by lookups, and their size
  shows. Found by bisecting against the committed build; moved to the code
  table, the native numbers are back within noise.) `Host::install_code`;
  the web host's `install_code` import compiles and instantiates the module
  (`new WebAssembly.Module`, importing the VM's memory, table and runtime
  functions) and adds its function to the VM's table (exported and growable,
  `eurasia-web/build.rs`). `EURASIA_JIT=n` in `run-node.mjs`, `jit` in
  `eurasia.mjs`'s options. Off when recording (the recording host installs
  no code).

**Correctness.** The kernel tests on wasm with every method compiled at its
first activation (`EURASIA_JIT=1`; 857 methods compiled) and at its third:
the same 620 outcomes as the native interpreter, and no module refused.
(The mock harness used to check the templates in isolation caught one bug
in its own test bytecode, not in the compiler: parameters are numbered from
1; the compiler now refuses the others, as the interpreter does.)

**Speed.** The benchmarks on wasm under Node, runs per second, interpreted
against compiled at the 100th activation (85 methods compiled):

| Benchmark | interpreted | compiled | gain |
|---|---:|---:|---:|
| MethodFibonacci | 23.4 | 50.4 | 2.2x |
| SlotRead | 26.9 | 62.8 | 2.3x |
| SlotWrite | 22.1 | 50.3 | 2.3x |
| DeltaBlue | 31.2 | 64.4 | 2.1x |
| ParserCombinators | 3.1 | 5.8 | 1.9x |
| NLRLoop | 65.3 | 117.8 | 1.8x |
| Richards | 40.0 | 70.0 | 1.75x |
| Splay | 71.7 | 122.6 | 1.7x |
| NLRImmediate | 242.2 | 375.6 | 1.55x |
| ClosureFibonacci, ClosureDefFibonacci | 17.2, 11.4 | 16.7, 11.0 | none: closures are outside the subset |

That is with every send still through the runtime's full send (no inline
caches yet), the operand stack in memory, and dispatch through a
`br_table` at every jump. Compiling is cheap: compiling every method the
kernel tests run (857 modules, instantiated synchronously) did not change
their run time.

**Against psoup in the browser.** The same benchmarks in one Chrome session,
psoup's wasm build (`primordialsoup.html?snapshot=BenchmarkRunner.vfuel`)
against Eurasia's (`index.html?snapshot=...&jit=100`), runs per second:

| Benchmark | psoup wasm | Eurasia interpreted | Eurasia compiled | compiled / psoup |
|---|---:|---:|---:|---:|
| SlotWrite | 42.1 | 22.8 | 50.1 | 1.19 |
| SlotRead | 65.6 | 28.0 | 62.8 | 0.96 |
| NLRLoop | 166 | 69.7 | 116 | 0.70 |
| MethodFibonacci | 69.4 | 24.3 | 45.7 | 0.66 |
| NLRImmediate | 787 | 268 | 371 | 0.47 |
| Splay | 240 | 80.1 | 115 | 0.48 |
| DeltaBlue | 136 | 43.7 | 63.1 | 0.46 |
| Richards | 153 | 49.9 | 66.6 | 0.43 |
| ParserCombinators | 14.9 | 3.4 | 5.7 | 0.38 |
| ClosureFibonacci, ClosureDefFibonacci | 55.8, 33.4 | 18.3, 12.2 | 17.5 to 31.4, 11.5 to 20.5 | 0.3 to 0.6 (not compiled; noisy) |

The send-heavy benchmarks are where the full send through the runtime costs
most: stage 3's inline caches.

**Go.** The web design (section 4) works: separate modules sharing the VM's
memory and table, calls in both directions, the interpreter taking over at
any send or exit. Next, stage 2: every instruction (closures, non-local
return, literals, indirect locals, the remaining sends), so that whole
programs run compiled; then stage 3's inline caches, which the profile says
are where most of the remaining time is.

## 10. Stage 2: every instruction, and accessor inline caches

**What changed.**
- **Every method compiles.** The common instructions inline; every other one
  as a call to the runtime's `step`, which runs that one instruction as the
  interpreter does. Common-selector and super sends are real sends;
  SmallInteger arithmetic that overflows or meets other operands is the
  common-selector send. Literals and indirect locals are read (and written)
  inline.
- **Entries.** Compiled code can take a frame back at any block start: the
  method's start, each closure body (a closure's body is inline in its
  method's bytecode, so one function runs the method and its closures), each
  jump target, and after each call into the runtime. `run(vm, regs, entry)`;
  the code table keeps each compiled method's entries. A frame the
  interpreter continued (after a callee that was not compiled, a safepoint, a
  poll) is compiled again at its next entry, and closures are compiled with
  their method, counted against it.
- **Registers.** The VM keeps, at a fixed address, what compiled code would
  otherwise ask for: the stack's address and height, the top frame's layout,
  receiver and literals, nil, true and false, the arena's address and the
  nursery boundary, the lookup cache's epoch, whether a safepoint is due. It
  refreshes them after every call that lets compiled code go on; compiled
  code reads them with loads. (The first version of stage 2 called the
  runtime for each, three to ten calls per send and entry, and was slower
  than stage 1.)
- **Inline caches for accessors** (stage 3's first piece). Each send site of
  no or one argument, ordinary, self or implicit-receiver, keeps a class,
  an epoch and a slot in globals of its module. On a hit (the receiver an
  object of that class, the epoch the lookup cache's, the slot within its
  size; for a setter not frozen, not a value, and young or already
  remembered) the slot is read or written inline, with no call. The cache is
  filled from what the runtime's send found: a getter or setter of the
  receiver itself, from the global lookup cache. Every flush of the lookup
  cache (collections, commits, program changes) changes the epoch.
- **Non-local return.** A `^` from a closure whose home's caller is a
  compiled frame on the host's stack unwinds the wasm frames in between
  (`UNWOUND`), and that caller goes on as after a completed send, instead of
  everything going back to the interpreter.
- **Interrupts.** Backward jumps count down and poll every 64 (`tick`).
- **Where compiled code does not go on.** After a call, only if the frame is
  the one it was, at the instruction it expects (an activation native, such
  as `terminateTo:` or `continueAt:`, can cut frames back or move a frame),
  with no collection since; a return or non-local return only after a return
  instruction. Anything else is the interpreter's. (Found by the kernel
  tests: `terminateTo:` cut frames back under compiled code.)

**Correctness.**
- The kernel tests with every method compiled at its first activation (2648
  methods; none refused): the native interpreter's 620 outcomes. Also under
  GC stress (a collection after every 64 allocations). Both in
  `scripts/web-tests.sh` (the stress run with `STRESS=1`).
- `EurasiaCompiledGCProbe.ns`: a compiled method whose receiver a collection
  in the middle of the method moves. A collection leaves a safepoint due,
  which compiled code checks after every call; the VM also refuses to let it
  go on after one. With both checks removed, every round fails (the negative
  control); with either, none does.
- All gates green: check, genesis, kernel, reflection, replay, web, native GC
  stress. The native interpreter is unchanged (within noise).
- **Not done: recording with compilation on.** Compiled code's runtime calls
  take the web host itself, so a recording host would not see the host
  operations made from compiled code; recording keeps compilation off. A
  replay check of compiled code needs the host in effect during compiled
  code to be the recorder.

**Speed.** One Chrome session, the browser pane, runs per second; psoup's wasm
build against Eurasia compiled at the 100th activation (two runs each, the
mean; the stage-1 column from section 9's Chrome table):

| Benchmark | psoup wasm | stage 1 | stage 2 | stage 2 / psoup |
|---|---:|---:|---:|---:|
| SlotRead | 65.6 | 62.8 | 423 | 6.4 |
| SlotWrite | 42.1 | 50.1 | 228 | 5.4 |
| ClosureFibonacci | 55.8 | 17.5 to 31.4 | 40.8 | 0.73 |
| NLRLoop | 166 | 116 | 118 | 0.71 |
| MethodFibonacci | 69.4 | 45.7 | 48.7 | 0.70 |
| Richards | 153 | 66.6 | 92.1 | 0.60 |
| Splay | 240 | 115 | 138 | 0.58 |
| ClosureDefFibonacci | 33.4 | 11.5 to 20.5 | 18.8 | 0.56 |
| DeltaBlue | 136 | 63.1 | 72.0 | 0.53 |
| NLRImmediate | 787 | 371 | 312 | 0.40 |
| ParserCombinators | 14.9 | 5.7 | 5.8 | 0.39 |

Where the time goes now (Node's profiler): the runtime's side of each call
(the send, the activation, the registers) and the entries (every compiled
callee's entry fills the registers and loads them). Next, for stage 3:
- method sends from an inline cache: the activation without the lookup,
  and the callee's frame pushed without the general path;
- closure creation and closure activation (`value`) without `step` and the
  native;
- the top of the operand stack in wasm locals, so that most instructions do
  not touch memory;
- recording with compilation on (above).

## 11. Stage 3: sends without the general path

Stage 2 left about 70% of the time on the runtime's side of each call (Node's
profiler: compiled code itself was 31%). Stage 3 takes the common cases of a
send out of the general path, guided by counting what each send resolved to.

**What changed.**
- **Method inline caches.** Every ordinary, self, super, implicit-receiver
  and common-selector send site has an inline cache of four globals: the
  receiver's class, the epoch, a slot or target, and a kind. When the lookup
  cache resolves a send to an ordinary method that is already compiled, the
  VM pushes the callee's frame itself and answers `CALLEE`, and the site
  caches a *target*: an index into a VM table of what the activation needs
  (the method, its function, code, literals' offset and count, mixin, locals,
  arguments, where the receiver comes from), deduplicated by method and
  receiver and cleared with the lookup cache. A hit calls the runtime's `call`
  with the target, which pushes the frame and sets only the registers a frame
  push changes. Pushing a frame allocates nothing, so the checks after a
  general call are not needed.
- **One `after_call` per send.** A site's paths (accessor, indexed native,
  cached method, general send) share one copy of the code after the call: a
  second copy made accessor-heavy code 30% slower in V8.
- **The cache is filled before the callee runs.** A compiled callee runs
  inside the caller's `after_call`, and its own sends change the registers
  the fill reads; filled after, method caches never filled.
- **Common selectors are sends with an arity.** The compiler knows each
  common selector's arity (`COMMON_SELECTORS`), so those sends get sites and
  go through the lookup cache like ordinary sends, after SmallInteger's fast
  path for the arithmetic and comparisons. (They were 26M of
  ParserCombinators' sends, each through the full send.)
- **Indexed natives inline.** `size` (Array, String, ByteArray), `at:`
  (Array; String and ByteArray through a new register, the byte store's
  address) and `at:put:` (Array, not frozen, young or remembered) run in
  compiled code when the site's cache holds the native and the receiver has
  that format, for ordinary and self sends.
- **Closures.** A `value` send that the lookup cache resolves to a closure's
  `value` native, to a closure whose method is compiled, pushes the closure's
  frame directly and enters its body. Closure creation is a runtime call of
  its own (`closure`) rather than `step`.
- **Returns.** Compiled code keeps the literals' offset and count in locals
  loaded at entry, so a return refreshes only the stack, the arena, the
  safepoint and the depth, not the caller's frame registers. A `^` outside
  every closure body (in an inlined block) compiles as a local return.
- **The interpreter too:** a non-local return cut the frames with
  `Vec::split_off`, a new vector per return (13% of NLRImmediate); it now
  truncates in place.
- **Program arguments on the web host** (`eurasia_add_arg`, `args` in
  `eurasia.mjs`; in `run-node.mjs`, the arguments after the snapshot), to
  run one benchmark at a time.

**Correctness.** The same gates as stage 2: the kernel tests with every
method compiled at its first activation (2648 methods) give native's
outcomes, also under GC stress; the compiled-GC probe; check, genesis,
kernel, reflection, replay. The native interpreter (`benchmarks.sh`):
NLRImmediate about 500 to 600 (the in-place cut), DeltaBlue 105.5 (as
before), Richards 112 (117 to 120 before, with runs as low as 106: noise or a
small loss, to watch).

**Speed.** Node 26, runs per second, every method compiled at its first
activation; stage 2 is the same measurement before this work:

| Benchmark | stage 2 | stage 3 | psoup wasm (Chrome, section 10) |
|---|---:|---:|---:|
| SlotRead | 490 | 475 | 65.6 |
| SlotWrite | 367 | 346 | 42.1 |
| NLRLoop | 120 | 248 | 166 |
| MethodFibonacci | 51.3 | 91.2 | 69.4 |
| ClosureFibonacci | 42.1 | 57.7 | 55.8 |
| Richards | 93.9 | 136 | 153 |
| DeltaBlue | 74.3 | 119 | 136 |
| Splay | 142 | 196 | 240 |
| NLRImmediate | 313 | 602 | 787 |
| ClosureDefFibonacci | 19.3 | 29.4 | 33.4 |
| ParserCombinators | 5.0 | 9.5 | 14.9 |

**What is left.** Each cached call still crosses into Rust to push a frame
(the VM's frames are a Rust vector, with an `Rc` of the code), and each
return crosses back; closure creation allocates an activation for its
defining frame. Next:
- frames compiled code can push and pop itself (a frame record in wasm
  memory), so that a compiled-to-compiled call is a wasm call;
- polymorphic inline caches (megamorphic sites refill every miss);
- inline caches for SmallInteger receivers, and for natives other than the
  indexed ones;
- the top of the operand stack in wasm locals;
- recording with compilation on (section 10).

## 12. Stage 3, continued: the sends that still missed

Counting what each send through the general path resolved to (temporary
counters in `compiled_send`, removed) showed, per DeltaBlue run: 16M `=`
sends resolving to `Object>>==` (common selector 13 has SmallInteger's fast
path, so it had no site at all); 13M implicit-receiver reads of an
enclosing object's slot (19M in Richards); 8M `bitAnd:` and `bitOr:` in
Richards (SmallInteger receivers, which no site could hold); 9M closure
`value:` sends; 2M to 9M refills at polymorphic sites; 5M methods that only
answer self (Splay).

**What changed.**
- **Two entries per site.** A site has two entries (class, epoch, slot or
  target, kind, object: ten globals); a hit copies the entry's kind, slot
  and object into locals that every path reads. A fill takes the first
  entry if it is empty, stale or of the receiver's class, else the second.
- **SmallInteger receivers.** A site holds SmallInteger as a class
  (`Regs::small_integer`); methods, `==` and the bit operations cache for
  SmallInteger receivers.
- **Fast-path selectors get sites.** The arithmetic and comparisons keep
  their inline SmallInteger code; when the operands are not both
  SmallIntegers the send goes through a site (the runtime still tries the
  fast path first). `=` on objects is the main beneficiary.
- **New kinds, run in compiled code:** `==` (`IC_IDENTICAL`, any receiver);
  SmallInteger's `bitAnd:`, `bitOr:`, `bitXor:` with a SmallInteger
  argument; an implicit-receiver read of an enclosing object's slot
  (`IC_OUTER_GETTER`: keyed by the frame receiver's class, the object in the
  entry; every collection changes the epoch, so the object's bits stay
  valid); a method that answers its receiver (`IC_RETURN_SELF`).
- **Closures through `call`.** A closure `value` send that pushed the
  closure's frame caches a target with `CLOSURE_TARGET` set and the native's
  id; `call` pushes the frame again.
- **`MISS`.** When `call` cannot enter the cached callee it answers `MISS`
  and the site makes the general send. (Answering `INTERPRET` looped
  forever: a closure of the wrong arity at a cached site sent the frame to
  the interpreter at that instruction, which re-entered compiled code
  there. The compiled kernel tests caught it, in
  `testRepeatingTimerInvalidCallback`.) `call` lost its `ip` argument.

**Correctness.** The gates of section 11: check; the kernel tests with
every method compiled (2648) give native's outcomes, also under GC stress;
the compiled-GC probe (0 of 20 rounds failed); genesis, kernel, reflection,
replay. The native interpreter is unchanged: DeltaBlue 104, Richards 111,
NLRImmediate 600.

**Speed.** Node 26, runs per second, every method compiled at its first
activation:

| Benchmark | stage 3 | now | psoup wasm (Chrome, section 10) |
|---|---:|---:|---:|
| SlotRead | 475 | 490 | 65.6 |
| SlotWrite | 346 | 373 | 42.1 |
| NLRLoop | 248 | 259 | 166 |
| MethodFibonacci | 91.2 | 86.7 | 69.4 |
| ClosureFibonacci | 57.7 | 61.2 | 55.8 |
| Richards | 136 | 185 | 153 |
| DeltaBlue | 119 | 175 | 136 |
| Splay | 196 | 226 | 240 |
| NLRImmediate | 602 | 623 | 787 |
| ClosureDefFibonacci | 29.4 | 30.5 | 33.4 |
| ParserCombinators | 9.5 | 10.5 | 14.9 |

Richards and DeltaBlue now beat psoup. Splay, NLRImmediate,
ClosureDefFibonacci and ParserCombinators do not.

**What is left.** In DeltaBlue almost every send now hits a cache. The
remaining cost is the call and the return, which cross into Rust (per run:
50M `call`s, 63M returns). That is section 11's first item, frames that
compiled code pushes and pops itself. Still on the general path:
allocation natives (`new:`, `basicNew`: 4M to 5M in ParserCombinators and
Splay), Float arithmetic and comparisons, string concatenation, and
`valueWithArguments:`.

