# Eurasia: a baseline compiler, design

**Date:** 2026-11-19
**Status:** Approved (Gilad, 2026-11-19: Rust compiler, native interpreted
for now). Stage 1, the spike, done (section 9). Stage 2, every instruction,
done, with the first of stage 3's inline caches (section 10). Stage 3, sends
without the general path (section 11), done; more inline caches (section
12), done; frames compiled code pushes and pops itself (section 13),
done; outer sends, non-local returns and closure calls (section 14),
done; natives through `call` and in-place arrays (section 15),
done; Chrome measured, activations and closures made in wasm (section
16), done; allocation and number comparisons in wasm (section 17),
done; two closure bodies per site, a second-level cache tried and
dropped (section 18), and callbacks compiled, #doesNotUnderstand:
cached (section 19), and alien sends cached, compiled methods named
in profiles (section 20), uncommitted.
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

## 13. Frames that compiled code pushes and pops itself

Section 12 left a compiled-to-compiled call crossing into Rust twice: once
to push the callee's frame, once to pop it (in DeltaBlue, 50M `call`s and
63M returns per run, about 47% of the time). Now compiled code does both
in wasm, in the VM's own frames vector, and calls the runtime only for what
it cannot do itself.

**Step 1: a frame is a plain record.** `Frame` is `#[repr(C)]` and `Copy`,
all integers (every bit pattern is a frame), 80 bytes on wasm32:
- `code` was an `Rc<[u8]>` and is now a number: 0, the method's current
  bytecode (every frame, in practice); `k`, the VM's pinned code `k - 1`.
  `Method>>bytecode:` replaces the code of unfrozen methods only, so a
  running method's code almost never changes. When it is about to, the VM
  pins the old code for the frames running it (`pin_code_of`): they keep
  the code they began with, as before. Pinned code goes at a collection
  once no frame uses it. This path is not covered by any test.
- `activation` and `closure` are `OptValue`s, one word each, 0 for none
  (activations and closures are references, never SmallInteger 0).
- The frame serial counter moved into the registers, so the VM and
  compiled code take serials from one place.
- The inline-cache targets (`TargetEntry`) are `#[repr(C)]` too.

The layouts are checked at compile time on wasm32 (`offset_of!` against
the compiler's `FRAME_` and `TARGET_` constants), and so are the
registers'. No `unsafe` in the VM: as for the operand stack, the web host
does the one `set_len`.

**Step 2: push and pop in wasm.**
- **Publish and adopt.** Before compiled code runs, entered or continuing
  after a runtime call, the VM publishes what it needs: the frames'
  address, count and capacity (with 64 frames of room reserved), the
  targets' address, the stack's capacity, `jit_base` and whether a step
  limit is set. At every call into the VM, the host adopts the frame count
  compiled code left (`set_len`, as it adopts the stack's height).
- **Push.** A method-cache hit pushes the callee's frame in wasm when there
  is room for the frame and for its locals plus the headroom, no step
  limit, no safepoint due, and the frame and nesting limits allow it. The
  push inserts the frame's or a fixed receiver for self and
  implicit-receiver sends, fills the locals with nil, sets the caller's
  `ip`, writes the record, sets the callee's registers and runs it with
  the existing `call_indirect`. Otherwise it goes through `call` as before.
- **Pop.** A local return pops the frame in wasm when the frame has no
  activation handle and is deeper than the frame the host entered
  (`jit_base`): its caller is compiled code below it on the wasm stack,
  which goes on from the registers. The frame the host entered returns
  through `ret`: the host does not adopt the stack's height from a plain
  return. Popping that frame too was a bug: DeltaBlue failed with
  `NonBooleanReceiver 0`, found by isolating pop from push.

**Correctness.** A temporary check of the frames' invariants at every call
into the VM found nothing in the compiled kernel tests, with and without
GC stress, then was removed. The gates of section 11 pass: check; the
compiled kernel tests (2648 methods) give native's outcomes, also under GC
stress; the compiled-GC probe; genesis, kernel, reflection, replay.

**Speed.** Node 26, runs per second, every method compiled at its first
activation:

| Benchmark | section 12 | step 1 | now | psoup wasm (Chrome, section 10) |
|---|---:|---:|---:|---:|
| SlotRead | 490 | 478 | 488 | 65.6 |
| SlotWrite | 373 | 364 | 381 | 42.1 |
| NLRLoop | 259 | 269 | 293 | 166 |
| MethodFibonacci | 86.7 | 106 | 193 | 69.4 |
| ClosureFibonacci | 61.2 | 67.1 | 75.4 | 55.8 |
| Richards | 185 | 209 | 286 | 153 |
| DeltaBlue | 175 | 194 | 243 | 136 |
| Splay | 226 | 220 | 268 | 240 |
| NLRImmediate | 623 | 612 | 686 | 787 |
| ClosureDefFibonacci | 30.5 | 32.6 | 35.7 | 33.4 |
| ParserCombinators | 10.5 | 10.9 | 12.2 | 14.9 |

Every benchmark but NLRImmediate and ParserCombinators now beats psoup.

**The interpreter pays a little.** Finding a frame's code through its
method costs the native interpreter about 2 to 3% (DeltaBlue 101.7 against
98.9, ClosureFibonacci 37.8 against 36.6, the committed build and this one
alternating on the same image; Splay within noise). Recovering it would
take caching the code table's index in the frame, renumbered at every
collection.

**What is left.** Closure frames are still pushed in Rust
(`direct_closure`), and closure creation is a runtime call that makes an
activation for the defining frame. The allocation natives (`new:`,
`basicNew`), Float arithmetic and comparisons, and `valueWithArguments:`
still take the general path. Then the top of the operand stack in wasm
locals, and recording with compilation on.

## 14. Outer sends, non-local returns and closure calls

After section 13, counting the instructions compiled code still handed to
`step` showed what remained in the benchmarks behind psoup: per
ParserCombinators run, 6.4M outer sends (never compiled), 2.2M
`PUSH_NEW_ARRAY` and 1.3M non-local returns; per NLRImmediate run, 23M
non-local returns. The profiles also showed closure `value` sends pushing
their frames in Rust (`direct_closure`, 6 to 12%).

**What changed.**
- **Outer sends are sends with sites.** An outer send `d` levels out is
  rule `RULE_OUTER + d`. It looks up and caches as an implicit-receiver
  send does: keyed by the frame receiver's class and the method's mixin,
  with a fixed receiver (the enclosing object), or the frame's at depth 0.
  Its sites take every kind an implicit-receiver site takes, the enclosing
  object's slot read (`IC_OUTER_GETTER`) included, and the frame push of
  section 13.
- **Non-local returns by their own runtime call.** A `^` in a closure body
  is `Ins::NonLocalReturn`: compiled code pushes the value and calls `nlr`
  (a new import, the eighth), which runs the VM's `non_local_return`
  directly, the frame's `ip` already past the instruction as `step` leaves
  it (an upcall, `cannotReturn:` or `aboutToReturn:through:`, resumes
  there). Its answer is a call's (`after_call`); the frame never goes on.
- **Closure frames pushed in wasm.** A closure `value` send that the VM
  entered directly caches a *closure target* (`IC_CLOSURE`): for closures of
  one method whose body starts at one instruction, what their frames need
  (method, literals, mixin, function, entry block, literals' offset and
  count, argument count). The VM's table of them is `#[repr(C)]` (checked
  against the `CTARGET_` offsets), keyed by method and body, cleared with
  the lookup cache, and published like the method targets. A hit checks
  the closure in hand (its body's first instruction, its argument count,
  its defining activation's method) and, with room as for a method frame,
  pushes the frame in wasm: the receiver is the defining activation's, the
  copied values are the first locals, and it enters the body's block.
  Otherwise `call`, with `CLOSURE_TARGET` and the target's index, pushes
  it in Rust or answers `MISS`.

**Correctness.** The gates of section 11 pass: check; the compiled kernel
tests (2648 methods) give native's outcomes, also under GC stress; the
compiled-GC probe; genesis, kernel, reflection, replay.

**Speed.** Node 26, runs per second, every method compiled at its first
activation (Splay and ParserCombinators vary: three runs each, 248 to 271
and 14.5 to 14.7):

| Benchmark | section 13 | now | psoup wasm (Chrome, section 10) |
|---|---:|---:|---:|
| SlotRead | 488 | 485 | 65.6 |
| SlotWrite | 381 | 378 | 42.1 |
| NLRLoop | 293 | 444 | 166 |
| MethodFibonacci | 193 | 194 | 69.4 |
| ClosureFibonacci | 75.4 | 188 | 55.8 |
| Richards | 286 | 294 | 153 |
| DeltaBlue | 243 | 237 | 136 |
| Splay | 268 | 248 to 271 | 240 |
| NLRImmediate | 686 | 924 | 787 |
| ClosureDefFibonacci | 35.7 | 47.9 | 33.4 |
| ParserCombinators | 12.2 | 14.5 to 14.7 | 14.9 |

Every benchmark but ParserCombinators beats psoup; ParserCombinators is
within 3%.

**What is left.** Closure creation is a runtime call that allocates an
activation for the defining frame and the closure. Arrays (`PUSH_NEW_ARRAY`)
are made by `step`. The allocation natives (`new:`, `basicNew`), Float
arithmetic and comparisons, and `valueWithArguments:` take the general
send. Then the top of the operand stack in wasm locals, recording with
compilation on, and a Chrome measurement.

## 15. Natives through `call`; arrays filled in place

After section 14, the general sends left in ParserCombinators (counted, as
before, with temporary counters since removed) were natives with no inline
form: per run, 5.9M `new:`, 1.45M each of `valueWithArguments:` and
`numArgs`, 1.1M `basicNew`. Each went through `compiled_send`'s lookup-cache
probe and the selector's decoding. `Heap::push` was 5% of the profile:
`new:` and `PUSH_NEW_ARRAY` built the array's elements in a temporary
vector, then copied them into the arena.

**What changed.**
- **Native targets.** A native with no inline form, sent to the receiver
  itself (ordinary, or self or implicit to the frame's), now gets a method
  target whose function is `NATIVE_FUNCTION`. A site's hit goes to `call`,
  which runs the native as the general send would (`activate_with`, then
  the checks after a call). Compiled code pushes no frame for it.
- **Arrays filled in place.** `new:` (Array and WeakArray) and
  `PUSH_NEW_ARRAY` allocate their nils straight into the arena
  (`Heap::allocate_array_of`), as `basicNew` already did. That helps the
  interpreter too.

After this, a ParserCombinators run makes a few thousand general sends.

**Correctness.** The gates of section 11 pass.

**Speed.** Node 26, runs per second, every method compiled at its first
activation:

| Benchmark | section 14 | now | psoup wasm (Chrome, section 10) |
|---|---:|---:|---:|
| SlotRead | 485 | 480 | 65.6 |
| SlotWrite | 378 | 373 | 42.1 |
| NLRLoop | 444 | 465 | 166 |
| MethodFibonacci | 194 | 183 | 69.4 |
| ClosureFibonacci | 188 | 185 | 55.8 |
| Richards | 294 | 295 | 153 |
| DeltaBlue | 237 | 234 | 136 |
| Splay | 248 to 271 | 277 to 289 | 240 |
| NLRImmediate | 924 | 925 | 787 |
| ClosureDefFibonacci | 47.9 | 47.8 | 33.4 |
| ParserCombinators | 14.5 to 14.7 | 15.5 to 15.6 | 14.9 |

Every benchmark beats psoup's Chrome figures. The native interpreter:
ParserCombinators 7.3 to 7.9 (in-place arrays); the others as in section 13.

**What is left.** The psoup comparison is against Chrome figures measured
before this work, and these are Node's: a Chrome measurement of both is
due. Then closure creation (an activation and a closure allocated through
the runtime), allocation in wasm, Float arithmetic, and the top of the
operand stack in wasm locals.

## 16. Chrome against psoup; closures and their activations in wasm

**Chrome, both VMs.** One Chrome session (the browser pane), psoup's wasm
build (`primordialsoup.html?snapshot=BenchmarkRunner.vfuel`, served from
`out/`) and Eurasia's (`index.html?snapshot=bench.eus&jit=1`), after
section 15. psoup's figures match section 10's to within 2%:

| Benchmark | psoup | Eurasia (section 15) | ratio |
|---|---:|---:|---:|
| SlotRead | 66.0 | 438 | 6.6 |
| SlotWrite | 42.2 | 356 | 8.4 |
| ClosureFibonacci | 56.4 | 167 | 3.0 |
| MethodFibonacci | 70.3 | 192 | 2.7 |
| NLRLoop | 168 | 443 | 2.6 |
| Richards | 154 | 282 | 1.8 |
| DeltaBlue | 138 | 230 | 1.7 |
| Splay | 235 | 290 | 1.2 |
| ClosureDefFibonacci | 33.6 | 45.6 | 1.36 |
| NLRImmediate | 796 | 894 | 1.12 |
| ParserCombinators | 15.1 | 15.4 | 1.02 |

The closest three make closures. In ClosureDefFibonacci, about 45% of the
time was making them: the defining frame's activation handle allocated
through the generic `Heap::push`, the closure through the runtime's
`closure`, and every frame with a handle returned through Rust.

**What changed.**
- **Frames with an activation handle pop in wasm.** The pop marks the
  handle dead (its frame field SmallInteger -1: a plain store, no write
  barrier), as `retire` does.
- **Activation handles allocated directly** (`Heap::allocate_live_activation`),
  not through a `Body` description: for the interpreter too.
- **Closures made in wasm.** Compiled code allocates in the arena, as it
  pushes frames: the VM publishes the arena's length and room, the next
  sequence number (the allocation counter) and the count at which a
  safepoint is due, the Closure and Activation classes, and the two meta
  words for the current actor's space. At every call into the VM, the host
  adopts the arena's length (`set_len`, as for the stack and the frames),
  and the VM the sequence numbers and the objects allocated. A
  `PUSH_CLOSURE` makes, in wasm, the frame's activation handle if it has
  none, then the closure with its copied values, when there is room and
  the sequence numbers stay below the safepoint (so no safepoint comes
  due); otherwise the runtime's `closure`, which allocates and may make the
  safepoint due, as before. Objects compiled code makes are young (past
  the nursery's boundary), so no barrier.
- **`jit_publish` reserves frames only when the room is short.**

**Correctness.** The gates of section 11 pass, the compiled kernel tests
under GC stress included (with allocation in wasm, the case that matters).

**Speed.** Runs per second, every method compiled at its first activation:

| Benchmark | Node, section 15 | Node, now | Chrome, now | psoup (Chrome) |
|---|---:|---:|---:|---:|
| SlotRead | 480 | 490 | 443 | 66.0 |
| SlotWrite | 373 | 381 | 359 | 42.2 |
| NLRLoop | 465 | 528 | 457 | 168 |
| MethodFibonacci | 183 | 180 | 193 | 70.3 |
| ClosureFibonacci | 185 | 182 | 171 | 56.4 |
| Richards | 295 | 352 | 323 | 154 |
| DeltaBlue | 234 | 259 | 239 | 138 |
| Splay | 277 to 289 | 314 | 279 | 235 |
| NLRImmediate | 925 | 1235 | 1179 | 796 |
| ClosureDefFibonacci | 47.8 | 82 to 92 | 87 | 33.6 |
| ParserCombinators | 15.6 | 17.2 to 17.8 | 16.7 | 15.1 |

In Chrome, every benchmark beats psoup: ParserCombinators by 11%, Splay by
19%, NLRImmediate by 48%, the rest by 1.6x to 8.5x. The native interpreter
is unchanged.

**What is left.** Allocation in wasm covers closures and their handles
only: `basicNew`, `new:` and `PUSH_NEW_ARRAY` could use it. Float
arithmetic boxes through the runtime. Then the top of the operand stack in
wasm locals, and recording with compilation on.

## 17. `basicNew`, `new:` and number comparisons in wasm

After section 16, the natives `call` ran most were, per Splay run, 5.9M
`basicNew`, 5.5M string `,`, 3.3M `<` and 2.5M `>` (Float keys) and 2.8M
`new:`; per ParserCombinators run, 7.1M `new:` and 1.3M `basicNew`.

**What changed.**
- **`basicNew` and Array `new:` allocate in wasm** (`IC_BASIC_NEW`,
  `IC_NEW_ARRAY`), with the arena of section 16. The entry holds the meta
  word without the space (the current actor's, published as
  `Regs::space`, is or-ed in) and, for `basicNew`, the slot count. Which
  classes `basicNew` makes Regular objects of, and with which flags (a
  value class's instances are values), is one function,
  `natives::basic_new_regular`, so the cache makes what the native would.
  `new:` makes in wasm only Arrays of SmallInteger size 0 to 2^16, within
  the room and below the safepoint, as closures do.
- **Number comparisons in wasm** (`IC_LT`, `IC_GT`, `IC_LE`, `IC_GE`) for
  `Number`'s comparison natives when the receiver is a SmallInteger or a
  Float. They run when the argument is one too: two SmallIntegers are
  compared exactly (as tagged words); otherwise both as f64s
  (`f64.convert_i64_s`, the Float's bits), as the native does, NaN
  comparing false. Anything else takes the general send.
- **The kinds a site tests, reordered.** A site tests its entry's kind one
  after another; with the comparisons, one-argument sites test eight
  binary kinds before a method's. That cost Richards 3% (an A/B of two
  builds, three runs each). Now a site tests the accessor, then the
  closure and method kinds (the most common), then the rest, with the
  binary kinds behind one range test. In the same A/B: DeltaBlue 2.5%
  faster than without the comparisons, Richards 1%, Splay 23%.

**Correctness.** The gates of section 11 pass.

**Speed.** Runs per second, every method compiled at its first activation:

| Benchmark | Node, section 16 | Node, now | Chrome, now | psoup (Chrome) | Chrome / psoup |
|---|---:|---:|---:|---:|---:|
| SlotRead | 490 | 487 | 434 | 66.0 | 6.6 |
| SlotWrite | 381 | 361 | 340 | 42.2 | 8.1 |
| NLRLoop | 528 | 564 | 450 | 168 | 2.7 |
| MethodFibonacci | 180 | 203 | 197 | 70.3 | 2.8 |
| ClosureFibonacci | 182 | 191 | 178 | 56.4 | 3.2 |
| Richards | 352 | 360 | 307 | 154 | 2.0 |
| DeltaBlue | 259 | 270 | 251 | 138 | 1.8 |
| Splay | 314 | 353 to 380 | 365 | 235 | 1.55 |
| NLRImmediate | 1235 | 1240 | 1162 | 796 | 1.46 |
| ClosureDefFibonacci | 82 to 92 | 99 | 90 | 33.6 | 2.7 |
| ParserCombinators | 17.2 to 17.8 | 18.4 to 18.8 | 17.8 | 15.1 | 1.18 |

The native interpreter is unchanged.

**What is left.** String `,` (Splay: 7M) allocates in the byte space
through the runtime. Splay spends about a fifth of its time collecting.
Then `valueWithArguments:`, the top of the operand stack in wasm locals,
and a `br_table` for a site's kinds.

## 18. Megamorphic sites: what worked and what did not

After section 17, ParserCombinators spent 69% of its time in compiled
code, and the rest mostly on sends that missed both of a site's entries:
per run, 8.3M refills, 5.2M of them outer sends one level out. Those are
megamorphic in the receiver's class: they inherit into many parser
subclasses, though their target (the enclosing object's method) is one.
DeltaBlue lost 6 to 7% in `direct_closure`: closure `value` sites seeing two
closure bodies, whose frames were pushed in Rust.

**Measuring.** Single runs mislead at the 5% level here: V8 compiles wasm
first with its baseline compiler (Liftoff) and tiers up to TurboFan on its
own schedule, which made DeltaBlue and Richards bimodal (Richards 280 or
350 for the same build). The comparisons below are A/B builds with
`node --no-liftoff`, five runs each.

**Two closure bodies per site (kept).** The cache's fill put a send of the
same class in the first entry, so two closure bodies at one site thrashed
it. Now the first entry is refilled only for the same class *and* slot
(for every kind but closures, the same class gives the same slot in an
epoch). A second body goes to the second entry, and a closure send tries
both entries' targets before the general send (which refills). `call` no
longer takes closure targets. DeltaBlue 265 to 287 (+8.5%),
ParserCombinators +3%, ClosureFibonacci unchanged.

**Constants published on entry only (kept).** The classes, the actor's
space and the meta words compiled code allocates with change only at a
collection (after which compiled code does not go on) or between turns.
`jit_publish_constants` publishes them when the host enters compiled
code, not after every runtime call.

**A second-level cache (dropped).** A VM-wide table in wasm memory, 4096
entries keyed by receiver class and site (the method's compile serial and
the site's first global), probed when both inline entries miss and
written at every fill, by two helper functions in each module (multi-value
returns). Misses fell from 8.3M to about 2K per ParserCombinators run, and
ParserCombinators gained 7 to 10%. But:
- Without refilling the inline entries from a hit, sites stuck with stale
  classes probed forever (DeltaBlue: 7.5M probes). With a refill (the hit
  into the first entry), sites cycling through three or more classes
  (Richards) churned.
- The code at every site cost DeltaBlue about 5% and Richards about 3% even
  with the probe's answer ignored; with the helpers emitted only in modules
  that used them, DeltaBlue still lost 2.6%.
- Limited to outer-send sites: ParserCombinators +4.5%, Richards +2%,
  DeltaBlue -2.6%. Not worth a second cache. Caching the target's index in
  the lookup cache entry (to save a map lookup per refill) changed nothing
  measurable either.

Both patches are kept in the session's scratch area, not the repository.
Outer sends' real fix would key their cache by the enclosing object (what
the target depends on) rather than the receiver's class.

**Correctness.** The gates of section 11 pass.

**Speed.** Runs per second, every method compiled at its first activation:

| Benchmark | Node, section 17 | Node, now | Chrome, now | psoup (Chrome) | Chrome / psoup |
|---|---:|---:|---:|---:|---:|
| SlotRead | 487 | 491 | 437 | 66.0 | 6.6 |
| SlotWrite | 361 | 355 | 331 | 42.2 | 7.8 |
| NLRLoop | 564 | 597 | 484 | 168 | 2.9 |
| MethodFibonacci | 203 | 201 | 194 | 70.3 | 2.8 |
| ClosureFibonacci | 191 | 193 | 178 | 56.4 | 3.2 |
| Richards | 360 | 360 | 320 | 154 | 2.1 |
| DeltaBlue | 270 | 305 | 287 | 138 | 2.1 |
| Splay | 353 to 380 | 395 | 390 | 235 | 1.66 |
| NLRImmediate | 1240 | 1270 | 1174 | 796 | 1.47 |
| ClosureDefFibonacci | 99 | 97 | 90 | 33.6 | 2.7 |
| ParserCombinators | 18.4 to 18.8 | 20.2 | 18.7 | 15.1 | 1.24 |

**What is left.** Outer sends keyed by their enclosing object. String `,`
in wasm. Splay's collections (about a fifth of its time; the minor
collection sorts its forwarding table). The top of the operand stack in
wasm locals, and a `br_table` for a site's kinds.

## 19. The IDE as the test case: typing in an Emmanuel document

Gilad found the IDE on Eurasia (with `?jit`) usable, except that typing in
a larger Emmanuel document (BitsOfHistoryWordsOfAdvice, 57 KB of source)
was markedly slower than on psoup, despite the benchmarks.

**The measurement.** `EmmanuelEditorProbeApp` (the editor in a page, with a
stand-in evaluator) packaged for Eurasia as CounterApp is (a scratch entry
naming its modules), and a driver over the DevTools protocol in headless
Chrome: load the document, put the caret at the start of its first
paragraph, type, and take the editor's own timings of the last keystroke
(edit, interpret, caret, render) and the wall time until its source holds
the key. Both VMs in one fresh Chrome (a long-running headless Chrome
slowed both 2.5x after many page loads):

| Per keystroke | psoup | Eurasia before | callbacks compiled | and DNU cached |
|---|---:|---:|---:|---:|
| edit | 4.0 ms | 14.4 ms | 1.4 ms | 1.3 ms |
| interpret | 26.7 ms | 99 ms | 26.0 ms | 24.8 ms |
| render | 13.2 ms | 46.8 ms | 23.1 ms | 17.4 ms |
| wall (the driver's, polling included) | 205 ms | 832 ms | 191 ms | 183 ms |

**Compiled code never ran while typing.** With `?jit` and without, the
same times: a keystroke reaches the VM as a callback from a DOM event, and
a callback ran by `step`, one instruction at a time; compiled code is
entered by returning `Completion::Compiled` to the host's trampoline,
which a callback (running to completion inside the host's call) does not
have. Now a callback with no turn under it (an event while the VM is idle)
runs as a turn does: the event loop's safepoint and interrupt checks, the
fast loop (`run_simple`), and compiled code through a new host operation,
`Host::run_compiled`, which the web host implements as its trampoline
does. A callback inside a turn still steps, so as not to run past its own
frames. The JS FFI and callback tests give the same outcomes compiled and
compiled under GC stress, and the full editor probe (31 scenarios, 1229
link edits, the raw view, the viewer, paper and slides, cut and paste)
passes on Eurasia compiled as on psoup.

**#doesNotUnderstand: was never cached.** Counting the lookup-cache misses
over the load and 20 keystrokes: 258K, nearly all not-understood sends,
of two kinds: predicates answered false by not being understood
(`isKindOfRaised` 49K, `isKindOfFailure` 18K, `isKindOfString` 11K,
`isKindOfFinalNode` 8K), and the DOM through aliens (`setAttribute:to:`
35K, `isDead` 35K, `appendChild:` 14K, `createElement:` 11K). Each walked
the class chain three times, comparing selector strings at every method
(`resolve`, `ordinary_send_uncached`, then the search for
#doesNotUnderstand:). Now an ordinary send that finds no method is cached
too: the entry holds the #doesNotUnderstand: method the receiver's class
answers, and a hit sends it the message directly. Every program change
flushes the cache, as for found methods. Compiled code's caches and the
fast loop's probe treat such an entry as a miss and leave it to `send`.

**What is left here.** Render is still about 30% slower than psoup's: the
DOM, through aliens, each a #doesNotUnderstand: that allocates a message
and goes through the alien's handler to a host operation. A cache kind for
alien sends (straight to the host operation) is the next thing to try,
then sends inside a turn's callbacks (still stepped). The benchmarks are
unchanged: ParserCombinators 20.8 and DeltaBlue 313 runs per second
under Node.

## 20. Alien sends cached; compiled methods named in profiles

**Alien sends.** A message a host object (an Alien) does not understand
goes to the host: `Alien>>doesNotUnderstand:` (the kernel's) answers
false for `isKindOf…`, handles `isDead` and `new` itself, and otherwise
sends `perform: name withArguments: arguments`, the name being the
selector's first keyword, cut from it with `indexOf:` and `copyFrom:to:`
(a new String each time). With section 19 the not-understood send was
cached, but every call still allocated a message, ran that method and
made the name. Now, when the receiver's class is the Alien class, the
lookup cache's not-understood entry records what the method would do
(`AlienSend`): answer false, or call `perform:withArguments:` (its
method, native and failure included, as the target) with the name made
once when the entry is filled. A hit builds the arguments Array and
activates `perform:withArguments:` directly. `isDead` and `new` still run
the method. The difference from running the method: no
`doesNotUnderstand:` frame in a backtrace.

Typing in BitsOfHistoryWordsOfAdvice (section 19's measurement): render
17.2 to 16.4 ms, interpret unchanged. Rendering's remaining cost is not
the alien protocol. Benchmarks (which send no aliens): ParserCombinators
16.6 to 17.6 under `--no-liftoff` (five runs each; the send path's code
changed), DeltaBlue within the noise (264 to 286 in both builds).

**Compiled methods named, on request.** With names on
(`Vm::set_jit_names`: `EURASIA_JIT_NAMES=1` under Node, `?names` on
`index.html` and `ide.html`), each compiled module gets a `name` section
naming its function `Mixin>>selector`, so a CPU profile shows compiled
methods by name rather than one `wasm-function[8]`. It is off by default:
in an A/B (`--no-liftoff`, five runs) DeltaBlue may have been a few
percent slower with names, within the noise but not worth risking for a
diagnostic. Typing, by method:
`List>>add:` 6.4%, `_Array>>do:` 4.2%, `Emmanuel>>fastTokens:from:to:` 3.4%,
`Host>>parse:` 3.3%, `ByteArray class>>withAll:` 2.6%,
`StringBuilder>>add:` 2.1%, `Emmanuel>>encodeCodePoint:on:` 1.8%,
`True>>and:` 1.4%; the VM's own functions are a few percent each. Typing
is now mostly ordinary Newspeak (collections, string building) in
compiled code: the code compiled code is made of, not the runtime, is
what is left (the top of the operand stack in wasm locals; inlining).

**Tried and dropped: a laxer write barrier inline.** `at:put:`, setters
and indirect stores run inline only into a young or remembered object.
Storing a SmallInteger or an old reference into an old object needs no
barrier either, so the check can allow it. Correct (the kernel tests pass
under GC stress) but no measurable gain on typing (the lists are young),
for more code at every store: not kept.

**Correctness.** The gates of section 11 pass; the JS FFI and callback
tests give the same outcomes interpreted, compiled, and compiled under GC
stress.

