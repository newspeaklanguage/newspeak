# Eurasia: a baseline compiler, design

**Date:** 2026-11-19
**Status:** Approved (Gilad, 2026-11-19: Rust compiler, native interpreted
for now). Stage 1, the spike, done (section 9), uncommitted.
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
