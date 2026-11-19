# Eurasia M7: snapshots, restore and replay

**Date:** 2026-11-18
**Status:** Implemented 2026-11-18; the questions of section 5 were decided as recommended. Section 6 says what was built and how it differs from the proposal.
**Context:** `NEW_VM_IMPLEMENTATION_PLAN_2026-11-17.md` (M7),
`VM_KERNEL_CONTRACT_DESIGN_2026-11-09.md` sections 5 and 6 (decided
there), `VM_KERNEL_OPERATIONS_2026-11-10.md` section 9,
`eurasia/docs/SNAPSHOT_FORMAT.md`.

## 1. What M7 must deliver

The plan: "Snapshots, restore, replay log, checkpoints, divergence
detection". Done when we can save and restore with paused stacks, and a
recorded IDE session replays to the same outputs.

Already decided (contract design, 2026-11-09 and 2026-11-10):
- **Snapshots include paused actor stacks.**
- **Checkpoints may be taken mid-turn,** and their frequency is a parameter
  that can change while running.
- **Replay is a checkpoint plus the input log.**
- **Outputs are recorded too,** and a replayed output that differs signals
  divergence. Whether to record a digest instead is not decided.
- **Restoring into a new host invalidates aliens.** Lazy slots holding
  aliens are reset on save, and the program rebuilds host state on a
  restore notification.

## 2. Where Eurasia stands

- **What a snapshot saves.** `vm snapshot` writes what the roles reach, as
  collected into a copy, with no frames. Only the actor whose message loop
  is the role is saved; other actors, mailboxes, timers and expats are not.
  Activations, detached ones included, are saved dead.
- **Most of execution is already deterministic.**
  - Scheduling is round robin.
  - Collections happen after a number of allocations, not on memory
    pressure, so weak clearing happens at the same points on replay,
    provided the allocation counter is saved too.
  - Identity hashes and the order of `allInstancesOf:` are allocation
    order.
- **Every nondeterministic input crosses the `Host` trait:**
  - clocks and random bytes;
  - host-object operations (whose results are inputs, whose requests are
    outputs);
  - callbacks with their arguments, during a host call or while idle;
  - timers firing;
  - `print:` (an output).

## 3. Proposal

### 3.1 The log: at the host boundary

A recording host wraps the real one. It appends each input to the log in
the order the VM consumes it:
- a clock reading;
- random bytes;
- a host operation's result, with the callbacks it made during the call
  nested inside it;
- an idle callback with its arguments;
- the point at which a timer was allowed to fire.

It also appends each output: a `print:`, and a host operation's request.

A **replaying host** answers inputs from the log and never calls the real
host. It compares each output with the recorded one, and the first
mismatch is reported as **divergence**: its log position, and what was
expected and what was produced.

Because replay never needs the host, **a session recorded in a browser
replays on the command line** (`eurasia replay <checkpoint> <log>`). That
is how the done-criterion is checked: record an IDE session in the
browser, then replay it natively and compare.

### 3.2 Snapshots: the whole cohort, stacks included

**Snapshot format 6** adds:
- **Per actor:** its message loop, mailbox, wakeup and expats (the expat
  table becomes per-actor data in the image).
- **Frames:** each running or paused frame's method, receiver, closure, ip
  and base, with the operand stack as values.
- **Detached activations** saved with their state: sender, bci and temps.
- **The VM state replay needs:** the allocation counter, the collection
  budget, the program version, the current actor, the next frame serial,
  and the log position.

### 3.3 Checkpoints

`vm checkpointNow` and `vm checkpointPolicy: p` take a snapshot into the
log's storage, mid-turn if need be. The policy is an allocation or turn
count to begin with. Replay starts from any checkpoint, at its log
position.

### 3.4 Restore into a new host

As decided in the contract design:
- the alien table starts empty, so every saved Alien is dead and using one
  fails with `#dead`;
- the writer resets lazy slots (cache slots `x`cache`slot`) whose value is
  an Alien;
- after restore, the restore role is sent a notification, which for the
  IDE re-renders Hopscotch.

A checkpoint replayed in the same session does not touch aliens, since the
log answers for the host.

### 3.5 Where the log lives

In the browser it is kept in memory. The page can save it and the latest
checkpoint as files, from a debug control or from the console. On the
command line it is written to a file. Persisting it continuously
(IndexedDB) is not proposed for M7.

## 4. Order of work

1. **Format 6.** Whole-cohort snapshots with frames and detached
   activations, and the VM state above. Check: save mid-turn, restore,
   continue, compare with an uninterrupted run.
2. **The log, with recording and replaying hosts.** Check: record the
   kernel tests natively and replay them with identical outputs, plus a
   negative control (a tampered input diverges).
3. **Checkpoints and their policy.**
4. **Restore into a new host:** dead aliens, reset lazy alien slots, the
   restore role.
5. **The browser.** Record an IDE session, save it, replay it natively with
   the same outputs.

## 5. Questions

1. **The log sits at the `Host` boundary,** with host operations' requests
   as outputs. **Recommended.** It covers every nondeterministic input
   Eurasia has, and replay needs no host.
2. **Full outputs, not digests,** for now. They are simplest to diagnose,
   and digests can come later if logs grow too large.
3. **Format 6 saves the Rust frames as frames,** rather than converting
   them to detached activations on save. Restore then needs no
   materialization, and a mid-turn checkpoint restores exactly.
4. **Command-line replay of browser sessions** as M7's check.
5. **The log in memory, saved on request,** in the browser for M7.

## 6. Progress (2026-11-18)

All five steps are done, and the done-criterion is met: an IDE session
recorded in a browser (395 top-level events, about 105,000 log events:
start, timer resumes, clicks, typing a search) replays on the command line
with every output identical, from its start and from a checkpoint taken in
the browser in the middle of the session.

What was built (eurasia):
- **Format 6** (`docs/SNAPSHOT_FORMAT.md`): a machine section (the operand
  stack, frames, every actor with its mailbox and timer, expats, the VM's
  selector strings, the counters), activation handles saved live or
  detached with their state, and role 40. `Vm::checkpoint_image`,
  `Vm::restore`, `Vm::continue_run`; `read_checkpoint`.
- **The log** (`crates/eurasia-core/src/replay.rs`): `Recorder`, `Replayer`,
  `replay`, the encoding (`EURL`, version 1). The log also records how each
  top-level event ended, idle callbacks' results, and each checkpoint's
  digest, so a replay that writes different checkpoint bytes diverges.
  Checkpoints travel in the log; the first is the image the run started
  from, so a log is self-contained.
- **Checkpoints**: `vm checkpointNow`, `vm checkpointPolicy:`, `vm
  logPosition` (natives 174–176).
- **Restore into a new host**: `Vm::restored_into_new_host`.
- **The command line**: `eurasia --record LOG [--checkpoint-every N]
  SNAPSHOT`, `eurasia --replay LOG [CHECKPOINT]`, `eurasia --checkpoint LOG
  K FILE`; a checkpoint given as the snapshot is restored into the new host.
- **The browser**: `ide.html?record=N` records; `eurasiaSaveLog()` or
  Ctrl-Shift-L downloads the log, `eurasiaUploadLog()` sends it to
  `scripts/serve-web.sh`'s server (into `target/web/uploads`). Under Node,
  `EURASIA_RECORD=path` (`web/run-node.mjs`).
- **Checks**: `scripts/replay-tests.sh` covers:
  - the kernel tests, recorded natively, replayed from the start and from a
    checkpoint in the middle of a turn;
  - a tampered log that diverges at the altered line (the negative control);
  - the debugger probe (detached activations) replayed from each of its 43
    checkpoints, each of which, restored on its own, prints the rest of the
    output;
  - the kernel tests and the JS tests (callbacks, an idle callback),
    recorded on wasm and replayed natively;
  - `EurasiaRestoreProbe` (newspeak), restored into a new host.

How it differs from the proposal:
- **`vm snapshot` stays the snapshot that starts afresh.** Paused stacks are
  in checkpoints, which the VM hands to the host (`Host::checkpoint`) rather
  than answering as a ByteArray. A checkpoint taken mid-turn continues right
  after the safepoint it was taken at.
- **Checkpoints are taken only with no host call under way.** The event
  loop's safepoints have none, and a checkpoint due during an idle
  callback is taken at the next resume. A callback's Rust frames
  (host operation, nested run) are not saved, so a checkpoint cannot be
  taken inside one.
- **The checkpoint heap keeps what the roots reach weakly.** A copy
  collected normally would clear weak references the running VM still
  holds, and the restored run would diverge. Unreachable objects are
  dropped, which changes only how many objects the next collection finds
  (nothing observes that).
- **Lazy slots holding Aliens are reset on restore into a new host, not on
  save**, so one checkpoint serves both replay and restore. Aliens other
  than the host's undefined and global objects get the reference -1, and an
  operation on one fails with `#dead`.

Done since (2026-11-18, later):
- **The IDE restores into a new page.** `actors whenRestored: aBlock` sets
  the restore handler (role 40; nothing on psoup and JS). The IDE's
  handler makes Hopscotch forget its windows and every presenter
  (`forgetWindows`: `uiGeneration` advances, so subjects build new
  presenters rather than reconciling with dead visuals) and reopens the IDE
  window on the subject it showed. The IDE's modules keep host objects
  (the document, JS constructors, localStorage) in lazy slots, so that they
  are looked up again (contract design, section 6, rule 1). Checked by
  hand: a session recorded in a browser, its checkpoint opened in a new
  page, comes back on the same page and keeps working.
- **Incarnation ids and lineage.** Every start mints a 16-byte id from host
  entropy (recorded, so a replay reproduces it); the id the image was saved
  with becomes the lineage. Roles 41 and 42, snapshot format 7, `vm
  incarnation` and `vm lineage` (natives 177, 178). Genesis saves no
  incarnation, so base images stay reproducible.
- **Logs stay bounded.** A log keeps its last K checkpoints and the events
  after the oldest (`--keep-checkpoints K`; in the browser `keep=k`,
  default 2). Positions and checkpoint numbers stay absolute. Log format 2
  (format 1 still reads).
- **Saving a running image.** `actors saveImage: name` (native 179) asks
  for a checkpoint at the next safepoint, which the VM hands to the host
  (`Host::save_image`) even when nothing is recorded; the restore handler
  is then sent `imageSaved`. The promise it answers is fulfilled with
  `#saved` there, and with `#restored` in an image restored from it (the
  pending save is in the image; the notice is queued after the image is
  taken). The program learns only that the image was handed over, so the
  outcome is not an input and logs are unchanged; a recorder passes the
  image on, a replay saves nothing. The command line writes the file
  `name`; the web page keeps it in the origin private file system and
  offers saved images, or a fresh IDE, when it loads. `actors
  savesImages` is false on psoup and JS, where `saveImage:` answers a
  broken promise. The IDE's Home page menu has Save Image.
  EurasiaSaveImageProbe checks both outcomes (replay-tests.sh, step 5).

Not done:
- **Recording a run restored from a checkpoint** is refused. Its replay
  would need the restore's effects on aliens as part of the log.
- **Succession** (contract design, section 6, items 3 and 4) is not
  designed beyond the contract design's sketch.
