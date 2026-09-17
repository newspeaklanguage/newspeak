# Session summary 2026-09-16..17: bridge budget, chat re-entry, context menus, keystrokes, hidden pages

One long chat session in the Croquet Web IDE (bus agent). Read this first when
resuming Croquet work. The previous record is
`SESSION_SUMMARY_2026-09-06_to_13_HOST_ON_CROQUET.md`.

## State at the end of the session

**Committed and mirrored** (newspeak `master`, merged into `webide-ai-access`):

| Commit | What |
|---|---|
| `e38cdc0` | Chat-page re-entry keeps its input editor; `upload_file` is coordinated |
| `3ab6e8f` | AI bus: the bridge's reply budget bounds silence, not the whole turn |
| `1735a51` | Front door: `/_ns/config` reports whether the running process is stale |
| `44dfdc8` | Probes: `NAV=home|history` re-enters the chat page |
| `e71efaf` | Context menus are synchronized; their Menu subscription is retired |
| `6393704` | A keydown is published only for the keys the editor acts on |
| `176c543` | An editor's before-change response rides its change event |

**On disk, UNCOMMITTED, in Gilad's rebuild of 2026-09-17** (he is testing in a
fresh session; commit only on his explicit word; planned as four newspeak
commits, one per concern, plus one in primordialsoup):

| File | Concern |
|---|---|
| `HopscotchForCroquet.ns` | Keystroke item 3: coalesced change publishing (was changeset cs4) |
| `Browsing.ns` | Method editor collapsing on accept (cs5) |
| `HopscotchForHTML5.ns` | Deferred content on an unpainted page (cs6 + promise-turn refinement) |
| `croquet-probes/setup-latejoin-probe.js`, `croquet-probes/syntax-check.js` (new) | `HIDDEN_B=1` probe mode; glue syntax checker |
| primordialsoup `meta/croquet-post.js` | Replay pacing no longer depends on animation frames |

Scratch helpers (untracked, regenerate at will): `scratch/splice_test_glue.py`
(rebuilds `out/croquetpsoup-test.js` from the meta file, TEST artifact only),
`scratch/make_cs_coalesce.py` / `make_cs_deferred.py` (generate a
`propose_changes` payload from canonical file text).

## What was found, and why

### 1. The bridge killed long turns (fixed, `3ab6e8f`)
`tool/bus-claude.py` had a fixed 540s cap on a whole reply and a 300s idle
limit that only saw completed messages, and gave the next turn no hint that the
last one died, so the chat looped on dead work. Now: the deadline restarts on
every stream line under a 30-minute cap, partial messages stream, the bridge
posts a heartbeat every 60s during a tool call, a hang is 660s of silence, and
the turn after a kill opens with a notice. Working practice that held all
session: long probes run as a harness background task and are polled with
`TaskOutput` inside the same turn (ending the turn kills them; `nohup`/`setsid`
are refused by the permission gate).

### 2. Re-entered chat page typed into a retired editor (fixed, `e38cdc0`)
The amplet cache lives on the presenter, so re-entry builds a fresh page whose
new input editor attaches under a new address and then same-kind ADOPTS the old
editor's identity. The old one was retired on leaving, so adoption skipped
re-subscribing. Adoption now drops the new fragment's pre-adoption
subscription, removes the old fragment's handlers, and always subscribes under
the adopted address. Same commit: the Croquet `FileChooserFragment` overrides
`chooseFileList:ifCanceled:` (a cancel is a click with an empty descriptor
list), and `coordinatedShare` logs when a recording supersedes a local failure.

### 3. Context menus were never synchronized (fixed, `e71efaf`)
HopscotchForCroquet had a module-level `openMenu:` since 2024. It never ran:
`Presenter>>openMenu:` is found by INHERITANCE before the lexical scope is
consulted. **Lesson: a module-level override cannot intercept a method that a
nested class inherits; the base must route through a module-level seam.** Base
now has `openMenu:forShell:inVisual:`; Croquet overrides it; the Croquet shell
holds the current context Menu and retires the previous one at the next open.

### 4. Keystroke traffic: three events per keystroke down to a bounded rate
- Item 1 (`6393704`): keydown published only for modified Enter and Escape.
- Item 2 (`176c543`): user before-change publishes nothing; the change handler
  sends the base before-change response first. Hot-load caveat: open editors
  keep old handler closures until re-armed.
- Item 3 (uncommitted): a throttle, not a debounce. The first unpublished user
  change starts an 80ms timer (`changeCoalescingWindow`, a method, tune by
  hot-load); the flush publishes the full text, the LAST change record, the
  sender's view id and an ordinal.
  **Key insight: every client, the typist included, applies an echo with
  `setValue`, so naive coalescing LOSES characters** (the echo wipes unflushed
  text and the next flush publishes the wiped buffer). So on its OWN echo while
  ahead (an edit pending, or a later ordinal in flight) the typist applies the
  echo and runs the response in lockstep, then restores its text and cursor in
  the same turn - only when a further own publish is certain, which guarantees
  convergence. An editor already holding the echoed text is left alone (this
  removes the single-typist cursor jump). Accept and the shortcuts flush first;
  cancel DISCARDS; same-kind adoption hands over pending state.
  Known limit: no blur hook, so a button that reads the editor within 80ms of
  a keystroke sees older text on other clients (a probe could; a person cannot).
  `codeMirrorData:` is now unused.

### 5. Method editor collapsed on accept, intermittently (fixed, uncommitted)
Not Croquet and not the accept paths. Keyed list reconciliation (2026-08)
matches by `#key`; `Presenter>>key` is the subject; a method subject's model
compares method mirrors, which compare COMPILED METHODS BY IDENTITY. Accept
installs a new compiled method, so the accepted method's presenter matched
nothing and was built fresh; its toggle then starts from `mustBeExpanded`,
which a header-click expand does not set but navigation does - hence the
apparent randomness. Fix: `MethodPresenter>>key` answers its `tag` (the method
name), as tagged lists always matched. Lazy slots are unaffected.
Noted, untouched: `Browsing` ~5535, `MiscBrowsing` ~833, `Inspecting` ~716 have
a SLOT named `key` on presenters, shadowing the reconciliation key.

### 6. A window that is not painted diverged (fixed, uncommitted, probe-verified)
Gilad opened all senders of `#key` while a second client's window was on
another macOS space. Base Hopscotch drains deferred content one action per
three animation frames; **an unpainted page gets no animation frames**, so
nothing was built there and the alarm correctly reported every event for the
unbuilt fragments as never delivered (kind `delivery`). A real divergence.
- `HopscotchForHTML5>>nextFrameDo:ifNoFrame:` races frames against a timer
  (`noFrameTimeout`, 1000ms); a hidden page goes straight to the fallback, in a
  PROMISE TURN - hidden pages throttle timers to 1/s, then 1/min after 5 min;
  the fallback drains the WHOLE queue (nothing to pace for).
- Glue `nsReplayPace`: a hidden page takes one MessageChannel macrotask
  (unthrottled); a painted page races its frame against 250ms.
- The DeploymentManager mirror has NO replay pacing at all (drift since
  2026-09-13); nothing to fix there, but port it during the JS testing item.

Verification (`croquet-probes/run.sh NS_SUFFIX=-TEST
NS_PAGE=croquetpsoup-test.html PROVIDER=openai-compat FROM_CLASS=0 ...`):

| Run | Result |
|---|---|
| fixed TEST build, `NAV=home`, painted joiner | 15/15 |
| fixed TEST build, `HIDDEN_B=1` | 12/12, 0 divergence, 0 orphans |
| CONTROL: unfixed live build, `HIDDEN_B=1 JOIN_MS=60000` | 4 fail, joiner stuck at event 1 of 45 |

Event counts for the same script: 66 before the keystroke work, 50 after.

## Corrections to older notes (do not relist these as open)
- The dropdown Menu subscription leak was fixed 2026-09-03 (`1661600`).
- The silent adopted-recording fallback is built (`e38cdc0`).
- "Media tool results local" is closed for the current tool set: only the text
  of a tool result is shared, but `upload_file` is the only media-producing
  tool and its bytes are coordinated upstream by the file chooser. A future
  media tool must coordinate its own media.
- `syncTime` is genuinely NOT built (design only). `syncRandom` and the
  model-driven `TimerFragment` are.

## Remaining Croquet agenda (per Gilad, 2026-09-16)
1. **Croquet on JS (NS2JS).** The whole host-on-Croquet arc and everything
   above has only run on psoup. The glue mirror embedded in
   `DeploymentManager.ns` is hand-maintained and has drifted (no replay
   pacing). Path: `croquet-probes/deploy-driver2.js` regenerates
   `CroquetJSIDE-TEST.*`; then determinism-test, typing-test, menu-probe, and
   a JS-page mode for setup-latejoin-probe.
2. **Keystroke performance** - items 1-3 done; tune the window by feel; diffs
   only if payload size on large documents proves the bottleneck (they need
   OT-style care under concurrent typing, which full-text replacement masks).

Parked, no trigger known: `ChatStatusPresenter` state-dependent id minting;
the unexplained session-id change on reconnect.
