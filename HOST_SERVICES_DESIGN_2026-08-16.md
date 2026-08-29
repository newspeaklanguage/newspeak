# Host services: one front door, one Newspeak capability, one async idiom

**Status:** design, nothing implemented. Written 2026-08-16.
**Companion artifact:** `AsyncBridgeProbe.ns` + `AsyncBridgeProbeApp.ns`.
**Updated 2026-08-25:** probe RUN on BOTH runtimes — results in §6.1, and they
are decisive: the gate passes. It also exposed a latent bug in `ActorsForJS`
(§6.1.1), since fixed on master as `4713887`, and localized the psoup VM abort to
the alien bridge. Croquet discovery shape corrected in §3 from the Croquet
owner's reply.

Three decisions are entangled here, and writing them separately guarantees they
disagree: how local services are *served*, how Newspeak *reaches* them, and what
async values *look like* once they arrive. This covers all three.

Everything below has to work on **both runtimes** — primordialsoup (WASM) and the
NS→JS deploy. That constraint is not a footnote; it decides several of the
choices, and it is called out at each point where it bites.

---

## 1. Where we are

Three servers are running right now, and they differ in kind:

| Port | What | Whose code | Protocol |
|---|---|---|---|
| 8080 | static `out/` | Python stdlib | HTTP |
| 9999 | CORS proxy for git (`tool/cors-proxy.py`) | ours, Python stdlib | HTTP |
| 9090 | Croquet reflector | third-party, Node | WebSocket |

All three bind `0.0.0.0` — every interface, no authentication. Two more are
already scoped: a diagnostics fetch endpoint (so the AI's `local_fetch` can see
status, headers and body instead of an opaque failure) and a message bus for
talking to Claude Code sessions.

The pattern is clear enough to design for: **we keep meeting capabilities the
browser sandbox denies us, and each one has arrived as its own port with its own
configuration surface.** The git proxy URL is a per-repository field defaulting
to `localhost:9999`; the reflector URL lives in the bootstrap page; the static
root is wherever Python was launched. Each is a place where dev and deploy drift
apart.

## 2. Principle: consolidate the origin, not the process

One process is the wrong goal. The reflector is third-party Node code speaking
WebSocket, deliberately swappable (self-hosted now, Multisynq's network if it
returns). Absorbing it couples us to a dependency we want at arm's length, and
one process means one crash takes out git, fetch, chat and sync together.

One **origin** is the goal. If everything the browser talks to lives at one
`host:port` under reserved paths, then: CORS is structurally gone rather than
proxied around; there is one thing to start; there is one auth boundary; and —
the real payoff — **the IDE stops hardcoding ports**, because every service is a
relative path.

```
/                       static (out/)
/_ns/git/<host>/<path>  the existing @isomorphic-git/cors-proxy convention
/_ns/fetch?url=…        diagnostics fetch: status, headers, redirects, body
/_ns/bus                SSE + POST — the agent channel
/_ns/config             discovery: what this origin actually offers
```

`_` is illegal in hostnames, so `/_ns/…` can never collide with a proxied host;
the existing convention keeps working untouched.

**The reflector stays its own process**, discovered through `/_ns/config` rather
than absorbed. Reverse-proxying a WebSocket upgrade through Python's stdlib
`HTTPServer` means hijacking the socket and pumping bytes both ways, and it puts
our process in the latency path of the one latency-sensitive thing we have.
Revisit only if a single port through a firewall becomes a requirement.

## 3. The discovery contract

`GET /_ns/config` is the keystone. It is what makes everything else incremental,
and it is the one piece both the server and the Newspeak side must agree on
exactly.

```json
{
  "version": 1,
  "git": true,
  "fetch": true,
  "bus": false,
  "croquet": {"reflector": "ws://localhost:9090", "files": "/files"}
}
```

**The `croquet` shape is confirmed by the Croquet owner** (newspeak-35), and it
corrects two assumptions in the first draft of this document:

- **The file server is not on 9090 — it is `server3.py` on :8080, i.e. the static
  front door already IS the Croquet file server.** It serves PUT/GET under
  `out/files/`. This strengthens the consolidation story rather than complicating
  it: `files` is a reserved path on the front door, not a separate service to
  discover. `out/files/` also holds session blob state (managed by
  `tool/clean-croquet-sessions.sh`) and `out/files/deploy` is deploy staging, so
  the path is load-bearing on disk.
- **`files` is effectively mandatory, not an optional extra.** Passing
  `reflector=` sets `signServer:"none"`, which kills default file-server
  resolution; `files=` is consulted first and restores file handling keylessly.
  Beyond drag-and-drop, the large-payload detour stores every oversized editor
  keystroke there — no `files=`, no usable editors.

Param names are the Croquet client library's own, so discovery → URL
construction is a rename-free pass-through. `reflector` stays **absolute**
(different scheme and port; it cannot be relative); `files` is deliberately
**origin-relative**, so it survives localhost → https and host renames with no
edit. An absent `croquet` key means "no local Croquet here — use whatever the
page was given".

Two things not to do. **Do not publish `box=`**, even though it replaces both
keys: `box` implies the reflector WebSocket lives behind that same origin, which
is exactly the WS reverse-proxying this design avoids. And **do not put
`apiKey`/`sessionId`/`pwd`/`appId` in discovery** — they are session/app-level,
not host-level. (`apiKey` must nonetheless be *present* on the page URL as
`apiKey=none` or `Session.join` throws; its value is ignored once `reflector=` is
given.)

Two facts worth recording because they constrain later work: the reflector's port
9090 is **hardcoded** in `reflector.js` with no CLI or env override, so hiding it
behind discovery is right but the server side cannot move without patching; and
when the front door goes https, **wss is not optional** — browsers block `ws://`
from an https page as mixed content.

Rules:

- **Absent means unavailable.** A missing key, a 404 on `/_ns/config`, a
  connection refused, and a malformed body are all the same answer: that
  capability is not here. Fail closed.
- **A deployed origin answers 404 and that is correct.** newspeaklanguage.org
  serves `/` and nothing under `/_ns/`, so the deployed IDE lights up exactly the
  features that work there. Same code, same relative paths, no localhost in the
  image, no per-deployment configuration.
- **Values, not just booleans, where a value is needed.** `reflector` is a URL
  because it names a different origin.
- `version` exists so the Newspeak side can refuse a contract it does not
  understand rather than guessing.

## 4. Server shape

Keep `tool/cors-proxy.py` as the front door — it is the only server we own, it
is stdlib-only (no `pip install`, which is a real virtue for a project whose
pitch is "open the page"), and it already proxies generically.

Three changes, in order:

1. **`ThreadingHTTPServer`.** One line, stdlib. It is a *prerequisite*, not an
   optimization: the server is single-threaded today, so one SSE stream on
   `/_ns/bus` would block every git clone.
2. **Bind loopback, require a token.** Today `*:9999` will forward an
   `Authorization` header for anyone on the network. That is tolerable for a dev
   git proxy. `/_ns/bus` is a different animal — it injects prompts into an IDE
   that edits and runs code, which is remote control. Auth must land *before* the
   inbox exists; retrofitting it onto a channel other things already use is how
   this goes wrong.
3. **Serve `/` from `out/`**, so static content and services share an origin and
   8080 can retire.

`/_ns/fetch` returns an envelope rather than a bare body, because the whole
reason it exists is that the provider's server-run `web_fetch` collapses every
failure into one opaque string:

```json
{"status": 403, "statusText": "Forbidden",
 "headers": {"server": "cloudflare", "cf-ray": "…"},
 "redirects": ["https://…"], "elapsedMs": 412,
 "body": "…first N KB…", "truncated": true}
```

An error *page* is frequently the whole answer — a Cloudflare 1014 names the
misconfiguration outright — so the body is returned on failure, not discarded.

## 5. Newspeak shape: `platform hostServices`

A module, exposed on the platform beside `js`, `kernel`, `hopscotch`,
`aiAccess`.

**Why it earns platform status** is capability attenuation, not tidiness.
Everything it does ultimately goes through `platform js`; today any code that
needs to fetch a URL is handed *all of JavaScript*. This lets us hand an
application a fetcher without handing it `js global`. The second argument is
deployment: platform variants are the established way to express "this
environment doesn't have that", so a platform built without the slot makes
dependent features structurally unavailable rather than failing at first call.

**Name.** Not `localServices`: the same object talks to a same-origin service in
a deployment, where "local" is a lie — and dev/deploy parity is the point. Not
`webGateway`: too narrow, since the bus is not web egress and reflector discovery
is not either. `hostServices` names the provider, covers both environments, and
promises no particular protocol.

**Not a façade — a namespace of separately-obtainable capabilities.** Clients
take only what they need, in the ordinary import-slot idiom:

```
private Fetcher = platform hostServices fetcher.   (* nil when unavailable *)
```

Attenuation then means something: the repository module never touches the bus,
the AI module never touches the git proxy.

**Membership rule** (to go in the class comment, or drift is certain): *a member
is something the browser sandbox forbids, provided by the host at the shared
origin, and independently absent.* An application-specific endpoint fails that
test — it belongs in an app module that *uses* `fetcher`.

**Availability protocol.** Discovery is asynchronous but callers mostly want a
synchronous "can I render this button?". Probe once during platform
construction, cache, and expose synchronous accessors afterwards, with
`whenReady:` for code that must wait. Two constraints on the implementation:
hold it in a **lazy** slot, so nothing is fetched at snapshot time and a hot-load
does not crash on a nil eager slot; and **fail closed**, so "no answer yet" and
"no server" both render as unavailable rather than as an error.

**Dual-runtime:** `hostServices` must not be psoup-specific. It should be written
against `platform js` and `platform actors` only, so the same module definition
serves both runtimes — and if a runtime-specific variant ever becomes necessary,
it follows the existing rule that the psoup API is canonical and the JS platform
library is what gets fixed.

## 6. Async idiom: confine JS promises

JS promises have spread through the system, and they are load-bearing in a way
that costs us. The known hazards are all bridge behaviour, not style:

- a raise unwinding out of a `then:` closure **loses the rejection** — the
  closure's `rawPush:` never runs and the next callback fires with garbage on the
  alien stack (documented in `AIAccess>>completeWithToolLoop`);
- `new Promise(executor)` silently passes nil for both arguments, so
  `Promise.withResolvers` is mandatory;
- callbacks must return marshalable values;
- psoup delivers the **last** JS argument to every callback parameter, while the
  JS runtime delivers the true order.

Every async method in the system carries defensive tics for these, and each has
to be re-learned by every reader.

**Two reframings make this tractable:**

1. **It is a boundary question, not a replacement question.** Every async value
   originates JS-side — `fetch`, `setTimeout`, `FileReader`, `EventSource`,
   isomorphic-git. Something must convert. The achievable goal is *confine JS
   promises to a thin adapter and use Newspeak promises above it*; "eliminate
   them" is not a thing.
2. **Promises are not actors.** Adopting Newspeak promises as the async value
   type (`whenFulfilled:whenBroken:`, pipelining) is local: one heap, Hopscotch's
   synchronous object graph untouched. Adopting the *actor* model — separate
   heaps, eventual-only sends, far references — collides head-on with Hopscotch,
   where a chat session in its own actor would hold far references to presenters
   and every subject read would become an eventual send. Phase 1 is the first.
   The second may never be worth it.

`hostServices` is the right pilot: it is the boundary object by definition, it is
greenfield with no legacy call sites, and if the idiom fails there the blast
radius is one module nobody depends on yet.

**What would be gained,** concretely: exceptions that behave under ordinary
`on:Exception do:` instead of the "never raise in a `then:`" rule; async failures
that land in the debugger as Newspeak stacks rather than alien frames and
"Exception in turn without resolver"; and one idiom instead of a set of
workarounds.

### The gate: run the probe first

`AsyncBridgeProbe.ns` answers the make-or-break questions before any design work
is committed. **Run it on both runtimes and compare** — psoup uses `Actors.ns`,
the JS deploy uses `ActorsForJS.ns`, and they are separate implementations of the
same protocol, so a result from one says nothing about the other.

```
psoup / IDE:  (AsyncBridgeProbe usingPlatform: platform) runAllToConsole
JS deploy:    the same expression from the deployed page's entry point
```

| Probe | Question | If it fails |
|---|---|---|
| 1 js-promise-control | Does the JS side work at all? | Nothing else is interpretable |
| **2 ns-fulfill-from-js-callback** | **Can a Newspeak promise be fulfilled from inside a JS callback?** | **The whole plan is dead** — this is the only way a value crosses |
| 3 ns-break-from-js-callback | Does the error path cross? | Adapter must model errors as values |
| 4 ns-raise-in-whenFulfilled | Does a raise break the *derived* promise? | The ergonomic win evaporates; JS promises are no worse |
| 5 ns-turn-semantics | Does `whenFulfilled:` on a resolved promise still defer a turn? | Re-entrancy bugs of the runaway-render class |
| 6 ns-timer | Can deadlines be Newspeak-native? | Adapter keeps owning timers (not fatal) |
| 7 eventual-send-to-promise | Does pipelining work? | Lose a nice-to-have, not the plan |
| 8 callback-argument-order | Confirms the psoup/JS divergence | Adapter must be written correct under both |
| 9 js-raise-in-then | Confirms the known hazard, and whether the runtimes differ | Runs last: it may corrupt the bridge for anything after it |

The harness reports `HANG` rather than hanging, and `DOUBLE` if a probe settles
twice — a duplicated settlement is as much a finding as a lost one.

### 6.1 Results — both runtimes, run 2026-08-25

psoup: `AsyncBridgeProbeApp` compiled to a vfuel with `WebCompiler`, loaded as
`primordialsoup.html?snapshot=…` in headless Chrome, console over CDP. NS→JS:
packaged through `JSPackager` with `ide deployment Runtime` and loaded as a
deployed page, run by newspeak-a4.

**Provenance — and this is the part to get right, because both columns are
weaker than they look.** *Neither runtime's results are pinned by a git SHA.* On
both sides what ran was an **artefact**, and the artefact is not the tree:

- **psoup**: a vfuel built from the `out/` **working copy** of sources on
  2026-08-25, not from a clean checkout.
- **NS→JS**: a page packaged by `JSPackager` running *inside a deployed JS IDE*,
  which packages the sources embedded in **that image** — built 2026-08-18 04:03
  — not the sources in the git tree. `ActorsForJS` was the one exception: it was
  injected deliberately (master's, plus the one-character fix) before packaging.

That distinction is not academic. Reasoning from git ancestry says the JS results
include `caa8255`, `bb3978a`, `fc24975` and `7fe3e17`, since all four are
ancestors of `4713887` and master's HEAD *is* `4713887`. **They are not in the
measurement.** Checking the artefact rather than the tree settles it:
`augment$withPropertiesOf$` in `out/AsyncBridgeProbeApp.js` contains no
`defineProperty` and no `enumerable`, so `caa8255`'s non-enumerable prototype
copy is absent. (Grepping the file for a bare `defineProperty` or `enumerable`
does *not* settle it — both appear in the vmmirror DNU-catcher installation,
which was already non-enumerable and which `caa8255`'s own comment cites as its
precedent. Extract the augment function by brace-matching to its close and test
*that* — a fixed-size window happens to work here, since the body is 411
characters, but only by luck. Checked independently twice, on both
`AsyncBridgeProbeApp.js` and the `HopscotchWebIDE.js` image it was packaged from;
they agree, as they must.)

So: **both columns mean "this artefact, on this date", and both should be rebuilt
before being quoted against a commit.** To measure the JS runtime against
`4713887` proper, somebody has to redeploy the IDE from current source and
re-package. The results below are still the answer to the gate question — the
async paths are not obviously touched by those four commits — but they are not a
statement about current master.

| Probe | psoup / WASM | NS→JS |
|---|---|---|
| 1 js-promise-control | **PASS** | **PASS** |
| **2 ns-fulfill-from-js-callback** | **PASS** | **PASS** |
| 3 ns-break-from-js-callback | **PASS** | **PASS** |
| **4 ns-raise-in-whenFulfilled** | **PASS** (derived promise broke) | **PASS** |
| 5 ns-turn-semantics | **PASS** | **PASS** |
| 6 ns-timer | FAIL — `Timer __duration:callback:repeating:` MNU | **PASS** — Timer fired |
| 7 eventual-send-to-promise | **PASS** | **PASS** |
| 8 callback-argument-order | FAIL — `ArgumentError` (psoup quirk) | **PASS** — `element=7 index=0` |
| 9 js-raise-in-then | never settles, **and aborts the VM** | HANG — rejection lost, **nothing else affected** |

**The gate is passed on both runtimes.** Probes 2 and 3 mean values and errors both cross
the boundary, so confining JS promises to an adapter is viable. Probe 4 is the
one that makes it *worth* doing: a raise inside a `whenFulfilled:` block breaks
the derived promise, so ordinary `on:Exception do:` discipline works and the
"never raise inside a `then:`" rule dies with it.

**Two API facts the probe had to discover, and they are the same on both
runtimes** (`Actors.ns` and `ActorsForJS.ns` each expose
`public Promise = PromiseUtils new`):

- A promise is an **eventual ref**. Immediate-sending `whenFulfilled:whenBroken:`
  to it raises *"Cannot immediate-send to an eventual ref"*.
- The supported form is the module's promise utilities:
  `platform actors Promise when: aPromise fulfilled: [:v | …] broken: [:e | …]`.

**Probe 9 is worse than "the rejection is lost".** In isolation it produces
exactly the signature seen in production:

```
Exception in turn without resolver: [closure] in Alien pushExpat: 'value:value:'
  -- Exception: deliberate raise inside then:
```

The downstream `onError:` never runs and the chain simply dies. Worse, in the
full battery — where probe 8's `ArgumentError` escapes an expat callback as well
— **the VM aborts**: `Aborted(native code called abort())` and
`RuntimeError: memory access out of bounds`, and probes 2, 3, 4 and 7 that pass
individually never report at all. So a raise escaping an expat closure does not
merely lose one rejection; with more than one in flight it can take down
unrelated in-flight work in the same VM.

That materially raises the priority of the psoup-side fix discussed below: it is
not just an ergonomic wart, it is a memory-safety failure reachable from ordinary
application code.

**And the NS→JS comparison localizes it.** There, probe 9 also loses the
rejection (HANG, no settlement) — so *that* symptom is common to both bridges —
but there was no abort, no renderer crash, and probes 2/3/4/7 all still reported
with probe 9's raise in flight, with Chrome's stderr clean. So the abort and the
memory unsafety are **specific to the psoup alien bridge**, not intrinsic to
raising out of an expat callback. Fixing psoup is therefore a bounded, targeted
job rather than a redesign.

### 6.1.1 The probe found a bug in `ActorsForJS` before it could measure anything

On the first NS→JS run every promise settlement failed with
`MessageNotUnderstood: ActorsForJS`DOMActor js`. Cause, at `ActorsForJS.ns:49`
in `DOMActor>>enqueueMessage:` — **one missing underscore**:

```
js call: (_js propertyOf: (_js ident: 'theGlobalObject') at: (_js literal: 'setTimeout')) with: {…}
```

Every argument is an `_js` intrinsic node, but the receiver is `js` — and the
module imports no `js` slot (WeakMap, List, Message, internalRefs, Promise,
handlerOfLastResort, defaultActor). So it compiles as an unbound name → self-send
→ DNU on the actor. The same file gets it right at lines 715, 720, 735 and 743
(`_js call: (_js propertyOf: (_js ident: 'window') …)`). Verified independently
here by reading the source.

`enqueueMessage:` is how a DOM-context actor schedules a turn, so **every**
promise settlement on the JS runtime hit it: that path cannot ever have run, and
this probe is the first thing to exercise it. With the one character fixed, the
JS runtime passes 8 of 9 — including both probes psoup fails.

Two things follow. First, the dual-runtime rule earns its keep: had we adopted
the idiom on psoup evidence alone, we would have shipped onto a runtime where
actor turn scheduling was broken. Second, the fix is a one-character change to
shared runtime code and is Gilad's call, not something to fold in silently.

**The fix is committed: master `4713887`, "Actor turn scheduling on JS: `_js
call:`, not `js call:`".** Verified here — line 49 now reads `_js call:` and the
check below comes back clean. So the NS→JS column above describes the committed
tree, not a patched one. The commit message carries the diagnosis and the probe's
role in finding it, so the reasoning lives in the history rather than only here.

To confirm the state of any tree (a worktree that has not merged master yet still
has the bug — mine did at the time of writing):

```
git -C <master worktree> log --oneline -1 -- ActorsForJS.ns   # fixed, or fixed-then-reverted?
grep -nE '(^|[^_])js call:' ActorsForJS.ns                    # a hit = still unfixed
```

The regex matters: `js call:` is a *substring* of the corrected `_js call:`, so a
plain `grep "js call:"` reports "unfixed" on a fixed tree too — it matches lines
49, 715, 720, 735 and 743 either way. Requiring that `js call:` is not preceded
by an underscore is what discriminates: one hit (line 49) before the fix, none
after. Verified both ways.

Where the bug is still present, "promise settlement does not work on the NS→JS
runtime" is **true of that tree** — the probe results above do not apply to it.

### The alternative worth weighing

The lost-rejection behaviour is a psoup bridge defect. **Fixing it** is a
psoup-side change that de-risks every existing async call site without migrating
anything — and it is worth doing even if we adopt Newspeak promises, since the
adapter will still raise across that boundary. It may well be higher leverage per
hour than the migration; it should not be assumed away by it.

## 7. Staging

1. `/_ns/config` + path prefixes on `cors-proxy.py`, with 9999 still answering
   the old convention so nothing breaks.
2. `ThreadingHTTPServer`, loopback bind, token.
3. Fold static serving in; retire 8080.
4. Run `AsyncBridgeProbe` on both runtimes. **Decision point.**
5. `hostServices` module + `fetcher`, in whichever idiom step 4 selected.
6. `/_ns/fetch`; `local_fetch` routes through it.
7. `/_ns/bus`; Claude Code posts with `curl`, IDE receives over SSE and hydrates
   turns via `sendText:` / `addSystemNotice:`.

Repositories and Croquet migrate to `hostServices` opportunistically; neither is
blocked by it, and neither should be destabilized for it.

### 6.2 How to run it headlessly

Recipe (from newspeak-a4, verified end to end here). The native VM is not an
option: `primitives.cc` guards `JS_pushValue` and siblings with
`#if !defined(OS_EMSCRIPTEN) return kFailure;`, so the CLI VM has no JS side at
all.

```
# build (from out/, which is what :8080 serves)
cp AsyncBridgeProbe.ns AsyncBridgeProbeApp.ns out/
$PRIMORDIALSOUP/out/ReleaseX64/primordialsoup \
  $PRIMORDIALSOUP/out/snapshots/WebCompiler.vfuel \
  ./*.ns ./*.png RuntimeForHopscotchForHTML AsyncBridgeProbeApp AsyncBridgeProbe.vfuel

# drive
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new \
  --disable-gpu --no-sandbox --no-first-run --remote-debugging-port=9222 \
  --user-data-dir=/tmp/ns-probe-profile about:blank &
/Users/gbracha/software/emsdk-main/node/22.16.0_64bit/bin/node cdp-probe.mjs \
  "http://localhost:8080/primordialsoup.html?snapshot=AsyncBridgeProbe.vfuel"
```

`cdp-probe.mjs` is ~80 dependency-free lines (node 22 has global `fetch` and
`WebSocket`): attach to the page target, `Runtime.enable` / `Log.enable` /
`Inspector.enable`, navigate, collect `Runtime.consoleAPICalled`. Newspeak `out`
and unhandled-exception stack traces both arrive as console events, which is how
the results above were read.

Practical notes, each of which cost time:

- **Poll for quiet; never block on the page.** A probe that never settles is a
  *result*, and only a polling driver can observe it.
- **Give each build a unique vfuel name.** Chrome will serve a cached snapshot
  from the previous build otherwise, and you will "reproduce" stale results.
- Do **not** use the system `node` — it is v12 and broken (missing icu4c). Use
  emsdk's node 22.
- Subscribe to `Inspector.targetCrashed`: renderer death is invisible from inside
  the page.
- The `:8080` server is Gilad's; if it stops, every failure looks like a boot
  failure.

## 8. Open questions

- **ANSWERED (§6.1): both runtimes pass the gate.** The remaining question is
  what to do about the two defects the probe exposed — the `ActorsForJS`
  missing underscore (fix uncommitted in master, Gilad's call) and the psoup
  abort/memory-unsafety on a raise escaping an expat closure.
- **Token distribution.** The IDE needs the token to call `/_ns/*`. Printed by
  the server and pasted into localStorage once, like an API key? Written to a
  file the static handler serves only over loopback?
- **Does `hostServices` belong in the psoup platform, the Hopscotch platform, or
  both?** It is not GUI-related, which argues for the lower layer; but its first
  consumers are all IDE-side.
- **What does the reflector actually need?** The Croquet instance owns that; the
  discovery entry above assumes a plain `ws://` URL and may be too simple.
- **Does the bus need per-path scoping?** One token granting fetch *and* prompt
  injection may be too coarse.
