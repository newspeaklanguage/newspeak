# Host services: one front door, one Newspeak capability, one async idiom

**Status:** design for review, 2026-08-31. Nothing implemented.
This supersedes `HOST_SERVICES_DESIGN_2026-08-16.md` as the design statement;
the older document remains the record of the evidence behind it — the
`AsyncBridgeProbe` runs, their provenance caveats, and the bugs they exposed.
All of its corrections (the Croquet owner's discovery shape, the probe
results) are folded in here as settled facts.

Three decisions are entangled, and writing them separately guarantees they
disagree: how local services are **served**, how Newspeak **reaches** them, and
what async values **look like** once they arrive. This document covers all
three.

Everything below must work on **both runtimes** — primordialsoup (WASM) and the
NS→JS deploy. That constraint decides several of the choices and is called out
where it bites.

---

## 1. The problem

Three servers run today, differing in kind:

| Port | What | Whose code | Protocol |
|---|---|---|---|
| 8080 | static `out/` (also the Croquet file server, PUT/GET under `/files`) | Python stdlib (`server3.py`) | HTTP |
| 9999 | CORS proxy for git and `local_fetch` fallback (`tool/cors-proxy.py`) | ours, Python stdlib | HTTP |
| 9090 | Croquet reflector | third-party, Node | WebSocket |

All three bind `0.0.0.0`, unauthenticated. On top of them, the AI's
`local_fetch` tool is **implemented and working**: it fetches directly from the
browser and falls back to the 9999 proxy on a transport failure. Its limitation
is diagnostic, not functional — when a fetch never completes, the browser
exposes no status, headers or body, so the tool can only report that opacity.
Two *server-side* services are scoped but not built: a diagnostics fetch
endpoint (`/_ns/fetch`, which sees what the browser cannot) and a message bus
for talking to Claude Code sessions.

The pattern: **we keep meeting capabilities the browser sandbox denies us, and
each has arrived as its own port with its own configuration surface.** The git
proxy URL is a per-repository field; the reflector URL lives in the bootstrap
page; the static root is wherever Python was launched. Each is a place where
dev and deploy drift apart.

## 2. Principle: consolidate the origin, not the process

One process is the wrong goal. The reflector is third-party Node code speaking
WebSocket, deliberately swappable; absorbing it couples us to a dependency we
want at arm's length, and one process means one crash takes out git, fetch,
chat and sync together.

One **origin** is the goal. If everything the browser talks to lives at one
`host:port` under reserved paths, then CORS is structurally gone rather than
proxied around; there is one thing to start; there is one auth boundary; and —
the real payoff — **the IDE stops hardcoding ports**, because every service is
a relative path.

```
/                       static (out/), including /files (Croquet file store)
/_ns/git/<host>/<path>  the existing @isomorphic-git/cors-proxy convention
/_ns/fetch?url=…        diagnostics fetch: status, headers, redirects, body
/_ns/bus                SSE + POST — the agent channel
/_ns/config             discovery: what this origin actually offers
```

`_` is illegal in hostnames, so `/_ns/…` can never collide with a proxied host;
the existing git convention keeps working untouched.

**The reflector stays its own process**, discovered through `/_ns/config`
rather than absorbed. Reverse-proxying a WebSocket upgrade through Python's
stdlib `HTTPServer` means hijacking the socket and pumping bytes both ways, and
it puts our process in the latency path of the one latency-sensitive thing we
have. Revisit only if a single port through a firewall becomes a requirement.

## 3. The discovery contract

`GET /_ns/config` is the keystone: it is what makes everything else
incremental, and the one piece server and Newspeak must agree on exactly.

```json
{
  "version": 1,
  "git": true,
  "fetch": true,
  "bus": false,
  "croquet": {"reflector": "ws://localhost:9090", "files": "/files"}
}
```

Rules:

- **Absent means unavailable.** A missing key, a 404 on `/_ns/config`, a
  connection refused, and a malformed body are all the same answer: that
  capability is not here. Fail closed.
- **A deployed origin answers 404 and that is correct.** newspeaklanguage.org
  serves `/` and nothing under `/_ns/`, so the deployed IDE lights up exactly
  the features that work there. Same code, same relative paths, no localhost in
  the image, no per-deployment configuration.
- **Values, not just booleans, where a value is needed.** `reflector` is a URL
  because it names a different origin.
- `version` exists so the Newspeak side can refuse a contract it does not
  understand rather than guessing.

The `croquet` shape (confirmed with the Croquet instance):

- The file server **is the static front door** — `/files` is a reserved path,
  not a separate service. `out/files/` also holds session blob state and deploy
  staging, so the path is load-bearing on disk.
- `files` is **effectively mandatory**: passing `reflector=` sets
  `signServer:"none"`, which kills default file-server resolution; `files=`
  restores it keylessly. The large-payload detour stores oversized editor
  keystrokes there — no `files=`, no usable editors.
- Param names are the Croquet client library's own, so discovery → URL
  construction is a rename-free pass-through. `reflector` stays **absolute**
  (different scheme and port); `files` is deliberately **origin-relative**, so
  it survives localhost → https and host renames unedited. An absent `croquet`
  key means "no local Croquet — use whatever the page was given".
- **Do not publish `box=`** (it implies the reflector WebSocket lives behind
  this origin — exactly the reverse-proxying we avoid) and **do not put
  `apiKey`/`sessionId`/`pwd`/`appId` in discovery** — they are session- and
  app-level, not host-level. (`apiKey=none` must still appear on the page URL
  or `Session.join` throws; its value is ignored once `reflector=` is given.)

Two constraints on later work: the reflector's port 9090 is **hardcoded** in
`reflector.js` (no CLI or env override), so the server side cannot move without
patching; and when the front door goes https, **wss is not optional** —
browsers block `ws://` from an https page as mixed content.

## 4. Server shape

Keep `tool/cors-proxy.py` as the front door: it is the only server we own, it
is stdlib-only (no `pip install` — a real virtue for a project whose pitch is
"open the page"), and it already proxies generically.

Three changes, in order:

1. **`ThreadingHTTPServer`.** One line, stdlib. A *prerequisite*, not an
   optimization: the server is single-threaded today, so one SSE stream on
   `/_ns/bus` would block every git clone.
2. **Bind loopback, require a token.** Today `*:9999` forwards an
   `Authorization` header for anyone on the network — tolerable for a dev git
   proxy. `/_ns/bus` is a different animal: it injects prompts into an IDE that
   edits and runs code, which is remote control. Auth must land *before* the
   inbox exists; retrofitting it onto a channel other things already use is how
   this goes wrong. The same gate applies to any future filesystem capability
   (§8).

   **Distribution (decided 2026-08-31): the token is a file.** The server
   mints it at startup and serves it at a reserved path answered only to
   loopback clients; the page fetches it before its first `/_ns/*` call.
   Nothing is pasted, and nothing rests in localStorage — which the Croquet
   runtime virtualizes per-session and clears at startup anyway
   (`JSForCroquet.ns`). A page loaded from another
   machine cannot fetch the token, gets no capabilities, and fails closed,
   which is the correct semantics: host services are per-host.
3. **Serve `/` from `out/`**, so static content and services share an origin
   and 8080 can retire.

`/_ns/fetch` returns an envelope rather than a bare body, because it exists to
see what neither existing instrument can: the provider's server-run `web_fetch`
collapses every failure into one opaque string, and the browser-side
`local_fetch` gets no status, headers or body when a request never completes:

```json
{"status": 403, "statusText": "Forbidden",
 "headers": {"server": "cloudflare", "cf-ray": "…"},
 "redirects": ["https://…"], "elapsedMs": 412,
 "body": "…first N KB…", "truncated": true}
```

An error *page* is frequently the whole answer — a Cloudflare 1014 names the
misconfiguration outright — so the body is returned on failure, not discarded.

The git path stays a byte-transparent tunnel and does **not** adopt the
envelope: isomorphic-git speaks smart-HTTP (streaming binary POST bodies, exact
header passthrough), and its client already knows the `corsProxy` prefix
convention. Distinct paths for git and fetch are what make per-capability
scoping possible later.

## 5. Newspeak shape: `platform host`

A module, exposed on the platform beside `js`, `kernel`, `hopscotch`,
`aiAccess`.

**Placement (decided 2026-08-31): the psoup platform** — the base layer, not
the Hopscotch layer; these capabilities are not GUI-dependent. One
implementation fact qualifies the rollout: the platform classes are
*parallel* definitions built from the manifest, not layers — the Hopscotch
`Platform` (`RuntimeForHopscotchForHTML.ns`) does not wrap the base one
(`primordialsoup/newspeak/RuntimeForPrimordialSoup.ns`). So `host` is mounted
on each platform separately: on the HTML platform first (a `lazy` member
beside `aiAccess`, hot-load-safe), and on the base psoup platform and
`RuntimeForJS` at the next rebuild for parity. The module itself is written
against `platform js`/`actors`/`collections` only, so every mount shares one
definition.

**Why it earns platform status** is capability attenuation, not tidiness.
Everything it does ultimately goes through `platform js`; today any code that
needs to fetch a URL is handed *all of JavaScript*. This lets us hand an
application a fetcher without handing it `js global`. Second, deployment:
platform variants are the established way to express "this environment doesn't
have that" — a platform built without the slot makes dependent features
structurally unavailable rather than failing at first call.

**Name (decided 2026-08-31): `platform host`.** In the object-oriented
spirit: the exposed object *represents the host*, and the services are its
methods — `platform host fetcher` reads as "the host's fetcher". The rejected
candidates fail as before: `localServices` lies in a deployment, where the
service is same-origin but not local — and dev/deploy parity is the point;
`webGateway` is too narrow, since the bus is not web egress and reflector
discovery is not either. `host` names the provider, covers both environments,
and promises no particular protocol.

**Not a façade — a namespace of separately-obtainable capabilities.** Clients
take only what they need, in the ordinary import-slot idiom:

```
private Fetcher = platform host fetcher.   (* nil when unavailable *)
```

Attenuation then means something: the repository module never touches the bus,
the AI module never touches the git proxy.

**Membership rule** (to go in the class comment, or drift is certain): *a
member is something the browser sandbox forbids, provided by the host at the
shared origin, and independently absent.* An application-specific endpoint
fails that test — it belongs in an app module that *uses* `fetcher`.

**Availability protocol.** Discovery is asynchronous but callers mostly want a
synchronous "can I render this button?". Probe once during platform
construction, cache, and expose synchronous accessors afterwards, with
`whenReady:` for code that must wait. Two implementation constraints: hold the
cache in a **lazy** slot, so nothing is fetched at snapshot time and a hot-load
does not crash on a nil eager slot; and **fail closed**, so "no answer yet" and
"no server" both render as unavailable rather than as an error.

**Dual-runtime.** `host` must not be psoup-specific: write it against
`platform js` and `platform actors` only, so one module definition serves both
runtimes. If a runtime-specific variant ever becomes necessary, the existing
rule applies — the psoup API is canonical and the JS platform library is what
gets fixed.

**Croquet (future work, not part of the initial build).** Under the Croquet
runtime the IDE itself is part of the synced computation — there is no
IDE-side "view" in which to confine client-divergent state. The answer is the
platform-variant mechanism again: the Croquet platform **overrides
`host` to indirect through the reflector**, the way file access
already works. A collaborator's own host performs the operation at the
boundary, and the *result* enters the session through the reflector — shared
with every collaborator, present in the replay history — so divergent
availability and divergent answers become shared session state rather than a
determinism hazard. The token itself stays in each client's local glue and
never enters the event stream. Until that override exists, the base
`host` must not be consulted from code running under Croquet.

## 6. Async idiom: confine JS promises

JS promises have spread through the system and are load-bearing in a way that
costs us: every async method carries defensive tics for bridge hazards, each
re-learned by every reader. Two reframings make this tractable:

1. **It is a boundary question, not a replacement question.** Every async value
   originates JS-side — `fetch`, `setTimeout`, `FileReader`, `EventSource`,
   isomorphic-git. Something must convert. The achievable goal is *confine JS
   promises to a thin adapter and use Newspeak promises above it*; "eliminate
   them" is not a thing.
2. **Promises are not actors.** Adopting Newspeak promises as the async value
   type is local: one heap, Hopscotch's synchronous object graph untouched.
   Adopting the *actor* model — separate heaps, eventual-only sends, far
   references — collides head-on with Hopscotch. This design adopts the first;
   the second may never be worth it.

**The gate has been passed.** `AsyncBridgeProbe` ran on both runtimes
(2026-08-25; results, provenance caveats and method in the 2026-08-16
document): a Newspeak promise can be fulfilled and broken from inside a JS
callback on both bridges, and a raise inside a `fulfilled:` block breaks the
*derived* promise. So above the adapter, ordinary `on:Exception do:` discipline
works, async failures land in the debugger as Newspeak stacks, and the "never
raise in a `then:`" rule retires.

The adapter is where the bridge facts live, once, instead of at every call
site. What it must observe:

- **API.** A Newspeak promise is an *eventual ref*: immediate-sending
  `whenFulfilled:whenBroken:` raises. The supported form is
  `platform actors Promise when: p fulfilled: [:v | …] broken: [:e | …]`
  (identical on `Actors.ns` and `ActorsForJS.ns`).
- **Construction.** `Promise.withResolvers()` only — the `new Promise(executor)`
  pattern passes nil for both executor arguments across the bridge.
- **Callbacks** must return marshalable values, and must bind the correct
  parameter: psoup delivers the *last* JS argument to every callback parameter,
  while the JS runtime delivers the true order.
- **No raise may escape an expat closure.** On both bridges the rejection is
  lost; on psoup a second raise in flight **aborts the VM** (`memory access out
  of bounds`), taking unrelated work down. The adapter catches at the boundary
  and converts to a broken promise.
- **Timers.** psoup's Newspeak-native `Timer` path is broken (MNU); the adapter
  owns deadlines via JS `setTimeout` on both runtimes for now.

`host` is the right pilot: it is the boundary object by definition, it
is greenfield with no legacy call sites, and if the idiom fails there the blast
radius is one module nobody depends on yet.

**Separate, parallel work item: fix the psoup expat-raise bridge.** The probe
showed the abort is specific to the psoup alien bridge (the NS→JS runtime loses
the rejection but nothing else), so the fix is bounded rather than a redesign.
It is worth doing *independently* of this design: it is a memory-safety failure
reachable from ordinary application code, and it de-risks every existing async
call site without migrating anything.

## 7. Staging

1. `/_ns/config` + path prefixes on `cors-proxy.py`, with 9999 still answering
   the old convention so nothing breaks.
2. `ThreadingHTTPServer`, loopback bind, token.
3. Fold static serving in; retire 8080.
4. The `host` module + `fetcher`, in the Newspeak-promise idiom (§6).
5. `/_ns/fetch`; `local_fetch` routes through it.
6. `/_ns/bus`; Claude Code posts with `curl`, the IDE receives over SSE and
   hydrates turns via `sendText:` / `addSystemNotice:`. **Built 2026-09-04.**
   The endpoint is **off unless the front door is started with `--bus`** —
   prompt injection into an IDE that edits and runs code is the sharpest
   capability, so the operator enables it consciously; when off, `/_ns/config`
   reports `bus:false` and the path 404s. External agents `POST` a JSON
   message `{to, text, from?, kind?}`; the IDE holds a `GET` open as an SSE
   stream, matching `to` against its Root chat names and delivering through
   the **same address space and delivery core as in-image `send_to_chat`**
   (`enqueueOrDeliver:to:hop:` / `deliverPeerMessage:to:hop:`), stamped
   `[from external agent 'X']` at hop 0. `kind:"notice"` folds in via
   `addSystemNotice:` instead of driving a turn. A small server-side backlog
   plus `Last-Event-ID` covers EventSource reconnects. This settles the §8
   scoping question for v1: **one token, but the capability is opt-in at
   startup**, which is the real boundary alongside the loopback bind.

   **Reverse direction (Level 1, 2026-09-04):** the IDE also reaches OUT — a
   chat's `send_to_agent name: text` POSTs to the bus so an in-IDE AI can
   converse with an external agent (a Claude Code session, or a human on the
   other end). Addressing is symmetric: `from` is the reply address in both
   directions, so a round trip closes with no separate correlation field, and
   the agent's reply returns through the ordinary receive path as a
   `[from external agent 'X']` turn. Because a chat holds the IDE's tools
   (`evaluate`, `inspect_object`, the debugger, `propose_changes`), this makes
   an in-IDE chat a **remote-control surface** for an external agent — every
   exchange a visible turn, so the human sees it. The POST handler is a
   **pass-through router**: it stamps a server id and fills two defaults but
   forwards the poster's whole object, so a later `reply_to`/`corr_id`
   completion envelope (Level 2 — a `BusProvider` backing a chat *directly*)
   rides through untouched. `tool/bus-agent.py` is a stdlib reference for the
   external end. Level 2 (correlated request/response so a chat is backed by an
   agent or a human rather than a hosted model) is deferred but unblocked.

Repositories and Croquet migrate to `platform host` opportunistically; neither
is blocked by it, and neither should be destabilized for it.

**Parallel track (spun out 2026-08-31):** the *in-image* half of the bus —
AI sessions in one IDE messaging each other, addressed by chat-document
name — needs no server and proceeds independently; see
`AI_SESSION_MESSAGING_SPEC_2026-08-31.md`. Step 6 then extends the same
address space to external agents rather than inventing a second one.

## 8. Open questions

- **Does the bus need per-path scoping?** One token granting fetch *and* prompt
  injection may be too coarse. (Token *distribution* is decided — the
  loopback-served file, §4.) **v1 answer (2026-09-04):** one token, but the bus
  is opt-in at startup (`--bus`, default off) and loopback-bound, so enabling
  prompt injection is a conscious operator act. Finer per-path scoping remains
  possible later if fetch and bus should be separable while both are on.
- **Is a single URL field enough for the reflector?** The Croquet instance
  owns that. The scheme itself is not in question — §3 settles it (`ws://` now,
  `wss://` mandatory once the front door goes https) — but the entry may still
  be too simple if the client ever needs more than an address.
- **A file-read service?** (New, from the 2026-08-31 discussion.) Today no
  fetch path can reach the filesystem — the browser refuses `file:` outright,
  the proxy fallback only rewrites `https://` URLs, and the proxy mints its
  upstream URL as `https://<host>/…` by construction — but those are scheme
  checks, not an auth boundary. If host-file reading is wanted (e.g. sources
  outside `out/`), it must be its own path (`/_ns/files/…`) with its own
  `/_ns/config` key and a declared root directory, and it cannot precede
  staging step 2. Never accept `file:` through `/_ns/fetch`.
