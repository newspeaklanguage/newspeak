# Host services — open followups

**Written 2026-09-05; revised 2026-09-13.** The host-services program (one
origin, `platform host`, `local_fetch` server-side, the agent bus, Level 2
agent-backed chats) is functionally complete and shipped. This document is the punch list of what is
*deliberately left open*, so a future session can pick any item up without
re-deriving the context. Nothing here is blocking; each is opt-in.

Reference material this builds on:
- `HOST_SERVICES_DESIGN_2026-08-31.md` — the design and rationale (its §8 is the
  original open-questions list; this doc supersedes and expands it).
- `AI_BUS_GUIDE_2026-09-04.md` — the operator/reader guide to the bus, both
  directions and Level 2.
- Auto-memory `project_host_services` — running status with commit SHAs.

## What is already done (baseline — do not rebuild)

Staging steps 1–6 of the design, plus Level 2, are built, IDE-tested and
committed on both `webide-ai-access` and `master` (and `Host.ns` in the
primordialsoup repo on `extraRevs`):

- One front door (`tool/cors-proxy.py`): static serving, `/files`, `/_ns/config`,
  `/_ns/token`, `/_ns/git`, `/_ns/fetch`, `/_ns/bus`. `server3.py` retired; the
  legacy `:9999` listener retired (default off).
- `platform host` on every non-Croquet platform (lazy, fail-closed discovery;
  `fetcher`, `serviceOrigin`, `gitAvailable`/`fetchAvailable`/`busAvailable`,
  `croquetReflector`/`croquetFiles`).
- `local_fetch` runs server-side through `/_ns/fetch` and is the model's default;
  `web_fetch` is the billed fallback.
- The agent bus, both directions (`send_to_chat` peers, external agents in/out),
  and **Level 2**: Bus Agent chats backed by an external agent — `BusProvider`
  (transport-swapped `AnthropicProvider`), the completion port, and the two
  reference responders `tool/bus-responder.py` (human) and `tool/bus-claude.py`
  (headless Claude Code: per-chat `--resume` session memory + `TOOL_CALL`
  IDE-tool driving).

**Added 2026-09-06 … 09-13** (this was followup 1, now closed — see below):

- `HostForCroquet.ns`: the collaborative host. `Fetcher` (text/bytes, GET/POST)
  and `Performer` (an exchange the caller carries out itself) over coordinated
  IO — one elected client performs, every other client and every late joiner
  replaying reads the recorded result. Text results ride the recorded event so
  they are delivered in dispatch-chain order; bytes go through the session Data
  API. Commits `87a082d`, `553509f`, `b82f0be`, `ad638e9`.
- Model discovery, document loading and model completions each go out **once per
  session** rather than once per client.
- Bus locality: the bus is per-machine, so a client asks its own front door
  whether the addressee is reachable (`/_ns/bus/agents`, named subscribers) and
  only then joins the election; clients that cannot reach it abstain and consume
  the recorded reply. `AI_BUS_GUIDE_2026-09-04.md` §3.5.
- AI tool results are shared rather than recomputed per client, and programmatic
  (synchronization-applied) editor changes are no longer republished
  (`CROQUET_REPLAY_CONTAMINATION_2026-09-12.md`).
- Probe batteries in `croquet-probes/` for all of the above.

---

## Open followups

### 1. Croquet host override — ~~the main designed-but-unbuilt piece~~ DONE 2026-09-12

**Built as designed**, and the description below is retained because the
reasoning still explains *why* it is shaped this way. `HostForCroquet` overrides
`host` and indirects through the reflector exactly as anticipated: the elected
client performs the operation at the boundary and the result enters the session
as a recorded event. See the baseline section above for what landed and the
commits. What remains is item 7.

**What.** Give the Croquet platform a `host` that works under live
collaboration. Today the Croquet runtimes have **no `host` mount** on purpose,
so under a Croquet-synced session `platform host` is nil and every host/AI
feature (AI chats, `local_fetch`, git, the bus) is absent — the guarded
`[platform host] on: Exception do: [:e | nil]` slots in `AIAccess`/
`AI_IDE_Support` fail closed there.

**Why it isn't just "mount it too."** Under Croquet the IDE is *part of the
synced computation* — there is no client-private "view" to hide client-divergent
state in. If two collaborators' hosts answered discovery or a fetch
differently (one has the front door, one doesn't; two different networks), that
divergence would break determinism. So the design (§5, decided 2026-08-31) is:
the Croquet platform **overrides `host` to indirect through the reflector**, the
way file access already does — a collaborator's host performs the operation at
the boundary and the *result* enters the session through the reflector, shared
with every collaborator and present in the replay history. Divergent
availability/answers become shared session state instead of a determinism
hazard. The token stays in each client's local glue and never enters the event
stream.

**Entails.** A Croquet-side platform variant of `Host` (in the Croquet runtime
modules — `RuntimeForCroquetJS.ns` / `HopscotchForCroquet.ns`) whose capability
calls are published as Croquet events and whose results are read back from the
synced model, mirroring how `/files` is already handled. Needs the Croquet
owner's input on the event shape and on which host services are even
appropriate to share wholesale (a fetched body enters the persisted replay
history — fine for determinism, but it widens who sees it and for how long;
the bus especially carries prompt traffic).

**Priority.** Only matters if you run host/AI features inside a live Croquet
session. If Croquet+AI is not a current scenario, this can wait indefinitely;
the fail-closed absence is correct in the meantime.

**Interim rule (already in force).** Base `host` must not be consulted from code
running under Croquet — which is why the mounts were deliberately omitted there.

### 2. `/_ns/files` — a host file-read service

**What.** Let the AI read host files outside `out/` (e.g. Newspeak sources in
the tree). Today no fetch path can reach the filesystem: the browser refuses
`file:`, `local_fetch`'s proxy fallback only rewrites `https://`, and `/_ns/git`
mints `https://<host>/…` by construction. Those are scheme checks, not an auth
boundary.

**Entails.** Its own path (`/_ns/files/…`) on the front door, its own
`/_ns/config` key, a **declared root directory** it is confined to, behind the
existing loopback+token gate. Expose it as a `platform host` member and an AI
tool. Never accept `file:` through `/_ns/fetch`.

**Priority.** Opt-in; build when a concrete need appears (e.g. the AI wants to
grep the real source tree rather than the `out/` copy).

### 3. Bus per-path token scoping

**What.** One token currently grants both `/_ns/fetch` and `/_ns/bus` (prompt
injection). The v1 answer — opt-in `--bus` (default off) + loopback + one token
— is fine, but a future need might want fetch and bus separable while both are
on.

**Entails.** Distinct tokens or scoped tokens per `/_ns` capability, checked in
`require_token`. Small, isolated change to `cors-proxy.py` plus the clients that
read the token.

**Priority.** Low; revisit only if the coarse grant becomes a real concern.

### 4. Reflector discovery shape

**What.** `/_ns/config`'s `croquet.reflector` is a single `ws://` URL. It may be
too simple if the Croquet client ever needs more than an address. Scheme itself
is settled (`ws://` now, `wss://` mandatory once the front door goes https).

**Priority.** Croquet-owned; leave until the Croquet side asks for more.

### 5. Level 2 refinements

*Note 2026-09-13:* the tool cycle changed underneath this item — tool results are
now computed once and shared rather than recomputed per client (`b82f0be`), so
re-check these against the current `bus-claude.py` before acting on them.


- **Native/validated tool-use for IDE-tool driving.** The `TOOL_CALL` text
  protocol in `bus-claude.py` is a text convention parsed heuristically (a
  headless `claude -p` returns text, not the API's structured tool-use). It
  works and is tolerant, but if reliability bites in real use, the sturdier
  paths are: an **API-forwarder** backend (native, schema-validated tool_use
  over the request's tools — loses the host-capable agent), or exposing the
  IDE's tools to `claude -p` over **MCP** (needs an out-of-band tool-execution
  channel the IDE does not have today). Only worth it if the text protocol
  proves flaky.
- **Multiple tool calls per turn.** `bus-claude.py` emits at most one `TOOL_CALL`
  per turn; the IDE's loop supports several. The agent can already iterate turn
  by turn, so this is a minor efficiency nicety.

### 6. Delete the legacy `:9999` code (eventually) — still open

Still exactly as written: the listener is default-off but the code is still
there as an opt-in escape hatch, so the deletion this item asks for has not
happened.


The legacy bare-proxy listener is default-off (`--legacy-port 0`) and all
clients use `/_ns/git`. Once you're confident no un-rebuilt client anywhere
still points at `:9999`, the legacy-listener code in `cors-proxy.py` can be
deleted outright rather than kept as an opt-in escape hatch.

### 7. ~~Inbound bus traffic is not coordinated~~ DONE 2026-09-14

**Built as described below**: newspeak `d6ef14e` + psoup `122cbc8`. Inbound
messages and notices now go through a synchronized inbox
(`hopscotch synchronizedInbox:post:payload:`, applied by
`AI_IDE_Support>>applyBusEvent:`): the client that receives a frame posts it
once, keyed by the stream's event id, and every participant applies it in the
recorded order. The INBOUND probe mode passes 14/14. With this, every
host-services item that the Croquet host was designed around is closed; the
remaining items (2–6) are independent of Croquet.

The description as it stood while open:

The one gap the Croquet host leaves open, and it is recorded in
`HostForCroquet>>busAvailable`'s comment so it cannot be lost. Outbound is
settled — a completion or a `send_to_agent` goes out once per session, from a
client that can reach the agent. **Inbound is not:** messages and notices arrive
on each client's own event stream, in whatever order that stream delivers them,
and nothing records them. A session whose chat receives unsolicited bus traffic
can therefore diverge on it. Completions — which is what a Bus Agent chat
actually turns on — do not.

The destination is to publish inbound bus traffic as synchronized events, so it
enters the session the way every other shared fact does.

---

## Not host-services (mentioned so nobody conflates them)

These are separate arcs with their own docs/memory, not part of this program:
Croquet fragment-identity plan, NS2JS transpiler, the typechecker, Ampleforth
site work. If a session is here for host services, those are out of scope.
