# Session summary 2026-09-06..13: host services on Croquet, bus locality, chat divergence

The arc took the host from "shipped, but absent under collaboration" to a
collaborative host: every outside operation an IDE performs — model discovery,
document loading, model completions, agent-bus traffic — now happens **once per
session** rather than once per client, and a late joiner replaying history
consumes the recorded result instead of repeating the operation against a source
that may have changed. It ends with the fragment-id divergence that had been
making chats "work for a while" finally understood and measured.

Companions: `HOST_SERVICES_DESIGN_2026-08-31.md` (rationale; §5 is this arc's
design), `HOST_SERVICES_FOLLOWUPS_2026-09-05.md` (punch list, item 1 now
closed), `AI_BUS_GUIDE_2026-09-04.md` §3.5 (bus locality),
`CROQUET_REPLAY_CONTAMINATION_2026-09-12.md`,
`CODEMIRROR_ID_DIVERGENCE_2026-09-12.md`,
`CROQUET_SCOPED_FRAGMENT_IDS_2026-08-18.md` (the invariant everything here
turns on).

## Commits this arc

newspeak master:
- `87a082d` host services, coordinated IO, and ordered delivery of the result
- `553509f` probe batteries for coordinated IO, and the fixtures they run against
- `9141e50` programmatic editor changes stay local; only user edits are published
- `b82f0be` AI tool results are shared, not computed per client
- `ad638e9` bus locality: the client that can reach the agent is the one that
  talks to it (also carries the fragment-id minting ledger)

Merged to `webide-ai-access` as `fee6a22`.

primordialsoup:
- `848b788` Host: bytes and POST capabilities, loopback gate on the dev fallback
- `bb17ea7` Host: `shareText:via:` seam; replay pacing in the Croquet glue
- `cea25f1` Croquet glue: answers for abstaining clients, and a fragment-id ledger

## What was built, and the invariants that make it work

**`HostForCroquet`** overrides `platform host` under Croquet, exactly as the
design anticipated: the elected client performs the operation at the boundary
and the *result* enters the session as a recorded event. Two capabilities:

- `Fetcher` — text/bytes, GET/POST. Text results ride the recorded event itself;
  bytes go through the session Data API. **That distinction is load-bearing.**
  The Data API read is a round trip *outside* the dispatch chain that orders
  every other event, so anything a synchronized handler will later READ — a
  model list a menu is built from, above all — must come through the text path,
  or a replaying client reaches the reader before the answer lands.
- `Performer` — `performText:via:`, for an exchange the caller carries out
  itself. It exists because the bus's reply does not come back from the request
  at all but later on a shared stream, correlated by id, so there is no URL for
  the Fetcher seam to key on.

**Sharing keys are minted inside the host**, from the URL (plus body digest for
a POST) the caller already passed, so a collaboration-oblivious application
stays oblivious. The key carries a per-digest ordinal, which is what lets the
same resource be fetched more than once and replayed in order. Agreement needs
only that clients fetch a resource the same number of times in the same order.

**Bus locality.** The bus is per-machine — an agent is a process on one
participant's front door — so election alone is wrong. Each client asks its own
front door (`/_ns/bus/agents`, new; subscribers declare `?name=`) and only then
joins the election; a client that cannot reach the agent **abstains** and
consumes the recorded reply. An unobtainable answer is optimistic, which
reproduces the pre-existing behaviour and fails safe: everyone believing
themselves able still elects one performer, everyone abstaining elects none.

**Tool results are shared, not recomputed** (`b82f0be`), and programmatic
editor changes are no longer republished (`9141e50`). These two removed the
per-client divergence that the chat UI was amplifying.

## The chat divergence — what it actually was

Worth recording because it cost most of the arc and four wrong theories.

A synchronized fragment's id **is** its Croquet event address, minted from a
per-type counter at construction, so clients agree about which widget an event
names only while they construct in the same order and number. `ChatStatusPresenter`
builds a different number *and type* of those fragments depending on
`subject waiting` / `errorMessage` / `canRetry` — all per-client:

```
waiting = {button: 1}
idle    = {imageButton: 2, dropDownMenu: 1}
```

Measured live across three clients: the originator was `nsbutton_` **+5** with
`nsdropdownmenu_` **equal** — five extra waiting-state renders, driven by local
`updateGUI:` calls that no replaying client reproduces. From that skew every
button minted afterwards is misaddressed; the chat's Send/Cancel/Retry were
minted after, the rest of the IDE's buttons before. Hence a dead chat in a
session that otherwise syncs, on the *originating* clients too, with no joiner
involved. The joiner additionally paid 15s per unmatched event during replay,
which is why it looked hung rather than wrong.

Wrong theories, recorded so nobody re-walks them: render-count skew in
`newIdFor:` (real waste, but both clients incur it identically); "the joiner is
just slow"; a boot/replay ordinal skew; and scoping as the fix (these fragments
are at root scope with monotone counters, so a scope would contain the damage
without preventing it).

**The fix that landed came from the platform, not the application** — sharing
tool results and not republishing programmatic edits — which preserves the
central goal: non-collaborative code ports cleanly and becomes collaborative
without application-level change.

## Instrumentation

**The fragment-id minting ledger** records every mint as
`{type, ordinal, scopePath, presenter}` so two clients can be diffed directly:
the first differing index *is* the divergence and the entry names who caused it.
`nsLedgerTotals()` / `nsLedgerBlockHashes(step)` / `nsLedgerSlice(from,to)` /
`nsLedgerReset()`. **Opt-in** (a bridge crossing per construction): set
`localStorage ns_mint_ledger = 'on'` and reload, or `&mintLedger=on` in the URL —
the flag is read once before the first fragment exists, so it cannot be toggled
mid-session.

Probes in `croquet-probes/` (see its README): `model-discovery-battery.js` (18),
`completion-election-probe.js`, `bus-election-probe.js`, `bus-locality-probe.js`
(two clients behind two front doors, agent on one), `chat-id-divergence-probe.js`
(proves the state-dependent minting by construction; its failing assertion is
the regression test). `NS_WEB_ROOT` points a probe's front doors at a staged
copy of `out/` so a runtime change can be tried without writing into a tree a
live session is served from.

## OPEN ITEMS

1. **Inbound bus traffic is not coordinated** — followup 7 in
   `HOST_SERVICES_FOLLOWUPS_2026-09-05.md`, recorded in
   `HostForCroquet>>busAvailable`'s comment. Outbound is settled; inbound
   messages/notices arrive per client, unordered and unrecorded.
2. **`ChatStatusPresenter` still mints a state-dependent number of ids.** The
   platform fixes removed the trigger, not the hazard. Making the transient
   controls non-synchronizing (and syncing the model *decision* rather than the
   picker widget) would close it; stress testing decides whether it is worth it.
3. **A live divergence alarm** — clients compare ledger digests at
   synchronization points so the next violation reports itself at the moment it
   happens rather than being reverse-engineered from a dead chat.
4. **Stale front door.** A `cors-proxy.py` or `bus-claude.py` started before
   2026-09-12 predates `/_ns/bus/agents` and `?name=`; the locality gate then
   falls back to optimistic and is not in force. Restart both after a rebuild.
5. Followups 2, 3, 4, 5, 6 in the punch list, unchanged.

## Hazards relearned this arc

- **Stale probe front doors.** Doors left by a crashed run answered on the same
  ports for three consecutive runs; every measurement was of the wrong server
  and the wrong runtime. The probes now refuse to start if the port is taken.
- **A route handler must return True.** `/_ns/bus/agents` returned `None`, the
  dispatcher fell through to the static handler, and two responses went out on
  one connection. `curl` swallowed it; node did not.
- **`git diff HEAD` direction when merging concurrent work.** klodAI saved from
  the live IDE into the same tree. Check that the working copy *contains* the
  other party's committed additions and audit every deletion before committing.
- **An await must not append to recorded history.** The first version of
  `coordinatedFetch_await` answered with `publishEventAndData`, which records —
  and the asking client may itself be replaying, so it skewed the very cursor it
  depended on. It now answers on `model_coordinatedFetch_awaited`, subscribed
  uncounted.
- **Check the observable discriminates** before trusting a negative result.
