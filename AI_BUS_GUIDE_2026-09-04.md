# The AI agent bus — how it works and how to run it

**Written 2026-09-04.** A guide for anyone, not only the people who built it.
It explains the background concepts (HTTP, `curl`, Server-Sent Events, the
token) before the bus itself, so you should be able to follow it even if those
terms are new.

The bus is part of the *host services* front door; the design rationale lives
in `HOST_SERVICES_DESIGN_2026-08-31.md`. This document is the operator's and
reader's guide to the one feature: the agent bus.

---

## 1. What the bus is, in one paragraph

The Newspeak Web IDE runs entirely inside a web browser. Inside it you can open
AI **chat sessions** — each is a conversation with a model (Claude, say),
backed by a document, and each has the IDE's tools available to it (it can
evaluate Newspeak code, inspect objects, run the debugger, propose edits). The
**agent bus** is a channel that lets those in-browser chats exchange messages
with **programs running outside the browser** — for example a Claude Code
session in a terminal on the same machine — addressing each other by name. It
works in both directions: an outside program can message a chat, and a chat can
message an outside program. Because a chat carries the IDE's tools, an outside
program can, in effect, drive the live IDE by asking a chat to run tools and
report back.

There is also a deeper mode, **Level 2** (§6): a chat can have *no hosted model
behind it at all* and instead be backed **entirely** by an external agent — a
headless Claude Code session, or even a human — which becomes that chat's brain,
answers its turns, and can drive the IDE's own tools directly. Sections 2–5
cover the messaging bus and its plumbing; §6 covers the agent-backed chat.

---

## 2. The background concepts

If you already know HTTP, `curl`, and SSE, skip to §3.

### 2.1 A web server, and HTTP requests

When your browser loads a page, it sends an **HTTP request** to a **server** —
a program listening on a numbered *port* on some machine — and the server sends
back an **HTTP response**. A request names a **method** (`GET` to fetch
something, `POST` to send something), a **path** (like `/_ns/config`), optional
**headers** (extra labelled key–value lines, e.g. `Content-Type: application/json`),
and, for a `POST`, a **body** (the data being sent). The response has a numeric
**status** (200 = OK, 404 = not found, 401 = unauthorized) and its own body.

In this project the server is a small Python program, `tool/cors-proxy.py`,
which we call the **front door**. By default it listens on port **8080** on
`localhost` (your own machine only — see §7 on security). It serves the IDE's
files *and* a set of special paths under `/_ns/…` — one of which is the bus, at
`/_ns/bus`.

### 2.2 `curl` — making HTTP requests from the terminal

`curl` is a command-line program that makes HTTP requests, the way a browser
does, but from a terminal and scriptable. You give it a URL and some flags. The
flags used in this guide:

| Flag | Meaning |
|---|---|
| `-s` | *silent* — don't print progress bars, just the response |
| `-N` | *no buffering* — print each byte as it arrives (needed for a live stream; see SSE below) |
| `-X POST` | use the `POST` method instead of the default `GET` |
| `-H 'Name: value'` | add a request header |
| `-d '…'` | send this string as the request body (implies `POST`) |

So this command sends a `GET` to the front door's discovery path and prints the
response:

```
curl -s http://localhost:8080/_ns/config
```

and it prints something like `{"version":1,"git":true,"fetch":true,"bus":true}`
— a small JSON document saying which services this front door offers.

### 2.3 Server-Sent Events (SSE) — a response that never ends

Normally an HTTP request gets **one** response and the connection closes. That's
fine for "fetch this page," but no good for "tell me whenever a new message
arrives," because you'd have to keep asking ("are we there yet?") — called
*polling*, which is wasteful and laggy.

**Server-Sent Events (SSE)** is a standard trick built on ordinary HTTP: the
client makes one `GET` request, and the server **keeps the connection open and
keeps writing to it over time**, one message after another, for as long as the
client stays connected. The client reads this never-ending response as a live
stream of events. Browsers have this built in as an object called
`EventSource`; the IDE uses it to receive bus messages. From a terminal, `curl -N`
(the `-N` is essential — it stops curl from buffering, so you see each event as
it lands) does the same thing.

The wire format is deliberately simple. The server writes plain text; each event
is a `data:` line followed by a blank line:

```
data: {"id":1,"to":"alpha","text":"hello","from":"Claude Code","kind":"message"}

data: {"id":2,"to":"alpha","text":"another one","from":"Claude Code","kind":"message"}

```

A line beginning with `id:` before the `data:` gives the event a sequence number
(used for reconnection, §4.4). A line beginning with a colon, like `: keepalive`,
is a **comment** — the server sends one every 20 seconds so the connection
doesn't look dead and so a dropped peer is noticed. The client ignores comments.

That's the whole of SSE: **one long-lived GET, and the server streams
`data:` lines as things happen.**

### 2.4 The token — why the bus asks for a password

The bus can inject a message into an IDE that runs code, so it must not be open
to just anyone. Every bus request must carry a secret **token**. The front door
mints a fresh random token each time it starts and serves it at `/_ns/token`,
but *only* to requests coming from your own machine (`localhost`). A program on
your machine fetches the token once and then includes it on every bus request —
as a query parameter `?token=…` on the streaming `GET` (because the browser's
`EventSource` can't add headers), or as a header `X-NS-Token: …` on a `POST`.
The token is never written to disk and never baked into the IDE image.

---

## 3. How the bus works

### 3.1 The pieces

- **The front door** (`tool/cors-proxy.py`) hosts the bus at `/_ns/bus`. It is a
  **router**: it does not understand or judge messages, it just moves them.
- **Subscribers** hold a streaming `GET` open (SSE). The IDE is a subscriber
  (it subscribes automatically at startup). An external agent becomes a
  subscriber by holding its own `GET` open.
- **Senders** make a `POST` with a JSON message. Anyone with the token can send.
- **A message** is a small JSON object. The two fields that matter for routing
  are `to` (the name of the intended recipient) and `from` (the sender's name,
  which doubles as the address to reply to). Optional: `text` (the content) and
  `kind` (`"message"`, the default, or `"notice"`, explained in §5).

### 3.2 Addressing by name — and the one rule that makes replies work

Every participant has a **name**, which is just a string. In-IDE chats are named
by their chat document (e.g. `alpha`). External agents pick their own name
(e.g. `claude-code`). Names live in one shared space; the bus doesn't care
whether a name belongs to a chat or an external program.

When the front door receives a `POST`, it **fans the message out to every open
subscriber**. Each subscriber then keeps only the messages whose `to` matches
its own name and ignores the rest. (On a loopback dev machine this broadcast is
simple and fine; if it ever matters, subscribers could register their names for
targeted delivery — but that's not needed today.)

The key convention: **`from` is the reply address.** If `claude-code` sends a
message to `alpha`, `alpha` sees it came `from: "claude-code"`, so to reply
`alpha` simply sends a message addressed `to: "claude-code"`. The same in the
other direction. This symmetry is why a full back-and-forth needs no special
"reply-to" bookkeeping.

### 3.3 What happens when a chat receives a message

This is the interesting half, because a chat is an AI with tools. When the IDE's
subscriber sees a message whose `to` matches one of its chat names, it delivers
that message into the chat **as a real user turn** — a visible bubble stamped
`[from external agent 'X']` (where X is the `from`) — and drives the chat to
respond, exactly as if a person had typed it. So:

- The message is **visible** in the transcript. Nothing happens off-screen; the
  human watching the IDE sees every exchange. This is the audit trail.
- The chat's AI can **use its tools** in response. If the message asks it to
  evaluate an expression or inspect an object, it runs the IDE tool and can send
  the result back with `send_to_agent` (§5). This is how an outside agent
  "drives" the IDE — indirectly, through a cooperating chat, with every step on
  the record.
- The chat's reply, if it chooses to answer, goes back out over the bus and
  arrives at the sender as another message.

### 3.4 The two directions, concretely

```
  EXTERNAL  →  IDE                        IDE  →  EXTERNAL
  ---------------------------             ---------------------------
  an agent POSTs {to:'alpha',             chat 'alpha' calls its
     from:'claude-code', text}               send_to_agent tool
        │                                     with name 'claude-code'
        ▼                                        │
  front door fans it out                         ▼
        │                                  front door fans it out
        ▼                                        │
  IDE's subscriber sees to=alpha                 ▼
        │                                  the agent's own subscriber
        ▼                                     sees to=claude-code
  delivered into 'alpha' as a                    │
  [from external agent 'claude-code']            ▼
  turn; alpha's AI responds               the agent reads it and,
        │                                  if it likes, POSTs a reply
        ▼                                  {to:'alpha', from:'claude-code'}
  alpha replies via send_to_agent                │
  to 'claude-code' … ─────────────────────────► … which arrives as the
                                           next [from external agent] turn
```

Both directions are the same mechanism (POST to send, SSE to receive); the only
difference is who is subscribed under which name.

---

## 4. How to run it

### 4.1 Start the front door with the bus enabled

The bus is **off by default** — you turn it on with `--bus`, a deliberate choice
because it is remote control of something that runs code. From the newspeak repo
(either worktree):

```
python3 tool/cors-proxy.py --bus
```

This serves the IDE and the `/_ns/…` services on `http://localhost:8080`, with
the bus live. Confirm it's on:

```
curl -s http://localhost:8080/_ns/config
# → {"version": 1, "git": true, "fetch": true, "bus": true}
```

`"bus": true` means the bus is enabled. Without `--bus` it reads `false` and the
`/_ns/bus` path returns 404 (not found).

### 4.2 The IDE end needs nothing

Open the Web IDE from that front door as usual. At startup it automatically
fetches the token, opens its SSE subscription, and is ready to receive. Any chat
you create (say, one named `alpha`) is immediately addressable by that name. No
configuration.

### 4.3 Being the external agent — the easy way

A small reference program, `tool/bus-agent.py`, is the "other end." Run it with
a name to subscribe under:

```
python3 tool/bus-agent.py claude-code
```

It fetches the token, subscribes as `claude-code`, prints any message addressed
to `claude-code`, and lets you send messages by typing at the prompt:

```
alpha  Hello alpha, what is 6*7?
```

(the first word is the destination name, the rest is the text). Messages from
chats appear as they arrive, with a reminder of how to reply. That's a complete,
live, two-way conversation between a terminal and an in-IDE chat.

### 4.4 Being the external agent — the raw way (understanding the plumbing)

You can do exactly what `bus-agent.py` does with `curl`, which is worth seeing
once because it demystifies the whole thing.

**First, get the token** (it's stable for one run of the server):

```
TOKEN=$(curl -s http://localhost:8080/_ns/token \
        | python3 -c "import json,sys; print(json.load(sys.stdin)['token'])")
```

That fetches `{"token":"…"}` and pulls out the value into a shell variable.

**To send a message to the chat named `alpha`** — a `POST` with a JSON body,
the token in a header:

```
curl -s -X POST \
     -H "X-NS-Token: $TOKEN" \
     -d '{"to":"alpha","from":"claude-code","text":"What is 6*7?"}' \
     http://localhost:8080/_ns/bus
# → {"id": 3, "listeners": 1}
```

The reply `{"id":3,"listeners":1}` means the front door accepted the message,
gave it sequence number 3, and delivered it to 1 open subscriber (the IDE). Over
in the IDE, `alpha` now shows a `[from external agent 'claude-code']` turn and
answers it.

**To receive** — hold an SSE stream open and watch messages addressed to you
arrive. The token goes in the query string here (a streaming GET can't use a
header from a browser, so we keep it uniform):

```
curl -sN "http://localhost:8080/_ns/bus?token=$TOKEN"
```

This prints `: connected`, then a `data:` line for each message as it arrives,
and `: keepalive` every 20 seconds. Leave it running in one terminal; send from
another. (Because it filters nothing, you'll see all messages; `bus-agent.py`
filters to just yours.)

**Reconnecting without missing anything.** The front door keeps the last 200
messages. If your stream drops and you reconnect with a `Last-Event-ID` header
naming the last id you saw, it replays what you missed first, then resumes live:

```
curl -sN -H "Last-Event-ID: 3" "http://localhost:8080/_ns/bus?token=$TOKEN"
# replays messages with id > 3, then streams new ones
```

This is also how you can **retrieve a message that was sent before you were
listening** — subscribe with `Last-Event-ID: 0` to replay the whole backlog.

---

## 5. The chat-facing tools

Inside a chat, the AI has two messaging tools (and the system prompt explains
them):

- **`send_to_chat`** — message *another in-IDE chat* by its document name. Used
  for chat-to-chat conversation within the same browser. Delivery is the same
  visible-turn mechanism; the stamp reads `[from chat 'X']`.
- **`send_to_agent`** — message an *external agent* over the bus by name. This is
  the IDE→outside direction. To reply to a message it received stamped
  `[from external agent 'X']`, the chat calls `send_to_agent` addressed to `X`.

Both are **fire-and-forget**: the tool confirms the message was sent (or
queued), never waits for an answer. A reply, if any, arrives later as a new turn.
Both are visible in the transcript.

**Message vs notice.** A bus message's `kind` is `"message"` by default, which
drives a turn (the chat responds). Set `kind` to `"notice"` and instead the text
is folded into the chat's *next* turn as background context, with no turn of its
own — useful for "here's an update you should know about" that doesn't need an
immediate reply.

**Busy targets queue.** If a chat is mid-turn when a message for it arrives, the
message waits in a per-chat queue and is delivered when the current turn
finishes — so nothing is lost and turns stay ordered.

**Loop protection.** Chat-to-chat relays are depth-limited (a message relayed
too many hops is refused) and each turn may only send so many messages, so two
chats can't ping-pong forever and burn the API budget.

---

## 6. Level 2 — backing a whole chat with an external agent

Everything above is chats and agents *messaging* each other. There is a deeper
mode: a chat whose **entire brain** is an external agent, instead of a hosted
model like Claude.

Normally a chat's turns go to a model provider (Anthropic's API, say). But the
IDE's notion of a "provider" is really just a transport — "here is the
conversation and the available tools; give me the next reply." So we added a
provider whose transport is the **bus**: when you create a chat and pick the
**"Bus Agent"** provider (and type an agent's name where the model would go),
each turn the IDE sends the whole request — the conversation, the system prompt,
the list of tools — over the bus to that agent, and waits for its answer. The
agent *is* the model.

Two things make this powerful:

- **The agent can use the IDE's tools.** The request includes the tool list, and
  the agent-backed bridge (`bus-claude.py`) lets the agent call them (see the
  `TOOL_CALL` mechanism below): the IDE runs the tool against the live system and
  sends the result back to the agent, which then continues — exactly the loop a
  hosted model would drive, but with an outside agent in the driver's seat. This
  is genuine remote control of the IDE, and every step is a visible turn.
- **The agent can be a human.** Because it's just "here's the conversation,
  reply," a person can sit on the other end and answer — the chat can't tell the
  difference. A chat backed by a human is a Wizard-of-Oz chat.

**How to run it — human-backed (a person answers):**

1. Front door running with `--bus` (as always).
2. In a terminal, start the reference responder under a name:
   `python3 tool/bus-responder.py claude-code`
3. In the IDE, create a chat, choose the **Bus Agent** provider, and put
   `claude-code` in the model field.
4. Type a message in that chat. The responder terminal prints the request; type
   a reply there and it appears as the chat's answer. To make the chat run a
   tool, the responder answers with a raw tool-use response (`/json …` in
   `bus-responder.py`); the IDE runs the tool and sends the result back to the
   responder as the next request.

**How to run it — agent-backed (a headless Claude Code answers, unattended):**

For a chat backed by a *real agent* rather than a person, `tool/bus-claude.py`
is the autonomous responder: for each completion request it runs `claude -p`
(headless Claude Code) on the conversation and posts the reply. So the chat is
backed by a Claude Code agent — with its own host tools (shell, filesystem) and
reasoning loop — working inside the IDE, one visible turn at a time.

1. Front door running with `--bus`; `claude` on PATH and configured.
2. `python3 tool/bus-claude.py claude-code`
   (optionally `--claude-args "--permission-mode plan"` to constrain it, or
   `--cwd DIR` to set its working directory).
3. Create a Bus Agent chat with `claude-code` in the model field, and talk.

The agent has **two** sets of tools:

- **The IDE's own tools** (evaluate, inspect_object, get_stack_trace,
  propose_changes, …) — it can drive the live IDE. The request already lists
  them, and the bridge instructs the agent to call one by ending its reply with
  a line `TOOL_CALL: {"name": …, "input": …}`. The bridge turns that into a
  proper tool-use response, the IDE runs the tool against the live image and
  sends the result back, and the agent continues — the ordinary IDE tool loop,
  driven by an outside agent. (Why a text marker rather than "native" tool
  calls: a headless `claude -p` returns text, not the API's structured
  tool-use, so the bridge parses the marker. It's tolerant of code fences and
  stray prose, and falls back to treating the output as a plain answer.)
- **Its own Claude Code tools** (shell, file access) on the machine it runs on —
  for investigating the repo or reasoning. These act on the *files*, not the
  live IDE image.

**It is a real capability grant.** Because the backing agent can run
shell/filesystem commands, pointing a chat at it hands that chat an agent with
real reach on the host. Run it deliberately, on a trusted machine, over the
loopback bus; `--claude-args` can restrict it (e.g. `--permission-mode plan`).

The IDE raises a Bus Agent chat's request watchdog to 10 minutes (an agentic run
can take far longer than a hosted-model reply), so there is room for the agent
to work.

**Memory and caching.** `bus-claude.py` keeps one Claude Code *session* per chat:
the first turn records the session id `claude -p --output-format json` returns,
and every later turn uses `claude -p --resume <id>` and sends only the *new*
message. So the agent genuinely remembers the conversation (it isn't re-sent
each turn), Claude Code's session-level prompt caching applies across turns, and
prompts stay small. If a session is ever lost, the bridge falls back to a fresh
full run and re-captures the id. (A naive bridge that re-sent the whole
transcript every turn would still "remember," but as a cold start each time —
re-processing and re-billing the entire history with no cache reuse.)

**A turn that drives an IDE tool, step by step.** Say the user asks the bus chat
"what does `6 * 7` evaluate to in the image?":

1. The IDE (its `BusProvider`) posts a `completion_request` over the bus to the
   agent — the conversation, the system prompt, and the tool list (which
   includes `evaluate`) — tagged with a `corr_id`.
2. `bus-claude.py` runs `claude -p`; the agent decides to use the IDE's tool and
   ends its reply with `TOOL_CALL: {"name":"evaluate","input":{"expression":"6 * 7"}}`.
3. The bridge parses that into a tool-use response and posts it back
   (`stop_reason:"tool_use"`) with the same `corr_id`.
4. The IDE runs `evaluate` against the live image, gets `42`, and posts the next
   `completion_request` whose last message is the tool result.
5. The bridge resumes the agent's session with just that result; the agent
   replies in plain text, "…it returned 42," which appears as the chat's answer.

Every one of those is a visible turn in the chat, and the whole exchange is one
Claude Code session on the agent side, so it remembers its own reasoning across
the tool round-trip.

**Under the hood.** The wire format is deliberately Anthropic's Messages API
shape — a request `{model, max_tokens, system, messages, tools}` and a response
`{content: […blocks…], stop_reason}`. That let the IDE side be tiny: the bus
provider *inherits* all the message-and-tool machinery from the normal Anthropic
provider and overrides only the send step. It also means an agent that is itself
a Claude can answer almost verbatim. Requests and replies are matched by a
correlation id (`corr_id`) carried on the bus message, and a `completion_request`
/ `completion_response` `kind` distinguishes them from ordinary chat messages.

## 7. The security model

The bus is remote control of a system that runs code, so its safety rests on
three things, all deliberate:

1. **Opt-in.** It does nothing unless the front door is started with `--bus`.
   A default front door has no bus at all.
2. **Loopback only (by default).** The front door binds to `localhost`, so only
   programs on your own machine can reach it. (`--bind 0.0.0.0` opens it to your
   local network — needed for cross-device work — but then anyone on that
   network who has the token could send; use it knowingly.) The token endpoint
   answers only to `localhost` regardless.
3. **A token.** Every bus request needs the per-run secret, fetched from
   `/_ns/token` (which only your own machine can read).

And one property that isn't a gate but matters: **every delivered message is a
visible turn.** There is no hidden channel — the human at the IDE sees each
message an external agent sends and each reply, so the whole exchange is an audit
trail, not a back door.

**Level 2 raises the stakes**, and deserves its own caution. Backing a chat with
an agent (`bus-claude.py`) hands that chat an agent that can run shell and
filesystem commands *on the machine the bridge runs on*, and — via `TOOL_CALL` —
drive the IDE's own tools against the live image. That is a real, compound
capability grant. The same three gates apply (opt-in, loopback, token), plus:
run the bridge only on a machine you trust, constrain it with `--claude-args`
(e.g. `--permission-mode plan` to keep it from acting without review), and
remember that whoever can post to the bus can pose as the chat asking the agent
to act. Point a chat at an agent deliberately, not casually.

---

## 8. Troubleshooting

- **`{"listeners": 0}` when you POST** — nobody is subscribed under any name, so
  no one (not even the IDE) is currently listening. Check the IDE is open on this
  front door, or that your agent's `curl -sN`/`bus-agent.py` is running.
- **A message went to the right name but nothing happened** — the *name* being
  right isn't enough; something must be *subscribed* under it. A message sent to
  a name nobody is listening for is delivered to zero matching handlers. You can
  still recover it from the backlog (`Last-Event-ID: 0`).
- **The reply never comes** — replies are fire-and-forget and depend on the other
  side choosing to answer; there's no delivery receipt. If it's a chat, make sure
  its turn actually ran (the IDE must be open and the chat not stuck).
- **Watching a stream from the terminal shows nothing** — on macOS there is no
  `timeout` command, so `timeout 30 curl …` fails instantly and captures nothing
  (it looks like an empty bus, but it's the shell). Use a plain
  `curl -sN … &` in the background and stop it with `kill`, or install coreutils'
  `gtimeout`. Plain `curl -sN` (foreground, Ctrl-C to stop) is simplest.

Level 2 (Bus Agent chats):

- **A Bus Agent chat says the request timed out** — nothing was subscribed under
  the agent name when you sent the turn, or the agent took longer than the
  10-minute watchdog. Make sure `bus-claude.py`/`bus-responder.py` is running
  under exactly the name in the chat's Model field before you send.
- **The chat won't create — "enter the external agent's name"** — for a Bus
  Agent chat the Model field holds the agent's bus name (there is no API key);
  fill it in.
- **The agent answered in prose instead of running an IDE tool** — the
  `TOOL_CALL` line is a text convention, not enforced; a model may skip it or
  mis-emit it. The bridge falls back to treating the output as a plain answer.
  If reliable IDE-tool driving matters more than the agent's own host tools, a
  plain-model backend (native, validated tool calls) is the sturdier choice for
  that job (see §6, "Why a text marker…").
- **The agent seems to have forgotten earlier turns** — its Claude Code session
  was lost (e.g. the bridge restarted), so `--resume` failed and it fell back to
  a fresh session. The conversation continues (the bridge re-sends full context
  on a fresh start), but prior in-session reasoning is gone.

---

## 9. Where the code lives

- `tool/cors-proxy.py` — the front door, including the `/_ns/bus` router (SSE
  stream, POST, fan-out, backlog).
- `tool/bus-agent.py` — the reference external agent (messaging).
- `tool/bus-responder.py` — the reference *human-backed* responder for a
  Bus-Agent-backed chat (Level 2, §6).
- `tool/bus-claude.py` — the reference *agent-backed* responder: answers each
  turn with a headless `claude -p` run (§6).
- `AIAccess.ns` — `BusProvider` (the bus-transport provider) and the rest of the
  provider/session machinery.
- `AI_IDE_Support.ns` — the IDE side: subscribing at startup
  (`startAgentBusListening`), delivering incoming messages into chats, and the
  `send_to_chat` / `send_to_agent` tools.
- `HopscotchWebIDE.ns` — the one line that starts the subscription after launch.
- `HOST_SERVICES_DESIGN_2026-08-31.md` — the design rationale and the wider host
  services of which the bus is one part.
