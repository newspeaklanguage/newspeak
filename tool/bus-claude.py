#!/usr/bin/env python3
"""Back an in-IDE Bus Agent chat with a headless Claude Code agent — with memory.

The autonomous version of bus-responder.py: each completion request from a Bus
Agent chat is answered by a headless `claude -p` run, and its reply is posted
back over the bus. So a bus-backed chat becomes a real agent — its own host
tools (shell, filesystem) and reasoning loop — working inside the IDE, one
visible turn at a time.

MEMORY / CACHING. A naive bridge would flatten the whole transcript into a fresh
`claude -p` each turn: the agent never forgets (the history is re-sent) but
every turn is a cold start, re-processing and re-billing the entire history with
no prompt-cache reuse. This bridge instead keeps a Claude Code SESSION per chat:
the first turn runs `claude -p --output-format json` and records the returned
session_id; every later turn runs `claude -p --resume <session_id>` and feeds
ONLY the new user message. Claude Code then retains the conversation and its
session-level prompt caching applies across turns, and the prompts shrink to
deltas. If a resume fails (a lost/expired session), the bridge falls back to a
fresh full run and re-captures the id.

WHAT IT DOES AND DOESN'T. The agent answers in TEXT, using its OWN Claude Code
tools while it thinks. It does not yet directly drive the IDE's tools
(evaluate/inspect/debugger) — that needs a tool-call protocol layered on this
(future work). And because it can run shell/filesystem commands on the machine
it runs on, pointing a chat at it is a real capability grant: run it
deliberately, on a trusted machine, over the loopback bus. `--claude-args` can
constrain it.

BUDGETS. Neither side puts a clock on a turn that is visibly working. The IDE
gives a Bus Agent chat a 10-minute watchdog of SILENCE, re-armed by every
heartbeat this bridge posts; the bridge kills a run only after IDLE_S with
nothing on its stream, or at --hard-cap, which exists for a runaway rather than
for a long job. So an agentic run has as long as it takes, provided it keeps
saying what it is doing.

Usage (front door running with --bus, and `claude` on PATH and configured):
    python3 tool/bus-claude.py <agent-name> [--origin http://localhost:8080]
                               [--cwd DIR] [--claude-bin claude]
                               [--claude-args "--permission-mode plan"]
                               [--hard-cap SECONDS]

Create a Bus Agent chat in the IDE whose Model field is <agent-name>, and talk.
"""

import argparse
import atexit
import json
import os
import queue
import re
import shlex
import signal
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid


# The bridge kills a run for ONE reason: silence. The IDE side is built the
# same way - AIAccess withWatchdog:ms:reason: re-arms rather than rejecting
# whenever a completion_progress frame has pushed its deadline out
# (deliverCompletionProgress: -> noteProviderProgress:), so a bus chat only
# times out when the bridge stops speaking, however long the turn takes.
#
# Silence here means no line on the `claude -p` stream. With
# --include-partial-messages generation itself streams, so the only silence
# left is a tool call in flight; the harness caps one tool call at 600s, so a
# longer silence really is a hang. IDLE_S is that 600 plus margin. The
# heartbeat the bridge posts every TOOL_HEARTBEAT_S does NOT reset it: the
# bridge's own clock is no evidence that the agent is alive. It exists so the
# IDE's watchdog and the user know the turn is working.
#
# There used to be a second budget of the same quantity, TURN_BUDGET_S = 540.
# Being the smaller it always won, so IDLE_S was unreachable and any turn whose
# agent made one long tool call died at nine minutes - short of the 600s the
# harness allows a single call, so ordinary work was over budget by
# construction (found and removed 2026-09-19).
IDLE_S = 900
TOOL_HEARTBEAT_S = 60
# The absolute cap on one answer, retry included: the only limit a live,
# streaming agent can still reach, and the only guard against a runaway loop
# burning the monthly limit with nobody watching. Set by --hard-cap, which
# takes 0 to remove it. MIN_RUN_S: with less than this much of the cap left
# there is no point starting a run at all.
HARD_CAP_S = 3600
MIN_RUN_S = 45


def hard_deadline_from(args):
    """The absolute cap as a monotonic instant; infinite if --hard-cap 0."""
    return time.monotonic() + args.hard_cap if args.hard_cap > 0 else float('inf')


# Runs in flight, so that quitting the bridge does not leave agents behind.
_LIVE = set()
_LIVE_LOCK = threading.Lock()


def kill_tree(proc):
    """Kill a run AND everything it started, then reap it.

    Killing only `claude` leaves its children - the shell it spawned, and
    whatever that spawned - running, holding files, ports and CPU with nothing
    left to answer to. It is the common case rather than a corner: the kill
    happens because a tool call is hanging, so there is always a child, and a
    killed probe turn has been observed keeping port 8098 to itself
    afterwards. Each run therefore gets a session of its own (start_new_session
    below) and the whole group is signalled here."""
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    except OSError:
        try:
            proc.kill()
        except OSError:
            pass
    try:
        proc.wait(timeout=5)        # reap: a killed turn leaves no zombie
    except Exception:
        pass
    with _LIVE_LOCK:
        _LIVE.discard(proc)


def kill_live_runs(*_signal_args):
    """Every run still going, on the way out. A run is in its own session, so
    it does NOT get the Ctrl-C that reaches the bridge; without this, quitting
    would strand one agent per chat mid-turn."""
    with _LIVE_LOCK:
        procs = list(_LIVE)
    for proc in procs:
        kill_tree(proc)
    if procs:
        print(f'[killed {len(procs)} run(s) still in flight]', file=sys.stderr, flush=True)


def fetch_token(origin):
    with urllib.request.urlopen(origin + '/_ns/token', timeout=5) as r:
        return json.load(r)['token']


def fetch_config(origin):
    with urllib.request.urlopen(origin + '/_ns/config', timeout=5) as r:
        return json.load(r)


# The bridge reports on itself, as the front door does (cors-proxy.py,
# process_status): a bridge started before this file was last edited keeps
# taking requests, runs the old code, and nothing says so - the fault shows up
# as a turn that misbehaves in some older way. Checked before every request it
# takes, so the warning lands beside the turn it affects; and at startup the
# front door's own 'stale' bit is checked, since a bridge attached to a stale
# door is stale by proxy.
SOURCE = os.path.abspath(__file__)
SOURCE_MTIME_AT_START = os.path.getmtime(SOURCE)
_STALE_REPORTED = [False]


def warn_if_stale():
    try:
        now_mtime = os.path.getmtime(SOURCE)
    except OSError:
        now_mtime = None
    if now_mtime == SOURCE_MTIME_AT_START or _STALE_REPORTED[0]:
        return
    _STALE_REPORTED[0] = True
    print(f'WARNING: {SOURCE} changed on disk since this bridge started; it is running '
          f'the OLD code. Restart it (the chat keeps its session: --resume is per chat).',
          file=sys.stderr, flush=True)


def refuse_stale_front_door(origin):
    """Exit if the front door reports that its own source changed after it
    started. An older door (no 'process' block) is not refused: it predates
    the check, and the launcher's other preflights already cover it."""
    try:
        process = fetch_config(origin).get('process') or {}
    except Exception:
        return
    if process.get('stale'):
        sys.exit(f'error: the front door at {origin} is STALE - it started '
                 f'{process.get("started")} running {process.get("source")}, which has '
                 f'changed on disk since. Restart it (python3 tool/cors-proxy.py --bus), '
                 f'reload the IDE page, then start this bridge again.')


def post(origin, token, obj, attempts=3):
    """POST a bus message, retrying a transient failure.

    Worth retrying because the alternative is silence: the IDE is holding a
    watchdog open on this corr_id and has no other way to learn the answer
    never came, so a dropped post costs the chat its full 10-minute budget
    and then kills the turn."""
    data = json.dumps(obj).encode('utf-8')
    req = urllib.request.Request(
        origin + '/_ns/bus', data=data, method='POST',
        headers={'Content-Type': 'application/json', 'X-NS-Token': token})
    for attempt in range(attempts):
        try:
            with urllib.request.urlopen(req, timeout=10) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            # The front door refused the message itself (oversized, bad token).
            # Retrying replays the same refusal, so fail fast and let the
            # caller send something smaller.
            raise RuntimeError('the bus refused the message: %s %s'
                               % (e.code, e.reason)) from e
        except Exception:
            if attempt == attempts - 1:
                raise
            time.sleep(2 ** attempt)


def system_text(system):
    if isinstance(system, str):
        return system
    if isinstance(system, list):                       # Anthropic system blocks
        return '\n'.join(b.get('text', '') for b in system if isinstance(b, dict))
    return ''


# First line of the paragraph Session>>noticesText: (AIAccess.ns) appends to the
# system prompt when a turn carries one-shot notices: "the codebase changed",
# "the user applied your changeset via the Apply button", messages from
# external agents. It is always the LAST thing in the system string.
NOTICES_MARKER = 'IMPORTANT — out-of-band updates since your last turn:'


def notices_text(request):
    """The IDE's out-of-band notices for this turn, or ''.

    The IDE folds them onto the end of the request's system prompt, which works
    for a hosted model that re-reads the system prompt every turn. A resumed
    `claude` session does not: it only sees the delta we send, so until this
    was pulled out and delivered with the delta, an agent whose changeset the
    user applied from the IDE never learned it had gone live."""
    sys_text = system_text(request.get('system'))
    i = sys_text.rfind(NOTICES_MARKER)
    return sys_text[i:].strip() if i >= 0 else ''


def block_text(content):
    """Flatten one message's content to readable text, noting tool traffic."""
    if isinstance(content, str):
        return content
    if not isinstance(content, list):
        return ''
    out = []
    for b in content:
        t = b.get('type')
        if t == 'text':
            out.append(b.get('text', ''))
        elif t == 'tool_use':
            out.append(f'[called tool {b.get("name")} with {json.dumps(b.get("input", {}))}]')
        elif t == 'tool_result':
            inner = b.get('content')
            out.append('[tool result: ' + (inner if isinstance(inner, str) else json.dumps(inner)) + ']')
    return '\n'.join(out)


PREAMBLE = """\
You are the model behind one chat session in the Newspeak Web IDE. Answer as
that chat's assistant.

You have TWO sets of tools:

1. THE IDE'S OWN TOOLS — listed in the chat's system instructions below (e.g.
   evaluate, inspect_object, get_class_source, get_stack_trace, propose_changes,
   …). These act on the LIVE IDE image the user is looking at. To call one,
   make the LAST thing in your reply a single line:

       TOOL_CALL: {"name": "<exact tool name>", "input": { … arguments … }}

   Output at most ONE TOOL_CALL, as the final line. You may write a sentence of
   reasoning before it. After you emit a TOOL_CALL your turn ends; the IDE runs
   the tool and sends you the result as your next message, and you continue
   (another TOOL_CALL, or a final plain-text answer). Use these whenever the
   user asks about their live system — inspect it, don't guess.

2. YOUR OWN Claude Code tools (shell, file access) on this machine — use them to
   investigate the repository or reason, but note they act on the FILES, not the
   live IDE image. Honor the repo's working rules (CLAUDE.md: pretty-print +
   round-trip + parse-validate every .ns you change, run tests, never commit).
   Prefer explaining and proposing over changing state unless asked.

When you are done and just answering the user, reply in plain text with NO
TOOL_CALL line.

Below are the chat's own system instructions and the conversation so far.

--- The chat's system instructions ---
"""


def killed_notice(reason, cold=False):
    """What to tell an agent whose previous turn this bridge killed.

    Two shapes, because the two situations differ in what the agent still
    knows. A RESUMED session remembers the work it was in the middle of, and
    nothing else tells it that none of that reached the user. A COLD one
    remembers nothing - but it is handed a transcript ending at the same user
    message, so left unwarned it walks straight back into the step that killed
    the last attempt, which is how a chat dies the same death twice."""
    if cold:
        return ('[Notice from the bridge] The previous attempt to answer this was '
                'KILLED: ' + reason + '. It ran in a session that is now gone, so '
                'nothing from it reached the user and none of its context is available '
                'to you. Do not just retry the same long step: reply with a short text '
                'status first, and do any long step alone in a later turn.')
    return ('[Notice from the bridge] Your previous turn was KILLED: ' + reason +
            '. Nothing you did or wrote in it reached the user. Do not silently '
            'resume that work: reply with a short text status first, and do any '
            'long step alone in a later turn.')


def first_prompt(request, killed=None):
    """Full context for turn 1: preamble + the chat's system prompt + the
    conversation so far. This becomes the resumed session's cached prefix.

    `killed`: see killed_notice. A cold run is not only the chat's first turn -
    it is also what a bridge restart and a lost session produce, and either can
    follow a turn this bridge killed. Until this argument existed the reason
    was popped and dropped on exactly those paths."""
    parts = [PREAMBLE + system_text(request.get('system'))]
    parts.append('\n--- Conversation so far ---')
    for m in request.get('messages', []):
        who = 'User' if m.get('role') == 'user' else 'Assistant'
        parts.append(f'{who}: {block_text(m.get("content"))}')
    if killed:
        # Last, so it is the freshest thing before the agent starts writing.
        parts.append('\n' + killed_notice(killed, cold=True))
    parts.append('\nAssistant:')
    return '\n'.join(parts)


def delta_prompt(request, killed=None):
    """For a resumed turn: only the newest message (the session already holds
    everything before it). Usually the user's new input; after a TOOL_CALL it is
    the IDE's tool result, which we frame so the agent knows to continue.

    `killed`: the reason the chat's previous turn died in this bridge, if it
    did. The resumed session remembers the work it was in the middle of and
    nothing else tells it that none of that reached the user; left alone it
    picks the same long work up again and dies again, turn after turn, until
    the chat is abandoned (2026-09-16)."""
    messages = request.get('messages') or []
    # Notices ride the system prompt, which a resumed session never re-reads;
    # lead the delta with them so they are not lost. Framed as coming from the
    # IDE: they are not the user speaking.
    notices = notices_text(request)
    prefix = ('[Notices from the IDE, delivered with this turn]\n' + notices + '\n\n'
              if notices else '')
    if killed:
        prefix = killed_notice(killed) + '\n\n' + prefix
    if not messages:
        return prefix + '(no new message)'
    last = messages[-1]
    content = last.get('content')
    if isinstance(content, list) and any(
            isinstance(b, dict) and b.get('type') == 'tool_result' for b in content):
        return (prefix + 'The IDE ran your tool call. Result:\n\n' + block_text(content) +
                '\n\nContinue: either make another TOOL_CALL, or give your final '
                'answer as plain text.')
    return prefix + block_text(content)


def extract_first_json(s):
    """The first balanced {...} object in s, or None."""
    start = s.find('{')
    if start < 0:
        return None
    depth, in_str, esc = 0, False, False
    for i in range(start, len(s)):
        c = s[i]
        if in_str:
            if esc:
                esc = False
            elif c == '\\':
                esc = True
            elif c == '"':
                in_str = False
        else:
            if c == '"':
                in_str = True
            elif c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
                if depth == 0:
                    return s[start:i + 1]
    return None


TOOL_CALL_MARKER = re.compile(r'^[ \t`]*TOOL_CALL:', re.MULTILINE)


def parse_tool_call(text):
    """If the agent's output ends in a TOOL_CALL, return (call, before_text)
    where call = {name, input}; else (None, None). Tolerant of code fences and
    a leading 'json' language tag after the marker.

    Only a marker at the START of a line counts, and candidates are tried from
    the last one backwards until one parses. A plain reverse search for the
    marker text is not enough: the tool call's own JSON payload may contain the
    literal 'TOOL_CALL:' (e.g. a document about this very protocol), and the
    search would land inside the payload and fail to parse. The payload is a
    single JSON line, so any marker text inside it is never at a line start."""
    for m in reversed(list(TOOL_CALL_MARKER.finditer(text))):
        before = text[:m.start()].strip().strip('`').strip()
        after = text[m.end():].strip()
        after = after.strip('`').strip()
        if after.lower().startswith('json'):
            after = after[4:].strip()
        obj_str = extract_first_json(after)
        if obj_str is None:
            continue
        try:
            obj = json.loads(obj_str)
        except ValueError:
            continue
        name = obj.get('name')
        if not isinstance(name, str) or not name:
            continue
        return {'name': name, 'input': obj.get('input') or {}}, before
    return None, None


def response_from_agent_text(text):
    """Turn `claude -p`'s text into an Anthropic-style response object: a
    tool_use response if it ends in a TOOL_CALL, otherwise a plain-text turn."""
    call, before = parse_tool_call(text)
    if call is None:
        return {'content': [{'type': 'text', 'text': text or '(the agent produced no text)'}],
                'stop_reason': 'end_turn'}
    content = []
    if before:
        content.append({'type': 'text', 'text': before})
    content.append({'type': 'tool_use', 'id': 'call_' + uuid.uuid4().hex[:16],
                    'name': call['name'], 'input': call['input']})
    return {'content': content, 'stop_reason': 'tool_use'}


# Whether `claude -p` takes its prompt on stdin. Probed once, on the first run
# that produces nothing from a non-empty stdin prompt; see run_claude.
_STDIN_PROMPT = [True]


class SessionGone(RuntimeError):
    """A resume failed because the session id is no longer usable — the one
    case where re-running the whole transcript cold is the right answer."""


_SESSION_GONE = re.compile(
    r'no conversation found|session .*not found|no such session|invalid session',
    re.IGNORECASE)


def run_claude(prompt, args, resume_session=None, hard_deadline=None, progress=None):
    """One `claude -p` run, streamed. Returns (result_text, session_id).

    The run is watched line by line (--output-format stream-json, with partial
    messages so generation streams too) rather than waited for as a whole, for
    two reasons. First, HEARTBEAT: every tool call the agent makes is reported
    through `progress` while the run is still going, and the bridge posts each
    one to the chat as a completion_progress frame, so the IDE can restart its
    watchdog and show the user what the agent is doing instead of silence; a
    call still running after TOOL_HEARTBEAT_S gets a heartbeat of its own.
    Second, the only budget is one of SILENCE: a run is killed once IDLE_S has
    passed since the last line - a hung tool is the common failure, and it
    looks exactly like thinking - under `hard_deadline` (the absolute cap for
    the whole answer, retry included; --hard-cap from now by default)."""
    cmd = [args.claude_bin, '-p', '--output-format', 'stream-json', '--verbose',
           '--include-partial-messages']
    if resume_session:
        cmd += ['--resume', resume_session]
    if args.claude_args:
        cmd += shlex.split(args.claude_args)

    def run(on_stdin):
        # The prompt goes on stdin rather than argv. A resumed turn is a small
        # delta, but a cold turn carries the whole transcript plus its tool
        # results - each of which the front door lets run to 256 KB - and macOS
        # caps a process's arguments plus environment at ~1 MB. Past that the
        # exec fails with E2BIG and the chat sees a bare bridge error, at
        # exactly the moment the history is most worth having.
        proc = subprocess.Popen(
            cmd if on_stdin else cmd + [prompt],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            cwd=args.cwd, text=True, start_new_session=True)
        with _LIVE_LOCK:
            _LIVE.add(proc)
        lines, errs = queue.Queue(), []

        def pump(stream, sink):
            try:
                for line in stream:
                    sink(line)
            except Exception:
                pass
            sink(None)
        threading.Thread(target=pump, args=(proc.stdout, lines.put), daemon=True).start()
        threading.Thread(target=pump, args=(proc.stderr, lambda l: l is not None and errs.append(l)),
                         daemon=True).start()
        try:
            proc.stdin.write(prompt if on_stdin else '')
            proc.stdin.close()
        except Exception:
            pass
        hard = hard_deadline if hard_deadline is not None else hard_deadline_from(args)
        last_seen = time.monotonic()
        deadline = min(last_seen + IDLE_S, hard)
        result, sid, is_error, saw_output = None, None, False, False
        in_flight = None        # the tool call the agent is waiting on, if any
        last_beat = last_seen

        def beat(text):
            # The IDE's watchdog is pushed out by our frames and by nothing
            # else, so the rule is about OUR silence, not the agent's: a frame
            # at least every TOOL_HEARTBEAT_S whatever the agent is doing.
            # Heartbeating only when the stream went quiet was not enough - an
            # agent generating steadily for the IDE's whole budget kept this
            # loop fed while the IDE heard nothing and abandoned the turn, and
            # the answer then came back to a corr_id no longer pending.
            nonlocal last_beat
            last_beat = time.monotonic()
            if progress:
                progress(text)

        while True:
            now = time.monotonic()
            if now >= deadline:
                # Which of the two it was matters to the reader: one says the
                # agent wedged, the other says it worked for an hour.
                kill_tree(proc)
                if now >= hard:
                    raise RuntimeError('claude was still going at the absolute cap of %ds '
                                       'for one answer; killed (raise or remove it with '
                                       '--hard-cap)' % args.hard_cap)
                raise RuntimeError('claude produced no output for %ds (stuck?); killed' % IDLE_S)
            wait = min(TOOL_HEARTBEAT_S, deadline - now)
            try:
                line = lines.get(timeout=max(wait, 0.1))
            except queue.Empty:
                now = time.monotonic()
                # Alive but silent: a tool call in progress. Say so, so the
                # IDE's watchdog is pushed out and the user sees it is working.
                beat('still %s (%ds)' % (('running ' + in_flight) if in_flight else 'working',
                                         int(now - last_seen)))
                continue
            if line is None:
                break
            line = line.strip()
            if not line:
                continue
            saw_output = True
            last_seen = time.monotonic()
            deadline = min(last_seen + IDLE_S, hard)
            try:
                ev = json.loads(line)
            except ValueError:
                # Some builds print plain text even when asked for JSON; keep
                # the last such line as the result.
                result = line
                continue
            t = ev.get('type')
            if t == 'assistant':
                for b in (ev.get('message') or {}).get('content') or []:
                    if isinstance(b, dict) and b.get('type') == 'tool_use':
                        in_flight = b.get('name') or 'a tool'
                        beat(tool_call_summary(b))
            elif t == 'user':
                # The tool result came back; the agent is generating again.
                in_flight = None
            elif t == 'result':
                result = str(ev.get('result', '') or '')
                sid = ev.get('session_id')
                is_error = bool(ev.get('is_error'))
            if last_seen - last_beat >= TOOL_HEARTBEAT_S:
                # Streaming steadily, and nothing above has spoken for a while:
                # the stream keeps US alive but says nothing to the IDE.
                beat('still %s' % (('running ' + in_flight) if in_flight else 'generating'))
        proc.wait()
        with _LIVE_LOCK:
            _LIVE.discard(proc)
        return proc.returncode, result, sid, is_error, ''.join(errs), saw_output

    rc, result, sid, is_error, stderr, saw_output = run(_STDIN_PROMPT[0])
    if _STDIN_PROMPT[0] and prompt and rc == 0 and not saw_output:
        # A build that ignores stdin sees an empty prompt and succeeds at
        # saying nothing. That exact shape - clean exit, no output - is what
        # distinguishes it from a real failure, which reports on stderr and is
        # passed through below rather than retried.
        print('  [this claude build did not read the prompt from stdin; '
              'using argv (large prompts may fail)]', file=sys.stderr, flush=True)
        _STDIN_PROMPT[0] = False
        rc, result, sid, is_error, stderr, saw_output = run(False)

    if rc != 0 or is_error:
        detail = (stderr or result or 'claude exited nonzero').strip()[:500]
        if resume_session and _SESSION_GONE.search(detail):
            raise SessionGone(detail)
        raise RuntimeError(detail)
    return (result or '').strip(), sid


def tool_call_summary(block):
    """One line naming what the agent is doing, for the chat's status line:
    the tool and, where the tool supplies one, its own description of the
    call (Bash's `description`), else a short slice of the input."""
    name = block.get('name') or 'tool'
    inp = block.get('input') or {}
    if isinstance(inp, dict):
        text = inp.get('description') or inp.get('command') or inp.get('file_path') \
            or inp.get('pattern') or inp.get('prompt') or ''
    else:
        text = ''
    text = str(text).replace('\n', ' ').strip()
    return name + (': ' + text[:100] if text else '')


class Bridge:
    def __init__(self, origin, token, name, args):
        self.origin, self.token, self.name, self.args = origin, token, name, args
        self.sessions = {}          # chat name -> claude session_id
        self.killed = {}            # chat name -> why its last turn died here, until told
        self.lock = threading.Lock()

    def reply_for(self, request, chat, progress=None):
        """Run the agent and return an Anthropic-style response object (a text
        turn, or a tool_use turn if the agent asked to call an IDE tool)."""
        with self.lock:
            sid = self.sessions.get(chat)
            killed = self.killed.pop(chat, None)
        # The absolute cap for the whole answer, retry included; the silence
        # budget (IDLE_S) restarts with every sign of life under it.
        hard = hard_deadline_from(self.args)

        def remaining():
            return hard - time.monotonic()      # inf when --hard-cap 0

        if sid is None:
            text, new_sid = run_claude(first_prompt(request, killed=killed), self.args,
                                       hard_deadline=hard, progress=progress)
        else:
            try:
                text, new_sid = run_claude(delta_prompt(request, killed=killed), self.args,
                                           resume_session=sid, hard_deadline=hard,
                                           progress=progress)
            except SessionGone as e:
                # Only a dead session earns a cold re-run. A run that timed out
                # or crashed is reported as-is: re-running the whole transcript
                # would double the wait for the same failure, and the IDE's
                # watchdog would have expired long before it finished.
                if remaining() < MIN_RUN_S:
                    raise RuntimeError(
                        f'the session was gone ({e}) and there was no time left '
                        f'in this turn to start a fresh one') from e
                print(f'  [session {sid} is gone ({e}); starting a fresh session]', flush=True)
                text, new_sid = run_claude(first_prompt(request, killed=killed), self.args,
                                           hard_deadline=hard, progress=progress)
        if new_sid:
            with self.lock:
                self.sessions[chat] = new_sid
        return response_from_agent_text(text)

    def answer(self, msg):
        chat, corr_id = msg.get('from', '?'), msg.get('corr_id')

        def progress(summary):
            # Heartbeat: one frame per tool call the agent makes, on the same
            # corr_id as the pending request, so the IDE can restart the turn's
            # watchdog and show the user what is happening. Best effort: a lost
            # heartbeat costs nothing the answer will not make good.
            try:
                post(self.origin, self.token, {
                    'to': chat, 'from': self.name, 'kind': 'completion_progress',
                    'corr_id': corr_id, 'text': summary}, attempts=1)
                print(f'  [progress {corr_id}: {summary[:70]}]', flush=True)
            except Exception as e:
                print(f'  [progress frame for {corr_id} not posted: {e}]', file=sys.stderr, flush=True)
        try:
            response = self.reply_for(msg.get('request', {}), chat, progress=progress)
        except Exception as e:
            response = {'content': [{'type': 'text', 'text': f'[bus-claude bridge error: {e}]'}],
                        'stop_reason': 'end_turn'}
            # Told to the resumed session at its next turn (delta_prompt),
            # so it does not pick the dead turn's work up as if it had landed.
            with self.lock:
                self.killed[chat] = str(e)[:200]

        def send(payload):
            post(self.origin, self.token, {
                'to': chat, 'from': self.name, 'kind': 'completion_response',
                'corr_id': corr_id, 'response': payload,
            })

        try:
            send(response)
            kind = response.get('stop_reason')
            summary = next((b.get('name') if b.get('type') == 'tool_use' else b.get('text', '')
                            for b in response.get('content', [])), '')
            print(f'  [answered {corr_id} for chat {chat!r} ({kind}): {str(summary)[:70]!r}…]',
                  flush=True)
        except Exception as e:
            # The answer could not be delivered — most likely too large for the
            # bus (the front door caps a message at 256 KB). Say so in a message
            # small enough to get through, rather than leaving the chat to sit
            # out its watchdog knowing nothing.
            print(f'  [failed to post answer for {corr_id}: {e}]', file=sys.stderr, flush=True)
            try:
                send({'content': [{'type': 'text', 'text':
                                   f'[bus-claude produced an answer but could not deliver it: {e}. '
                                   f'It may have been too large for the bus; ask for a shorter one.]'}],
                      'stop_reason': 'end_turn'})
            except Exception as e2:
                print(f'  [and the failure notice for {corr_id} did not post either: {e2}]',
                      file=sys.stderr, flush=True)

    def receive_loop(self):
        while True:
            # The token is re-read on every reconnect, not captured once. The
            # front door mints a fresh token per run, so after it restarts the
            # old one is refused - and without this the bridge would spin on
            # 403 forever while appearing to be up, which is the least useful
            # way for it to be down.
    # Declare our name on the stream so the front door can answer
    # /_ns/bus/agents. The bus is per-machine, and a collaborating IDE
    # session needs to know WHICH participant can reach this agent.
            url = self.origin + '/_ns/bus?token=' + self.token + '&name=' + urllib.parse.quote(self.name)
            req = urllib.request.Request(url, headers={'Accept': 'text/event-stream'})
            try:
                with urllib.request.urlopen(req, timeout=None) as stream:
                    for raw in stream:
                        line = raw.decode('utf-8', 'replace').rstrip('\n')
                        if not line.startswith('data: '):
                            continue
                        try:
                            msg = json.loads(line[len('data: '):])
                        except ValueError:
                            continue
                        if msg.get('to') != self.name or msg.get('kind') != 'completion_request':
                            continue
                        print(f'» completion request from chat {msg.get("from")!r} '
                              f'(corr {msg.get("corr_id")}) — running claude…', flush=True)
                        warn_if_stale()
                        # One thread per request so a slow run doesn't stall
                        # the stream. Safe because the IDE serializes turns per
                        # chat - confirmed by Gilad, 2026-09-19 - so a given
                        # chat's session id is never touched concurrently, and
                        # two runs never --resume the same session.
                        threading.Thread(target=self.answer, args=(msg,), daemon=True).start()
            except Exception as e:
                print(f'[stream dropped: {e}; reconnecting]', file=sys.stderr, flush=True)
                time.sleep(1)
                try:
                    self.token = fetch_token(self.origin)
                except Exception as e2:
                    print(f'[the front door is not answering ({e2}); will keep trying]',
                          file=sys.stderr, flush=True)
                    time.sleep(4)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name', help="this agent's bus name (the chat's Model field)")
    ap.add_argument('--origin', default='http://localhost:8080')
    ap.add_argument('--cwd', default=None, help='working directory for claude runs')
    ap.add_argument('--claude-bin', default='claude')
    ap.add_argument('--claude-args', default='',
                    help='extra args passed to claude, e.g. "--permission-mode plan"')
    ap.add_argument('--hard-cap', type=int, default=HARD_CAP_S, metavar='SECONDS',
                    help='absolute limit on one answer, however alive the agent is '
                         '(default %(default)s, 0 for none). Silence is bounded separately '
                         f'and always, at {IDLE_S}s.')
    args = ap.parse_args()

    # A run outlives a plain Ctrl-C now that each one has its own session, so
    # the bridge takes responsibility for ending them. SIGTERM does not run
    # atexit handlers by itself, hence the explicit handler.
    atexit.register(kill_live_runs)
    signal.signal(signal.SIGTERM, lambda *a: sys.exit(0))

    refuse_stale_front_door(args.origin)
    token = fetch_token(args.origin)
    print(f'bus-claude {args.name!r} on {args.origin} — backing any Bus Agent chat '
          f'whose Model is {args.name!r} (one Claude Code session per chat). Ctrl-C to quit.',
          flush=True)
    Bridge(args.origin, token, args.name, args).receive_loop()


if __name__ == '__main__':
    main()
