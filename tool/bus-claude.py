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

The IDE raises a Bus Agent chat's request watchdog to 10 minutes, so an agentic
run has room.

Usage (front door running with --bus, and `claude` on PATH and configured):
    python3 tool/bus-claude.py <agent-name> [--origin http://localhost:8080]
                               [--cwd DIR] [--claude-bin claude]
                               [--claude-args "--permission-mode plan"]

Create a Bus Agent chat in the IDE whose Model field is <agent-name>, and talk.
"""

import argparse
import json
import re
import shlex
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid


# The IDE gives a Bus Agent chat a 10-minute request watchdog. Everything the
# bridge does for one request has to fit inside that, or the answer arrives
# against a corr_id the IDE has already abandoned. TURN_BUDGET_S is the budget
# for the WHOLE answer including a retry, not per `claude` run: a resume that
# times out at 570s used to be followed by a fresh full run with another 570s,
# ~19 minutes in total, every second of it past the point of any use.
TURN_BUDGET_S = 540
MIN_RUN_S = 45          # below this there is no point starting a run at all


def fetch_token(origin):
    with urllib.request.urlopen(origin + '/_ns/token', timeout=5) as r:
        return json.load(r)['token']


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


def first_prompt(request):
    """Full context for turn 1: preamble + the chat's system prompt + the
    conversation so far. This becomes the resumed session's cached prefix."""
    parts = [PREAMBLE + system_text(request.get('system'))]
    parts.append('\n--- Conversation so far ---')
    for m in request.get('messages', []):
        who = 'User' if m.get('role') == 'user' else 'Assistant'
        parts.append(f'{who}: {block_text(m.get("content"))}')
    parts.append('\nAssistant:')
    return '\n'.join(parts)


def delta_prompt(request):
    """For a resumed turn: only the newest message (the session already holds
    everything before it). Usually the user's new input; after a TOOL_CALL it is
    the IDE's tool result, which we frame so the agent knows to continue."""
    messages = request.get('messages') or []
    # Notices ride the system prompt, which a resumed session never re-reads;
    # lead the delta with them so they are not lost. Framed as coming from the
    # IDE: they are not the user speaking.
    notices = notices_text(request)
    prefix = ('[Notices from the IDE, delivered with this turn]\n' + notices + '\n\n'
              if notices else '')
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


def run_claude(prompt, args, resume_session=None, timeout=TURN_BUDGET_S):
    # --output-format json returns {result, session_id, is_error, …}.
    cmd = [args.claude_bin, '-p', '--output-format', 'json']
    if resume_session:
        cmd += ['--resume', resume_session]
    if args.claude_args:
        cmd += shlex.split(args.claude_args)

    def run(on_stdin):
        # The prompt goes on stdin rather than argv. A resumed turn is a small
        # delta, but a cold turn carries the whole transcript plus its tool
        # results — each of which the front door lets run to 256 KB — and macOS
        # caps a process's arguments plus environment at ~1 MB. Past that the
        # exec fails with E2BIG and the chat sees a bare bridge error, at
        # exactly the moment the history is most worth having.
        return subprocess.run(
            cmd if on_stdin else cmd + [prompt],
            input=prompt if on_stdin else None,
            cwd=args.cwd, capture_output=True, text=True, timeout=timeout)

    proc = run(_STDIN_PROMPT[0])
    if (_STDIN_PROMPT[0] and prompt and proc.returncode == 0
            and not (proc.stdout or '').strip()):
        # A build that ignores stdin sees an empty prompt and succeeds at
        # saying nothing. That exact shape - clean exit, no output - is what
        # distinguishes it from a real failure, which reports on stderr and is
        # passed through below rather than retried.
        print('  [this claude build did not read the prompt from stdin; '
              'using argv (large prompts may fail)]', file=sys.stderr, flush=True)
        _STDIN_PROMPT[0] = False
        proc = run(False)

    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or 'claude exited nonzero').strip()[:500]
        if resume_session and _SESSION_GONE.search(detail):
            raise SessionGone(detail)
        raise RuntimeError(detail)
    try:
        data = json.loads(proc.stdout)
    except ValueError:
        # Some builds print plain text even with --output-format json; treat it
        # as the result and give up on session tracking for this turn.
        return proc.stdout.strip(), None
    if data.get('is_error'):
        detail = str(data.get('result') or 'claude reported an error')[:500]
        if resume_session and _SESSION_GONE.search(detail):
            raise SessionGone(detail)
        raise RuntimeError(detail)
    return str(data.get('result', '')).strip(), data.get('session_id')


class Bridge:
    def __init__(self, origin, token, name, args):
        self.origin, self.token, self.name, self.args = origin, token, name, args
        self.sessions = {}          # chat name -> claude session_id
        self.lock = threading.Lock()

    def reply_for(self, request, chat):
        """Run the agent and return an Anthropic-style response object (a text
        turn, or a tool_use turn if the agent asked to call an IDE tool)."""
        with self.lock:
            sid = self.sessions.get(chat)
        deadline = time.monotonic() + TURN_BUDGET_S

        def remaining():
            return int(deadline - time.monotonic())

        if sid is None:
            text, new_sid = run_claude(first_prompt(request), self.args,
                                       timeout=remaining())
        else:
            try:
                text, new_sid = run_claude(delta_prompt(request), self.args,
                                           resume_session=sid, timeout=remaining())
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
                text, new_sid = run_claude(first_prompt(request), self.args,
                                           timeout=remaining())
        if new_sid:
            with self.lock:
                self.sessions[chat] = new_sid
        return response_from_agent_text(text)

    def answer(self, msg):
        chat, corr_id = msg.get('from', '?'), msg.get('corr_id')
        try:
            response = self.reply_for(msg.get('request', {}), chat)
        except Exception as e:
            response = {'content': [{'type': 'text', 'text': f'[bus-claude bridge error: {e}]'}],
                        'stop_reason': 'end_turn'}

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
                        # One thread per request so a slow run doesn't stall the
                        # stream. The IDE serializes turns per chat, so a given
                        # chat's session id is never touched concurrently.
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
    args = ap.parse_args()

    token = fetch_token(args.origin)
    print(f'bus-claude {args.name!r} on {args.origin} — backing any Bus Agent chat '
          f'whose Model is {args.name!r} (one Claude Code session per chat). Ctrl-C to quit.',
          flush=True)
    Bridge(args.origin, token, args.name, args).receive_loop()


if __name__ == '__main__':
    main()
