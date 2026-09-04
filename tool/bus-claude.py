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
import urllib.request
import uuid


def fetch_token(origin):
    with urllib.request.urlopen(origin + '/_ns/token', timeout=5) as r:
        return json.load(r)['token']


def post(origin, token, obj):
    req = urllib.request.Request(
        origin + '/_ns/bus', data=json.dumps(obj).encode('utf-8'), method='POST',
        headers={'Content-Type': 'application/json', 'X-NS-Token': token})
    with urllib.request.urlopen(req, timeout=10) as r:
        return json.load(r)


def system_text(system):
    if isinstance(system, str):
        return system
    if isinstance(system, list):                       # Anthropic system blocks
        return '\n'.join(b.get('text', '') for b in system if isinstance(b, dict))
    return ''


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
    if not messages:
        return '(no new message)'
    last = messages[-1]
    content = last.get('content')
    if isinstance(content, list) and any(
            isinstance(b, dict) and b.get('type') == 'tool_result' for b in content):
        return ('The IDE ran your tool call. Result:\n\n' + block_text(content) +
                '\n\nContinue: either make another TOOL_CALL, or give your final '
                'answer as plain text.')
    return block_text(content)


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


def parse_tool_call(text):
    """If the agent's output ends in a TOOL_CALL, return (call, before_text)
    where call = {name, input}; else (None, None). Tolerant of code fences and
    a leading 'json' language tag after the marker."""
    idx = text.rfind('TOOL_CALL:')
    if idx < 0:
        return None, None
    before = text[:idx].strip().strip('`').strip()
    after = text[idx + len('TOOL_CALL:'):].strip()
    after = after.strip('`').strip()
    if after.lower().startswith('json'):
        after = after[4:].strip()
    obj_str = extract_first_json(after)
    if obj_str is None:
        return None, None
    try:
        obj = json.loads(obj_str)
    except ValueError:
        return None, None
    name = obj.get('name')
    if not isinstance(name, str) or not name:
        return None, None
    return {'name': name, 'input': obj.get('input') or {}}, before


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


def run_claude(prompt, args, resume_session=None):
    # --output-format json returns {result, session_id, is_error, …}.
    cmd = [args.claude_bin, '-p', '--output-format', 'json']
    if resume_session:
        cmd += ['--resume', resume_session]
    if args.claude_args:
        cmd += shlex.split(args.claude_args)
    cmd += [prompt]
    proc = subprocess.run(cmd, cwd=args.cwd, capture_output=True, text=True, timeout=570)
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or 'claude exited nonzero').strip()[:500])
    try:
        data = json.loads(proc.stdout)
    except ValueError:
        # Some builds print plain text even with --output-format json; treat it
        # as the result and give up on session tracking for this turn.
        return proc.stdout.strip(), None
    if data.get('is_error'):
        raise RuntimeError(str(data.get('result') or 'claude reported an error')[:500])
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
        if sid is None:
            text, new_sid = run_claude(first_prompt(request), self.args)
        else:
            try:
                text, new_sid = run_claude(delta_prompt(request), self.args, resume_session=sid)
            except Exception as e:
                print(f'  [resume of {sid} failed ({e}); starting a fresh session]', flush=True)
                text, new_sid = run_claude(first_prompt(request), self.args)
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
        try:
            post(self.origin, self.token, {
                'to': chat, 'from': self.name, 'kind': 'completion_response',
                'corr_id': corr_id, 'response': response,
            })
            kind = response.get('stop_reason')
            summary = next((b.get('name') if b.get('type') == 'tool_use' else b.get('text', '')
                            for b in response.get('content', [])), '')
            print(f'  [answered {corr_id} for chat {chat!r} ({kind}): {str(summary)[:70]!r}…]',
                  flush=True)
        except Exception as e:
            print(f'  [failed to post answer for {corr_id}: {e}]', file=sys.stderr, flush=True)

    def receive_loop(self):
        url = self.origin + '/_ns/bus?token=' + self.token
        req = urllib.request.Request(url, headers={'Accept': 'text/event-stream'})
        while True:
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
