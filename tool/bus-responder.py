#!/usr/bin/env python3
"""Back an in-IDE chat from outside — the "Level 2" end of the agent bus.

A Newspeak Web IDE chat created with the "Bus Agent" provider does not call a
hosted model; instead, each turn it sends a *completion request* over the bus
to an external agent named in the chat's model field, and waits for that agent's
*completion response*. This program is that agent: it subscribes under a name,
prints each completion request it receives, lets you type the reply, and sends
it back. So the chat is backed by whoever runs this — a human here, or a real
model if you wire one in.

The wire shape is Anthropic's Messages API. A request carries
{model, max_tokens, system, messages, tools}. A response is
{content: [ ...blocks... ], stop_reason}. For a plain text answer the block is
{"type":"text","text":"..."} and stop_reason is "end_turn" — this program builds
that for you from the line you type. To exercise the IDE's tool loop, answer
with a raw JSON response instead (see /json below): a tool_use block
{"type":"tool_use","id":"t1","name":"evaluate","input":{...}} with
stop_reason "tool_use" makes the IDE run that tool and send you its result as
the next request.

Also relays and lets you send plain bus messages, like bus-agent.py.

Usage (front door must run with --bus):
    python3 tool/bus-responder.py <agent-name> [--origin http://localhost:8080]

At the prompt:
    <text>              answer the most recent pending completion request as text
    /json <json>        answer it with a raw Anthropic-style response object
    /msg <chat> <text>  send a plain message to a chat (not a completion answer)
    /skip               drop the pending request without answering
Ctrl-C to quit.
"""

import argparse
import json
import sys
import threading
import urllib.request


def fetch_token(origin):
    with urllib.request.urlopen(origin + '/_ns/token', timeout=5) as r:
        return json.load(r)['token']


def post(origin, token, obj):
    req = urllib.request.Request(
        origin + '/_ns/bus', data=json.dumps(obj).encode('utf-8'), method='POST',
        headers={'Content-Type': 'application/json', 'X-NS-Token': token})
    with urllib.request.urlopen(req, timeout=5) as r:
        return json.load(r)


def last_user_text(messages):
    """A readable summary of what the chat is asking, for the human."""
    for m in reversed(messages or []):
        if m.get('role') != 'user':
            continue
        content = m.get('content')
        if isinstance(content, str):
            return content
        if isinstance(content, list):
            texts = []
            for b in content:
                if b.get('type') == 'text':
                    texts.append(b.get('text', ''))
                elif b.get('type') == 'tool_result':
                    texts.append('[tool_result for ' + str(b.get('tool_use_id')) + ']')
            if texts:
                return '\n'.join(texts)
    return '(no user text found)'


class Responder:
    def __init__(self, origin, token, name):
        self.origin, self.token, self.name = origin, token, name
        self.pending = None            # (corr_id, reply_to_chat) awaiting an answer

    def send_completion(self, chat, corr_id, response_obj):
        self.pending = None
        post(self.origin, self.token, {
            'to': chat, 'from': self.name,
            'kind': 'completion_response', 'corr_id': corr_id,
            'response': response_obj,
        })
        print(f'    [answered {corr_id}]\n> ', end='', flush=True)

    def answer_text(self, text):
        if not self.pending:
            print('    [no pending request to answer]\n> ', end='', flush=True)
            return
        corr_id, chat = self.pending
        self.send_completion(chat, corr_id, {
            'content': [{'type': 'text', 'text': text}], 'stop_reason': 'end_turn'})

    def answer_json(self, raw):
        if not self.pending:
            print('    [no pending request]\n> ', end='', flush=True)
            return
        try:
            obj = json.loads(raw)
        except ValueError as e:
            print(f'    [not valid JSON: {e}]\n> ', end='', flush=True)
            return
        corr_id, chat = self.pending
        self.send_completion(chat, corr_id, obj)

    def on_message(self, msg):
        kind = msg.get('kind', 'message')
        if kind == 'completion_request':
            req = msg.get('request', {})
            chat = msg.get('from', '?')
            corr_id = msg.get('corr_id')
            tools = [t.get('name') for t in (req.get('tools') or [])]
            self.pending = (corr_id, chat)
            print(f'\n=== completion request from chat {chat!r} (corr {corr_id}) ===')
            print('  asking:', last_user_text(req.get('messages')))
            if tools:
                print('  tools available to you (the IDE will run them):', ', '.join(tools))
            print('  → type a reply to answer as text, or /json <obj> for a raw response\n> ',
                  end='', flush=True)
        else:                                   # a plain message or notice
            print(f'\n<<< {kind} from {msg.get("from")!r}: {msg.get("text","")}\n> ',
                  end='', flush=True)

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
                        if msg.get('to') != self.name:
                            continue            # not addressed to us
                        self.on_message(msg)
            except Exception as e:
                print(f'\n[stream dropped: {e}; reconnecting]', file=sys.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name', help="this agent's bus name (the chat's model field)")
    ap.add_argument('--origin', default='http://localhost:8080')
    args = ap.parse_args()

    token = fetch_token(args.origin)
    r = Responder(args.origin, token, args.name)
    print(f'responder {args.name!r} on {args.origin} — backing any chat whose model is {args.name!r}')
    print('answer requests by typing; /json <obj>, /msg <chat> <text>, /skip; Ctrl-C to quit\n> ',
          end='', flush=True)

    threading.Thread(target=r.receive_loop, daemon=True).start()

    for line in sys.stdin:
        line = line.rstrip('\n')
        if not line.strip():
            print('> ', end='', flush=True)
            continue
        if line.startswith('/json '):
            r.answer_json(line[len('/json '):])
        elif line.startswith('/msg '):
            rest = line[len('/msg '):].split(None, 1)
            if len(rest) == 2:
                post(args.origin, token,
                     {'to': rest[0], 'from': args.name, 'text': rest[1], 'kind': 'message'})
            print('> ', end='', flush=True)
        elif line.strip() == '/skip':
            r.pending = None
            print('    [dropped]\n> ', end='', flush=True)
        else:
            r.answer_text(line)


if __name__ == '__main__':
    main()
