#!/usr/bin/env python3
"""A reference external agent for the Newspeak host agent bus (/_ns/bus).

The bus (HOST_SERVICES_DESIGN_2026-08-31.md, staging step 6) lets programs
outside the IDE converse with in-IDE AI chat sessions by name. This is the
"other end": it subscribes to the bus under an agent name, prints messages
addressed to that name, and lets you send messages (or replies) back.

It is deliberately tiny and stdlib-only — the whole bus protocol is: fetch a
token, hold a GET open as an SSE stream to receive, POST JSON to send.

Addressing: every message has "to" (destination name) and "from" (sender). The
IDE delivers a message whose "to" matches one of its chat names as a
[from external agent '<from>'] turn in that chat; a chat replies with
send_to_agent to '<from>'. So when this agent receives a message, its "from" is
the chat to reply to.

Usage (the front door must be running with --bus):
    python3 tool/bus-agent.py <agent-name> [--origin http://localhost:8080]

Then, on stdin, type lines to send:
    <chat-name> <text...>          send text to a chat (drives a turn)
    /notice <chat-name> <text...>  send an out-of-band notice (no turn)
Received messages are printed as they arrive. Ctrl-C to quit.

To reach a chat named "alpha" so its AI can converse with you, this agent must
be running before "alpha" calls send_to_agent with this agent's name — or the
chat can just be told your name by the human and message you first.
"""

import argparse
import json
import sys
import threading
import time
import urllib.parse
import urllib.request


def fetch_token(origin):
    with urllib.request.urlopen(origin + '/_ns/token', timeout=5) as r:
        return json.load(r)['token']


def post(origin, token, obj):
    data = json.dumps(obj).encode('utf-8')
    req = urllib.request.Request(
        origin + '/_ns/bus', data=data, method='POST',
        headers={'Content-Type': 'application/json', 'X-NS-Token': token})
    with urllib.request.urlopen(req, timeout=5) as r:
        return json.load(r)


def receive_loop(origin, token_box, my_name):
    # Hold the SSE stream open; print messages addressed to this agent.
    # `token_box` is a one-element list rather than the token itself so that a
    # token re-read here is also seen by the sender in main().
    while True:
        # Declare our name on the stream so the front door can answer
        # /_ns/bus/agents. The bus is per-machine, and a collaborating IDE
        # session needs to know WHICH participant can reach this agent.
        #
        # Built fresh each time round, because the token is re-read on every
        # reconnect rather than captured once: the front door mints a new one
        # per run, so after it restarts the old token is refused and this would
        # spin on 403 forever while appearing to be up.
        url = (origin + '/_ns/bus?token=' + token_box[0]
               + '&name=' + urllib.parse.quote(my_name))
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
                    if msg.get('to') != my_name:
                        continue                      # not for us; ignore
                    frm = msg.get('from', '?')
                    kind = msg.get('kind', 'message')
                    text = msg.get('text', '')
                    print(f'\n<<< from {frm!r} ({kind}): {text}\n'
                          f'    (reply:  {frm} <your text>)\n> ', end='', flush=True)
        except Exception as e:
            # And sleep before trying again: with the front door down,
            # reconnecting flat out is a hot loop printing to stderr.
            print(f'\n[stream dropped: {e}; reconnecting]', file=sys.stderr)
            time.sleep(1)
            try:
                token_box[0] = fetch_token(origin)
            except Exception as e2:
                print(f'[the front door is not answering ({e2}); will keep trying]',
                      file=sys.stderr)
                time.sleep(4)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name', help="this agent's bus name (what chats address)")
    ap.add_argument('--origin', default='http://localhost:8080')
    args = ap.parse_args()

    token_box = [fetch_token(args.origin)]
    print(f'agent {args.name!r} on {args.origin}  (token acquired)')
    print('type:  <chat> <text>   |   /notice <chat> <text>   |   Ctrl-C to quit\n> ',
          end='', flush=True)

    t = threading.Thread(
        target=receive_loop, args=(args.origin, token_box, args.name), daemon=True)
    t.start()

    for line in sys.stdin:
        line = line.strip()
        if not line:
            print('> ', end='', flush=True)
            continue
        kind = 'message'
        if line.startswith('/notice '):
            kind = 'notice'
            line = line[len('/notice '):]
        parts = line.split(None, 1)
        if len(parts) < 2:
            print('need: <chat-name> <text>\n> ', end='', flush=True)
            continue
        to, text = parts
        try:
            res = post(args.origin, token_box[0],
                       {'to': to, 'from': args.name, 'text': text, 'kind': kind})
            print(f'    [sent id={res.get("id")}, {res.get("listeners")} listener(s)]\n> ',
                  end='', flush=True)
        except Exception as e:
            print(f'    [send failed: {e}]\n> ', end='', flush=True)


if __name__ == '__main__':
    main()
