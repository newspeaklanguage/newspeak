#!/usr/bin/env python3
"""Do bus-agent.py and bus-responder.py survive a front-door restart?

    python3 tool/bus-tests/test-reconnect.py      (a few seconds, no IDE needed)

A fake front door stands in for cors-proxy.py: it hands out a token, serves an
SSE stream to whoever presents the current one, and refuses anyone else with
403 - which is exactly what the real door does after a restart, since it mints
a fresh token per run.

Two things are asserted of each client, and each was false before 2026-09-19:

  RECOVERS   it re-reads the token and gets back on the stream. Capturing the
             token once (and, worse, reusing one urllib Request forever) left
             it spinning on 403 while still looking like it was up.
  PACES      it sleeps between attempts. Reconnecting flat out is a hot loop
             that prints to stderr as fast as the machine allows.

To see it go red, point it at a checkout of the old tools:

    mkdir /tmp/old && cd /tmp/old
    git show HEAD~1:tool/bus-agent.py > bus-agent.py       # a commit before the fix
    git show HEAD~1:tool/bus-responder.py > bus-responder.py
    python3 tool/bus-tests/test-reconnect.py /tmp/old

Both cases fail, with roughly fifteen THOUSAND attempts in the six seconds
each is watched, and the run then aborts - the spin exhausts the interpreter.
That is the bug, not a flaw in the harness.
"""
import importlib.util
import inspect
import json
import os
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.dirname(HERE)

DOOR = {'token': 'T1', 'attempts': [], 'generation': 0}
DOOR_LOCK = threading.Lock()


class FakeDoor(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def do_GET(self):
        if self.path.startswith('/_ns/token'):
            with DOOR_LOCK:
                body = json.dumps({'token': DOOR['token']}).encode()
            self.send_response(200)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path.startswith('/_ns/bus'):
            supplied = ''
            for part in self.path.split('?', 1)[-1].split('&'):
                if part.startswith('token='):
                    supplied = part[len('token='):]
            with DOOR_LOCK:
                ok = supplied == DOOR['token']
                DOOR['attempts'].append((time.monotonic(), supplied, ok))
                generation = DOOR['generation']
            if not ok:
                self.send_response(403)
                self.send_header('Content-Length', '0')
                self.end_headers()
                return
            self.send_response(200)
            self.send_header('Content-Type', 'text/event-stream')
            self.end_headers()
            try:
                self.wfile.write(b': connected\n\n')
                self.wfile.flush()
                # Hold it open until the door "restarts" under us.
                while True:
                    with DOOR_LOCK:
                        if DOOR['generation'] != generation:
                            return
                    self.wfile.write(b': keepalive\n\n')
                    self.wfile.flush()
                    time.sleep(0.1)
            except OSError:
                return
        self.send_response(404)
        self.send_header('Content-Length', '0')
        self.end_headers()


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def restart_door(new_token):
    """What a real front-door restart looks like from a client: the token it
    was using stops working, and its open stream dies."""
    with DOOR_LOCK:
        DOOR['token'] = new_token
        DOOR['generation'] += 1
        DOOR['attempts'].clear()


def attempts_since(t0):
    with DOOR_LOCK:
        return [a for a in DOOR['attempts'] if a[0] >= t0]


def check(label, start_client, read_token, settle=6.0):
    restart_door('T1')
    stop = start_client('T1')
    time.sleep(1.0)                      # let it establish the first stream
    t0 = time.monotonic()
    restart_door('T2')
    time.sleep(settle)
    tries = attempts_since(t0)
    recovered = any(ok for (_, _, ok) in tries) and read_token() == 'T2'
    # A paced client makes a handful of attempts in `settle` seconds; a hot
    # spin makes hundreds. The bar is deliberately loose.
    paced = len(tries) <= 4 * settle
    ok = recovered and paced
    print(('PASS  ' if ok else 'FAIL  ') +
          f'{label:14s} attempts={len(tries):4d}  token now {read_token()!r}  '
          f'{"recovered" if recovered else "STILL LOCKED OUT"}, '
          f'{"paced" if paced else "HOT SPIN"}')
    if stop:
        stop()
    return ok


def main():
    server = ThreadingHTTPServer(('127.0.0.1', 0), FakeDoor)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    origin = 'http://127.0.0.1:%d' % server.server_address[1]

    which = sys.argv[1] if len(sys.argv) > 1 else TOOL
    agent_py = os.path.join(which, 'bus-agent.py')
    responder_py = os.path.join(which, 'bus-responder.py')

    results = []

    agent = load(agent_py, 'bus_agent_under_test')
    # The fixed receive_loop takes a one-element box it can write a fresh
    # token into; the old one took the token itself, which is the bug. Both
    # shapes are accepted so this file doubles as the control: run it with the
    # path to a checkout of the old tools and both cases should fail.
    takes_box = 'token_box' in inspect.signature(agent.receive_loop).parameters
    box = {}

    def start_agent(tok):
        box['v'] = [tok]
        threading.Thread(target=agent.receive_loop, daemon=True,
                         args=(origin, box['v'] if takes_box else tok, 'probe')).start()
        return None

    results.append(check('bus-agent', start_agent, lambda: box['v'][0]))

    responder = load(responder_py, 'bus_responder_under_test')
    holder = {}

    def start_responder(tok):
        r = responder.Responder(origin, tok, 'probe')
        holder['r'] = r
        threading.Thread(target=r.receive_loop, daemon=True).start()
        return None

    results.append(check('bus-responder', start_responder,
                         lambda: holder['r'].token))

    print()
    if all(results):
        print('both clients survive a front-door restart')
        return 0
    print('FAILURES above')
    return 1


if __name__ == '__main__':
    sys.exit(main())
