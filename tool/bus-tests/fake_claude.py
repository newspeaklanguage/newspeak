#!/usr/bin/env python3
"""A stand-in for `claude -p --output-format stream-json`, driven by env vars.

SCRIPT is a comma-separated list of steps:
  s<N>   sleep N seconds, emitting nothing (a tool call in flight)
  l      emit one assistant line (a sign of life)
  r<N>   stream lines steadily for N seconds (generating, never silent)
  c      spawn a long-lived grandchild, then print its pid on stderr
Then a final `result` line is emitted, unless SCRIPT ends with `hang`.
"""
import json
import os
import sys
import time

sys.stdin.read()
steps = os.environ.get('SCRIPT', '').split(',')
hang = steps and steps[-1] == 'hang'
if hang:
    steps = steps[:-1]
for step in steps:
    if not step:
        continue
    if step.startswith('s'):
        time.sleep(float(step[1:]))
    elif step.startswith('r'):
        until = time.time() + float(step[1:])
        while time.time() < until:
            print(json.dumps({'type': 'assistant',
                              'message': {'content': [{'type': 'text', 'text': '.'}]}}),
                  flush=True)
            time.sleep(0.1)
    elif step == 'c':
        import subprocess
        kid = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(3600)'])
        print('CHILD_PID=%d' % kid.pid, file=sys.stderr, flush=True)
        if os.environ.get('PIDFILE'):
            open(os.environ['PIDFILE'], 'w').write(str(kid.pid))
    elif step == 'l':
        print(json.dumps({'type': 'assistant',
                          'message': {'content': [{'type': 'text', 'text': 'thinking'}]}}),
              flush=True)
if hang:
    time.sleep(3600)
print(json.dumps({'type': 'result', 'result': 'done', 'session_id': 'sess-1',
                  'is_error': False}), flush=True)
