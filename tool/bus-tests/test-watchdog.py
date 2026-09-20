#!/usr/bin/env python3
"""Exercise bus-claude's run_claude watchdog against a scripted fake agent.

    python3 tool/bus-tests/test-watchdog.py        (a few seconds, no bus needed)

No front door, no `claude`, no network: fake_claude.py stands in for the agent
and is driven by a SCRIPT of sleeps, streamed lines and spawned children, and
the real constants are scaled down so each case takes seconds.

The point of each case is the regression it guards:
  - alive_but_slow  is the bug that was reported (killed at 9 min of real work)
  - stuck           is the only kill that should ever happen by default
  - hard_cap        is the new --hard-cap flag actually biting
  - no_cap          is --hard-cap 0 removing it
"""
import argparse
import importlib.util
import os
import re
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
BUS = os.path.join(os.path.dirname(HERE), 'bus-claude.py')

spec = importlib.util.spec_from_file_location('bus_claude', BUS)
bus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bus)

FAKE = os.path.join(HERE, 'fake_claude.py')

# Scaled down so the suite runs in seconds; the real values are 900 and 3600.
bus.IDLE_S = 2
bus.TOOL_HEARTBEAT_S = 1

failures = []


def case(name, script, hard_cap=3600, expect=None):
    os.environ['SCRIPT'] = script
    args = argparse.Namespace(claude_bin=FAKE, cwd=None,
                              claude_args='', hard_cap=hard_cap)
    beats = []
    started = time.monotonic()
    try:
        text, sid = bus.run_claude('hello', args, progress=beats.append)
        got = 'ok:' + text
    except Exception as e:
        got = 'err:' + str(e)
    took = time.monotonic() - started
    ok = expect in got
    print(('PASS  ' if ok else 'FAIL  ') +
          f'{name:16s} {took:5.1f}s  beats={len(beats):2d}  {got[:72]}')
    if not ok:
        failures.append(f'{name}: expected {expect!r} in {got!r}')


# A turn alive across more than one IDLE_S window: three silent stretches, each
# under the budget, with a line between them. Under the old two-budget code the
# equivalent (TURN_BUDGET_S < IDLE_S) killed this.
case('alive_but_slow', 's1.5,l,s1.5,l,s1.5', expect='ok:done')

# Silence past IDLE_S with the agent still running: the one real hang.
case('stuck', 'hang', expect='no output for 2s')

# Streaming steadily, but past the cap: only --hard-cap can stop this.
case('hard_cap', 's1,l,s1,l,s1,l,s1,l,s1', hard_cap=2, expect='absolute cap of 2s')

# Same run, cap removed.
case('no_cap', 's1,l,s1,l,s1,l,s1,l,s1', hard_cap=0, expect='ok:done')

# STREAMING heartbeat: the agent is generating without pause, so the stream
# never goes quiet and the bridge is content - but the IDE hears only what the
# bridge posts, and its watchdog is the one that fires. Beats must keep coming.
os.environ['SCRIPT'] = 'r3'
args = argparse.Namespace(claude_bin=FAKE, cwd=None, claude_args='', hard_cap=3600)
beats = []
bus.run_claude('hello', args, progress=beats.append)
if len(beats) >= 2:
    print(f'PASS  stream_beat      {len(beats)} frame(s) while streaming: {beats[0]!r}')
else:
    failures.append(f'stream_beat: only {len(beats)} frame(s) during 3s of steady output')
    print(f'FAIL  stream_beat      only {len(beats)} frame(s) during 3s of steady output')

# A killed run must take its children with it: the kill happens BECAUSE a tool
# is hanging, so there is always one.
os.environ['SCRIPT'] = 'c,hang'
os.environ['PIDFILE'] = os.path.join(tempfile.gettempdir(), 'ns-bus-test-child.pid')
if os.path.exists(os.environ['PIDFILE']):
    os.remove(os.environ['PIDFILE'])
args = argparse.Namespace(claude_bin=FAKE, cwd=None, claude_args='', hard_cap=3600)
child_pid = [None]


def sniff(_):
    pass


try:
    bus.run_claude('hello', args, progress=sniff)
except Exception:
    pass
if os.path.exists(os.environ['PIDFILE']):
    child_pid[0] = int(open(os.environ['PIDFILE']).read())
if child_pid[0] is None:
    failures.append('orphan: could not learn the child pid from the run')
    print('FAIL  orphan          could not learn the child pid')
else:
    time.sleep(0.5)
    try:
        os.kill(child_pid[0], 0)
        alive = True
    except OSError:
        alive = False
    if alive:
        failures.append(f'orphan: child {child_pid[0]} survived the kill')
        print(f'FAIL  orphan          child {child_pid[0]} survived the kill')
        os.kill(child_pid[0], 9)
    else:
        print(f'PASS  orphan          child {child_pid[0]} died with the run')
    try:
        os.remove(os.environ['PIDFILE'])        # leave no artifact behind
    except OSError:
        pass

# A heartbeat must be posted while a call is in flight, or the IDE's own
# watchdog never gets pushed out.
os.environ['SCRIPT'] = 's1.5,l,s1.5'
args = argparse.Namespace(claude_bin=FAKE, cwd=None, claude_args='',
                          hard_cap=3600)
beats = []
bus.run_claude('hello', args, progress=beats.append)
if beats:
    print(f'PASS  heartbeat       {len(beats)} frame(s): {beats[0]!r}')
else:
    failures.append('heartbeat: no progress frames during a silent stretch')
    print('FAIL  heartbeat       no progress frames posted')

print()
if failures:
    print('FAILURES:')
    for f in failures:
        print('  ' + f)
    sys.exit(1)
print('all watchdog cases passed')
