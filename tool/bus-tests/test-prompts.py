#!/usr/bin/env python3
"""What the bridge actually sends the agent: prompts, notices, tool calls.

    python3 tool/bus-tests/test-prompts.py         (instant, nothing to set up)

These are pure functions, so this is a plain unit test. The cases that matter
are the ones where something the IDE said has to survive the trip:

  KILLED NOTICE   a turn this bridge killed must be disclosed at the start of
                  the next one, on EVERY path. It used to be told only to a
                  resumed session; on a cold one - after a bridge restart or a
                  lost session - the reason was popped and dropped, and the
                  agent walked back into the step that had just killed it.
  IDE NOTICES     ride the system prompt, which a resumed session never
                  re-reads, so the delta has to carry them (2026-09-06).
  TOOL_CALL       the marker must be found at a line start and from the last
                  one backwards, or a payload that mentions TOOL_CALL: eats it.

Run against an older bus-claude.py to see the first group go red:
    python3 tool/bus-tests/test-prompts.py /path/to/old/tool
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(HERE)

spec = importlib.util.spec_from_file_location(
    'bus_claude', os.path.join(TOOL, 'bus-claude.py'))
bus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bus)

failures = []


def check(name, condition, detail=''):
    print(('PASS  ' if condition else 'FAIL  ') + name + ('  ' + detail if detail else ''))
    if not condition:
        failures.append(name + (': ' + detail if detail else ''))


NOTICES = ('IMPORTANT — out-of-band updates since your last turn:\n'
           '- The user applied your proposed changeset cs7')

REQUEST = {
    'system': 'You are the IDE assistant.\n\n' + NOTICES,
    'messages': [
        {'role': 'user', 'content': 'what broke?'},
        {'role': 'assistant', 'content': 'looking'},
        {'role': 'user', 'content': 'any news?'},
    ],
}
REASON = 'claude produced no output for 900s (stuck?); killed'


def first(request, killed=None):
    """first_prompt, on whichever signature this bus-claude.py has."""
    try:
        return bus.first_prompt(request, killed=killed)
    except TypeError:
        return bus.first_prompt(request)        # the old shape: no way to tell it


# --- the killed notice, on both paths -------------------------------------
cold = first(REQUEST, killed=REASON)
check('cold run discloses the kill', 'KILLED' in cold and REASON in cold,
      '' if 'KILLED' in cold else 'the reason never reaches a fresh session')
check('cold notice is last before the reply',
      cold.rfind('KILLED') > cold.rfind('any news?'),
      'it must be the freshest thing the agent reads')
check('cold run says the context is gone',
      'session that is now gone' in cold or 'none of its context' in cold)

clean = first(REQUEST)
check('an unkilled cold run says nothing of it', 'KILLED' not in clean)

delta = bus.delta_prompt(REQUEST, killed=REASON)
check('resumed run discloses the kill', 'KILLED' in delta and REASON in delta)
check('resumed wording differs from cold',
      ('Your previous turn' in delta) and ('Your previous turn' not in cold),
      'a resumed session still has the context; a cold one does not')

# --- IDE notices ----------------------------------------------------------
check('delta carries the IDE notices', 'changeset cs7' in delta)
check('delta frames them as the IDE speaking', 'Notices from the IDE' in delta)
check('cold run gets them via the system prompt', 'changeset cs7' in clean)
check('notices_text finds only the notice paragraph',
      bus.notices_text(REQUEST).startswith('IMPORTANT')
      and 'You are the IDE assistant' not in bus.notices_text(REQUEST))

# --- the newest message is what a delta sends -----------------------------
check('delta sends the newest message', 'any news?' in delta)
check('delta does not resend the history', 'what broke?' not in delta)

tool_req = dict(REQUEST, messages=[{'role': 'user', 'content': [
    {'type': 'tool_result', 'tool_use_id': 't1', 'content': '42'}]}])
tool_delta = bus.delta_prompt(tool_req)
check('a tool result is framed as one', '42' in tool_delta and 'Continue' in tool_delta)

# --- TOOL_CALL parsing ----------------------------------------------------
call, before = bus.parse_tool_call(
    'Let me look.\nTOOL_CALL: {"name": "evaluate", "input": {"expr": "1 + 1"}}')
check('a plain tool call parses', call is not None and call['name'] == 'evaluate',
      '' if call else 'got none')
check('text before the call is kept', before == 'Let me look.')

# The payload mentions the marker: a reverse text search lands inside it.
tricky = ('TOOL_CALL: {"name": "propose_changes", "input": '
          '{"text": "the agent writes TOOL_CALL: at a line start"}}')
call2, _ = bus.parse_tool_call(tricky)
check('a payload quoting the marker still parses',
      call2 is not None and call2['name'] == 'propose_changes')

call3, _ = bus.parse_tool_call('Just an answer, no call.')
check('plain prose is not a tool call', call3 is None)

resp = bus.response_from_agent_text('done, nothing to change')
check('a text answer ends the turn', resp['stop_reason'] == 'end_turn')
resp2 = bus.response_from_agent_text(
    'checking\nTOOL_CALL: {"name": "inspect_object", "input": {}}')
check('a tool call asks the IDE to run it', resp2['stop_reason'] == 'tool_use')

print()
if failures:
    print('FAILURES:')
    for f in failures:
        print('  ' + f)
    sys.exit(1)
print('all prompt cases passed')
