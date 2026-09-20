# Bus tests

Three suites over the agent bus, all stdlib-only and offline: no front door, no
`claude`, no IDE, no network. Seconds each.

    python3 tool/bus-tests/test-prompts.py     # what the bridge sends the agent
    python3 tool/bus-tests/test-watchdog.py    # when the bridge kills a run
    python3 tool/bus-tests/test-reconnect.py   # surviving a front-door restart

Each takes an optional path to a directory of older `bus-*.py` files, so the
cases can be shown RED on the bug they guard rather than merely green now:

    mkdir /tmp/old
    git show <commit-before-the-fix>:tool/bus-claude.py > /tmp/old/bus-claude.py
    python3 tool/bus-tests/test-prompts.py /tmp/old

`test-watchdog.py` scales the real constants (IDLE_S 900s, --hard-cap 3600s)
down to seconds, and drives `fake_claude.py` — a stand-in for `claude -p
--output-format stream-json` whose behaviour is a SCRIPT of sleeps, streamed
lines and spawned children. Its own control lives in its docstring.

After changing any of the bus tools, restart whatever is running them: a bridge
or agent started before its source changed keeps serving the old code, and only
says so on stderr.
