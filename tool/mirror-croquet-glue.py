#!/usr/bin/env python3
"""Generate the Croquet glue that a JS deploy ships from the canonical copy.

The Croquet integration script exists twice: primordialsoup/meta/croquet-post.js,
linked into the psoup build by emscripten, and a Newspeak string literal in
DeploymentManager.ns (JSPackager>>croquetSupportScript), written out beside a
Croquet JS deploy as <name>.croquet.js. The second used to be kept in step by
hand, and was not: by 2026-09-17 it lacked the await path, held answers, replay
pacing and the mint ledger. This script makes it a function of the first.

    tool/mirror-croquet-glue.py            regenerate the literal in DeploymentManager.ns
    tool/mirror-croquet-glue.py --check    exit 1 if the literal is stale; write nothing
    tool/mirror-croquet-glue.py --emit F   also write the generated JavaScript to F

The canonical file marks what differs:
    // <psoup-only> ... // </psoup-only>   dropped
    // <startup> ... end of file           replaced by tool/croquet-glue-js/startup.js
and tool/croquet-glue-js/header.js is put in front.

After regenerating: parse-validate DeploymentManager.ns BEFORE pretty-printing it
(an in-place pretty-print of an unparsable file overwrites it with the error
text), then round-trip and parse-validate again, as for any .ns edit.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NEWSPEAK = os.path.dirname(HERE)
PSOUP = os.environ.get('PRIMORDIALSOUP') or os.path.join(os.path.dirname(NEWSPEAK), 'primordialsoup')
META = os.path.join(PSOUP, 'meta', 'croquet-post.js')
DM = os.path.join(NEWSPEAK, 'DeploymentManager.ns')
HEADER = os.path.join(HERE, 'croquet-glue-js', 'header.js')
STARTUP = os.path.join(HERE, 'croquet-glue-js', 'startup.js')
METHOD = 'croquetSupportScript ^<String> = ('
BEGIN, END, START = '// <psoup-only>', '// </psoup-only>', '// <startup>'


def generate():
    out, skipping, started = [], False, False
    for n, line in enumerate(open(META).read().split('\n'), 1):
        t = line.strip()
        if t.startswith(BEGIN):
            if skipping:
                sys.exit('%s:%d: nested %s' % (META, n, BEGIN))
            skipping = True
        elif t.startswith(END):
            if not skipping:
                sys.exit('%s:%d: %s without %s' % (META, n, END, BEGIN))
            skipping = False
        elif t.startswith(START):
            if skipping:
                sys.exit('%s:%d: %s inside a psoup-only region' % (META, n, START))
            started = True
            break
        elif not skipping:
            out.append(line)
    if skipping:
        sys.exit('%s: unclosed %s' % (META, BEGIN))
    if not started:
        sys.exit('%s: no %s marker' % (META, START))
    body = '\n'.join(out).strip('\n')
    return open(HEADER).read().rstrip('\n') + '\n\n' + body + '\n\n' + open(STARTUP).read().rstrip('\n') + '\n'


def literal_span(s):
    """(start, end) of the literal's CONTENT, between its delimiting quotes."""
    i = s.index(METHOD)
    a = s.index("^'", i) + 2
    k = a
    while True:
        k = s.index("'", k)
        if s[k:k + 2] == "''":
            k += 2
            continue
        return a, k


def main():
    args = sys.argv[1:]
    check = '--check' in args
    js = generate()
    if '--emit' in args:
        open(args[args.index('--emit') + 1], 'w').write(js)
    s = open(DM).read()
    a, k = literal_span(s)
    quoted = js.replace("'", "''")
    if s[a:k] == quoted:
        print('croquetSupportScript is up to date (%d lines)' % js.count('\n'))
        return 0
    if check:
        print('croquetSupportScript is STALE: run tool/mirror-croquet-glue.py')
        return 1
    open(DM, 'w').write(s[:a] + quoted + s[k:])
    print('croquetSupportScript regenerated: %d lines (was %d)' % (js.count('\n'), s[a:k].count('\n')))
    print('now: parse-validate, THEN pretty-print, round-trip, parse-validate DeploymentManager.ns')
    return 0


if __name__ == '__main__':
    sys.exit(main())
