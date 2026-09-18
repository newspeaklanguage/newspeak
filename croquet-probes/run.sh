#!/bin/sh
# Run a probe from croquet-probes/ with the emsdk node 22 (the system node is
# broken - missing icu4c dylib). Leading VAR=value arguments become environment
# for the probe, so every recipe is one invocation of this ONE script:
#
#   croquet-probes/run.sh setup-latejoin-probe.js
#   croquet-probes/run.sh PROVIDER=openai-compat NOTICE=1 setup-latejoin-probe.js
#   croquet-probes/run.sh NS_SUFFIX=-TEST NS_PAGE=croquetpsoup-test.html FAIL_TURN=1 PROVIDER=openai-compat setup-latejoin-probe.js
#
# It exists so that a single permission-list entry (Bash(croquet-probes/run.sh:*))
# lets an assistant session run any probe with any environment without a
# prompt; a bare `VAR=x /path/to/node probe.js` has no stable prefix to allow.
# Runs from the repository root regardless of the caller's directory.
cd "$(dirname "$0")/.." || exit 1
NODE=/Users/gbracha/software/emsdk-main/node/22.16.0_64bit/bin/node
# The probes require 'ws', which this repository does not vendor; the Croquet
# reflector's checkout has it. Some probes set this for themselves, the older
# ones never did. A NODE_PATH given on the command line still wins.
: "${NODE_PATH:=/Users/gbracha/newspeak/dev/web/croquet/packages/reflector/node_modules}"
export NODE_PATH
while [ $# -gt 0 ]; do
    case "$1" in
        *=*) export "$1"; shift ;;
        *) break ;;
    esac
done
if [ $# -eq 0 ]; then
    echo "usage: croquet-probes/run.sh [VAR=value ...] <probe.js> [probe args]" >&2
    exit 2
fi
probe=$1; shift
exec "$NODE" "croquet-probes/$probe" "$@"
