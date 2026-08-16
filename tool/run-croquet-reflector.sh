#!/bin/sh
# Start the Croquet reflector (synchronizer) for local Newspeak-on-Croquet work.
#
# Usage: ./run-croquet-reflector.sh
#
# The port is 9090. That is not a choice we get to make: reflector.js hardcodes
# `const PORT = 9090` with no command-line or environment override, so changing it
# means editing that file.
#
# Why we self-host: Croquet's hosted backend is gone -- api.croquet.io does not
# answer, croquet.io/keys 404s, and multisynq.io returns 403, so no new API key can
# be obtained. Passing reflector= (or box=) to the client makes it skip API key
# verification entirely: getBackend() returns {apiKey:"none", signServer:"none"}
# BEFORE it validates the key, and verifyApiKey() short-circuits on
# signServer === "none". So a self-hosted reflector needs no key at all.
#
# See CROQUET_NOTES.md for the launch URL and what each URI parameter does.

set -e

if [ ! -f ./newspeak_util.sh ]; then
    printf "\nERROR: Run this command from the Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_env.sh

PORT=9090   # hardcoded in reflector.js; see the note above
REFLECTOR="${CROQUET_REFLECTOR:-${NEWSPEAK}/../croquet/packages/reflector}"

if [ ! -f "${REFLECTOR}/reflector.js" ]; then
    printf "\nERROR: reflector not found at %s\n" "${REFLECTOR}"
    printf "Clone it (Apache-2.0) with:\n"
    printf "    git clone --depth 1 https://github.com/croquet/croquet.git %s/../croquet\n" "${NEWSPEAK}"
    printf "or set CROQUET_REFLECTOR to an existing checkout.\n\n"
    exit 1
fi

# Emscripten's node, not the system one: the system node here is a broken node@12
# (missing icu4c dylib) and the reflector needs a modern runtime anyway.
NODE_BIN="$(ls -d "${EMSDK}"/node/*/bin 2>/dev/null | tail -1)"
if [ -n "${NODE_BIN}" ] && [ -x "${NODE_BIN}/node" ]; then
    PATH="${NODE_BIN}:${PATH}"
    export PATH
fi
if ! node --version > /dev/null 2>&1; then
    printf "\nERROR: no usable node found (looked in %s/node/*/bin and on PATH).\n\n" "${EMSDK}"
    exit 1
fi

if lsof -nP -iTCP:"${PORT}" -sTCP:LISTEN > /dev/null 2>&1; then
    printf "A server is already listening on port %s:\n" "${PORT}"
    lsof -nP -iTCP:"${PORT}" -sTCP:LISTEN
    printf "\nNothing to do (or kill it first to restart).\n"
    exit 0
fi

if [ ! -d "${REFLECTOR}/node_modules" ]; then
    printf "Installing reflector dependencies...\n"
    ( cd "${REFLECTOR}" && npm install --no-audit --no-fund )
fi

printf "node      %s\n" "$(node --version)"
printf "reflector %s\n" "${REFLECTOR}"
printf "listening ws://localhost:%s/\n\n" "${PORT}"

# --standalone      no cloud dependencies (no Google Cloud storage/secrets)
# --storage=none    keep session snapshots in memory only
# --no-loglatency   drop the per-message latency chatter
# npm start would pipe through pino-pretty; raw JSON is easier to grep, e.g.
#   grep '"event":"join"' reflector.log
cd "${REFLECTOR}"
exec node reflector.js --standalone --storage=none --no-loglatency
