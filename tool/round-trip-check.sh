#!/bin/sh
# Verifies a Newspeak source file round-trips through the pretty printer
# with no loss of information:
#   parse → pretty-print → re-parse → compare ASTs and comments.
# Prints one line per file: "OK: <path>" on success, "FAIL: <path>: <reason>"
# on mismatch. Exit status: 0 if all files round-trip cleanly, 1 otherwise.
#
# Usage: ./round-trip-check.sh <file.ns> [file2.ns ...]

if [ ! -f ./newspeak_util.sh ]; then
    printf "\n\nERROR: Run this command from Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

if [ "$#" -lt 1 ]; then
    printf "Usage: %s <file.ns> [file2.ns ...]\n" "$0"
    exit 1
fi

if [ ! -f "${PRIMORDIALSOUP}/out/snapshots/NewspeakRoundTripCheckApp.vfuel" ]; then
    printf "ERROR: NewspeakRoundTripCheckApp.vfuel not found.\n"
    printf "Build it with: cd %s/tool && ./build.sh\n\n" "${NEWSPEAK}"
    exit 1
fi

# Resolve every argument to an absolute path before invocation.
ABS_ARGS=""
for f in "$@"; do
    if [ ! -f "$f" ]; then
        printf "ERROR: File not found: %s\n" "$f"
        exit 1
    fi
    ABS_ARGS="$ABS_ARGS $(cd "$(dirname "$f")" && pwd)/$(basename "$f")"
done

# Run the app, then derive the script's exit code from its stdout.
# The Newspeak VM doesn't propagate main:'s return value as a process
# exit status, so we have to grep for "FAIL:" lines ourselves.
TMP_OUT="$(mktemp)"
trap 'rm -f "$TMP_OUT"' EXIT

# shellcheck disable=SC2086
${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
    ${PRIMORDIALSOUP}/out/snapshots/NewspeakRoundTripCheckApp.vfuel \
    $ABS_ARGS > "$TMP_OUT" 2>&1

cat "$TMP_OUT"

if grep -q "^FAIL:" "$TMP_OUT"; then
    exit 1
fi
exit 0
