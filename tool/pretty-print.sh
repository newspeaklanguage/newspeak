#!/bin/sh
# Script to pretty-print a Newspeak source file.
# Usage: ./pretty-print.sh <input.ns> <output.ns>
#
# Reads <input.ns>, runs it through NewspeakPrettyPrintApp, and writes
# the reformatted source to <output.ns>. The output filename may equal
# the input filename — the wrapper writes via a temp file in the output
# directory and atomically moves it into place, so in-place rewrite is
# safe.

# 1. Read utility functions and ensure directory is tool
if [ ! -f ./newspeak_util.sh ]; then
    printf "\n\nERROR: Run this command from Newspeak 'tool' directory. Current directory=%s. Exiting.\n\n" "$PWD"
    exit 1
fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

# 2. Check arguments
if [ "$#" -ne 2 ]; then
    printf "\nUsage: %s <input.ns> <output.ns>\n" "$0"
    printf "Example: %s ../NewspeakASTs.ns ../NewspeakASTs.ns   (in-place)\n" "$0"
    printf "         %s ../src.ns /tmp/formatted.ns           (to new file)\n\n" "$0"
    exit 1
fi

IN_RAW="$1"
OUT_RAW="$2"

# 3. Check input exists and resolve to absolute path
if [ ! -f "$IN_RAW" ]; then
    printf "\nERROR: Input file not found: %s\n\n" "$IN_RAW"
    exit 1
fi
IN="$(cd "$(dirname "$IN_RAW")" && pwd)/$(basename "$IN_RAW")"

# 4. Resolve output directory (must exist) and build absolute output path
OUT_DIR_RAW="$(dirname "$OUT_RAW")"
if [ ! -d "$OUT_DIR_RAW" ]; then
    printf "\nERROR: Output directory not found: %s\n\n" "$OUT_DIR_RAW"
    exit 1
fi
OUT_DIR="$(cd "$OUT_DIR_RAW" && pwd)"
OUT="${OUT_DIR}/$(basename "$OUT_RAW")"

# 5. Ensure primordialsoup is built
if [ ! -f "${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup" ]; then
    printf "ERROR: primordialsoup not found at %s\n" "${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup"
    printf "Please check newspeak_env.sh and ensure the system is built.\n\n"
    exit 1
fi

if [ ! -f "${PRIMORDIALSOUP}/out/snapshots/NewspeakPrettyPrintApp.vfuel" ]; then
    printf "ERROR: NewspeakPrettyPrintApp.vfuel not found.\n"
    printf "Build it with: cd %s/tool && ./build.sh\n\n" "${NEWSPEAK}"
    exit 1
fi

# 6. Run the app, capture stdout to a temp file in the same dir as OUT.
# Using a sibling temp file (rather than /tmp) means the final 'mv' is a
# rename within the same filesystem (atomic, no copy). Clean up the temp
# on failure so we don't litter the output directory.
TMP="$(mktemp "${OUT_DIR}/.pretty-print.XXXXXX")"
trap 'rm -f "$TMP"' EXIT

${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
    ${PRIMORDIALSOUP}/out/snapshots/NewspeakPrettyPrintApp.vfuel \
    "$IN" > "$TMP"

mv "$TMP" "$OUT"
trap - EXIT
