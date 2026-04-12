#!/bin/sh
# Script to parse and validate Newspeak source files
# Usage: ./parse-validate.sh <file.ns>

# 1. Read utility functions and ensure directory is tool
if [ ! -f ./newspeak_util.sh ]; then
    printf "\n\nERROR: Run this command from Newspeak 'tool' directory. Current directory=%s. Exiting.\n\n" "$PWD"
    exit 1
fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

# 2. Check that a file argument was provided
if [ -z "$1" ]; then
    printf "\nUsage: %s <file.ns>\n" "$0"
    printf "Example: %s ../NewspeakTypecheckerTesting.ns\n\n" "$0"
    exit 1
fi

FILE_TO_PARSE="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"

# 3. Check that the file exists
if [ ! -f "$FILE_TO_PARSE" ]; then
    printf "\nERROR: File not found: %s\n\n" "$FILE_TO_PARSE"
    exit 1
fi

printf "\nParsing: %s\n\n" "$(basename "$FILE_TO_PARSE")"

# 4. Ensure primordialsoup is built
if [ ! -f "${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup" ]; then
    printf "ERROR: primordialsoup not found at %s\n" "${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup"
    printf "Please check newspeak_env.sh and ensure the system is built.\n\n"
    exit 1
fi

if [ ! -f "${PRIMORDIALSOUP}/out/snapshots/NewspeakParser.vfuel" ]; then
    printf "ERROR: NewspeakParser.vfuel not found.\n"
    printf "Build it with: cd %s && ./out/ReleaseX64/primordialsoup ./out/snapshots/WebCompiler.vfuel ./newspeak/*.ns %s/NewspeakParser.ns RuntimeWithMirrorsForPrimordialSoup NewspeakParser ./out/snapshots/NewspeakParser.vfuel\n\n" "${PRIMORDIALSOUP}" "${NEWSPEAK}"
    exit 1
fi

# 5. Parse the file using NewspeakParser
${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
    ${PRIMORDIALSOUP}/out/snapshots/NewspeakParser.vfuel \
    "$FILE_TO_PARSE"
