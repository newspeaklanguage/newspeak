#!/bin/sh
# Script to run Newspeak tests using NewspeakTestRunner
# Usage: ./run-tests.sh <TestConfigurationClass>

# 1. Read utility functions and ensure directory is tool
if [ ! -f ./newspeak_util.sh ]; then
    printf "\n\nERROR: Run this command from Newspeak 'tool' directory. Current directory=%s. Exiting.\n\n" "$PWD"
    exit 1
fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

# 2. Check that a test configuration argument was provided
if [ -z "$1" ]; then
    printf "\nUsage: %s <TestConfigurationClass>\n" "$0"
    printf "Example: %s NewspeakTypecheckerTestingConfiguration\n\n" "$0"
    exit 1
fi

TEST_CONFIG="$1"

# 3. Ensure primordialsoup is built
if [ ! -f "${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup" ]; then
    printf "ERROR: primordialsoup not found at %s\n" "${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup"
    printf "Please check newspeak_env.sh and ensure the system is built.\n\n"
    exit 1
fi

if [ ! -f "${PRIMORDIALSOUP}/out/snapshots/NewspeakTestRunner.vfuel" ]; then
    printf "ERROR: NewspeakTestRunner.vfuel not found.\n"
    printf "Build it with: cd %s/tool && ./build.sh\n\n" "${NEWSPEAK}"
    exit 1
fi

# 4. Find the test configuration file and related test files
# The configuration file should be named like <TestConfigurationClass>.ns
# We also need to find the associated testing file (without "Configuration"  or "TestingConfiguration" suffix)
CONFIG_FILE="${NEWSPEAK}/${TEST_CONFIG}.ns"

# Handle both "TestingConfiguration" and "Configuration" suffixes
if echo "$TEST_CONFIG" | grep -q 'TestingConfiguration$'; then
    TEST_BASE=$(echo "$TEST_CONFIG" | sed 's/TestingConfiguration$//')
    IMPL_FILE="${NEWSPEAK}/${TEST_BASE}.ns"
    TEST_FILE="${NEWSPEAK}/${TEST_BASE}Testing.ns"
else
    TEST_BASE=$(echo "$TEST_CONFIG" | sed 's/Configuration$//')
    TEST_FILE="${NEWSPEAK}/${TEST_BASE}.ns"
    IMPL_FILE=""
fi

# Build list of additional files to load (in dependency order).
# Any extra .ns files passed after the test-config name are appended
# (lets callers thread in test deps the auto-discovery doesn't know
# about — e.g. multi-file packages like MemoryHole, which has
# VCSCore, VCSDiffing, VCSSourceMirrors, etc., none of which match
# the TEST_BASE name).
ADDITIONAL_FILES=""
if [ -n "$IMPL_FILE" ] && [ -f "$IMPL_FILE" ]; then
    ADDITIONAL_FILES="$IMPL_FILE"
fi
if [ -f "$TEST_FILE" ]; then
    ADDITIONAL_FILES="$ADDITIONAL_FILES $TEST_FILE"
fi
if [ -f "$CONFIG_FILE" ]; then
    ADDITIONAL_FILES="$ADDITIONAL_FILES $CONFIG_FILE"
fi
shift  # drop $1 (TEST_CONFIG); remaining args are extra dep files
for extra in "$@"; do
    if [ -f "$extra" ]; then
        ADDITIONAL_FILES="$ADDITIONAL_FILES $extra"
    elif [ -f "${NEWSPEAK}/$extra" ]; then
        ADDITIONAL_FILES="$ADDITIONAL_FILES ${NEWSPEAK}/$extra"
    else
        printf "WARNING: extra dep file not found: %s\n" "$extra"
    fi
done

# 5. Run the tests using NewspeakTestRunner
printf "\nRunning tests: %s\n\n" "$TEST_CONFIG"

${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
    ${PRIMORDIALSOUP}/out/snapshots/NewspeakTestRunner.vfuel \
    "$TEST_CONFIG" $ADDITIONAL_FILES
