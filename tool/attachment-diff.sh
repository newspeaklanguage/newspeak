#!/bin/sh
# Reports every comment that changed owner between two versions of a
# Newspeak source file -- a comment that used to document one member and
# now documents another.
#
# Usage: ./attachment-diff.sh <old.ns> <new.ns> [<old2.ns> <new2.ns> ...]
#        ./attachment-diff.sh --since <rev> <file.ns> [file.ns ...]
#
# The second form is the usual one: it compares each file as of <rev>
# against its current text, extracting the old versions from git for you.
#
# Why this exists: the pretty printer used to reattach comments to the
# wrong member when it put a class body in canonical order. That is
# fixed, but damaged text is a FIXED POINT -- printing it again
# reproduces it, and round-trip-check.sh confirms attachment was
# preserved, wrong owner and all. A corrupted file cannot diagnose
# itself; the only witness is an older version of it.
#
# Output, one verdict line per pair:
#   SAME  <file>            nothing changed owner
#   PURE  <file>: N ...     the versions are the same code with the same
#                           comments, so the change was a pure reformat
#                           and every listed move is printer damage
#   MIXED <file>: N ...     real edits are present; listed moves are
#                           candidates for review, not conclusions
#   ERROR <file>: ...       could not read or parse
# Exit status: 0 if nothing was reported, 1 otherwise.

if [ ! -f ./newspeak_util.sh ]; then
    printf "\n\nERROR: Run this command from Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

if [ "$#" -lt 2 ]; then
    printf "Usage: %s <old.ns> <new.ns> [<old2.ns> <new2.ns> ...]\n" "$0"
    printf "       %s --since <rev> <file.ns> [file.ns ...]\n" "$0"
    exit 1
fi

if [ ! -f "${PRIMORDIALSOUP}/out/snapshots/NewspeakAttachmentDiffApp.vfuel" ]; then
    printf "ERROR: NewspeakAttachmentDiffApp.vfuel not found.\n"
    printf "Build it with: cd %s/tool && ./build.sh\n\n" "${NEWSPEAK}"
    exit 1
fi

TMP_DIR="$(mktemp -d)"
TMP_OUT="$(mktemp)"
trap 'rm -rf "$TMP_DIR" "$TMP_OUT"' EXIT

ARGS=""
if [ "$1" = "--since" ]; then
    REV="$2"
    shift 2
    for f in "$@"; do
        [ -f "$f" ] || { printf "ERROR: File not found: %s\n" "$f"; exit 1; }
        DIR="$(cd "$(dirname "$f")" && pwd)"
        BASE="$(basename "$f")"
        # Path as git knows it, so the extract works from any subdirectory.
        REL="$(cd "$DIR" && git ls-files --full-name "$BASE")"
        if [ -z "$REL" ]; then
            printf "ERROR: not tracked by git: %s\n" "$f"
            exit 1
        fi
        OLD="$TMP_DIR/$(echo "$REL" | tr '/' '_').old"
        (cd "$DIR" && git show "$REV:$REL") > "$OLD" 2>/dev/null || {
            printf "SKIP %s: does not exist at %s\n" "$REL" "$REV"
            continue
        }
        ARGS="$ARGS $OLD $DIR/$BASE"
    done
else
    for f in "$@"; do
        [ -f "$f" ] || { printf "ERROR: File not found: %s\n" "$f"; exit 1; }
        ARGS="$ARGS $(cd "$(dirname "$f")" && pwd)/$(basename "$f")"
    done
fi

[ -n "$ARGS" ] || exit 0

# shellcheck disable=SC2086
${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
    ${PRIMORDIALSOUP}/out/snapshots/NewspeakAttachmentDiffApp.vfuel \
    $ARGS > "$TMP_OUT" 2>&1

cat "$TMP_OUT"

if grep -qE '^(PURE|MIXED|ERROR)' "$TMP_OUT"; then
    exit 1
fi
exit 0
