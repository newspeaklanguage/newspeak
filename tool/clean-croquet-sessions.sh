#!/bin/sh
# Clean out old Newspeak-on-Croquet session state.
#
# Usage (from the tool directory):
#     ./clean-croquet-sessions.sh                    # dry run: report what exists
#     ./clean-croquet-sessions.sh --prune [DAYS]     # delete session dirs older than DAYS (default 7)
#     ./clean-croquet-sessions.sh --all              # delete ALL session dirs
#     ./clean-croquet-sessions.sh --restart-reflector [--prune|--all]
#
# Session state lives in FOUR places:
#   1. The reflector's MEMORY (--storage=none): restarting the reflector erases
#      every session's replayable history. That is the only way to truly retire
#      a session id whose stored event history has gone bad.
#   2. The file server tree out/files/apps/<appId>/<persistentId>/: Data-API
#      blobs -- dropped files AND, since the large-payload detour, every
#      keystroke made in a large editor -- and each session's persisted
#      snapshot under save/. Grows without bound; this script prunes it.
#      persistentIds are hashes, so pruning is by appId/age, never by session
#      name.
#   3. The reflector's own PERSISTENCE RECORDS, persist/<appId>/<id>.json in
#      the reflector checkout (CROQUET_LOCAL_PERSIST overrides). Each one says
#      WHERE a session's snapshot lives -- a url into (2). These must be
#      removed with the blobs they name: a record left pointing at a deleted
#      snapshot makes the reflector tell every joining client to fetch a file
#      that is gone, the fetch 404s, Session.join rejects, and Newspeak never
#      starts. Deleting (2) alone did exactly that on 2026-09-21, which is why
#      this script now handles both together.
#   4. Browser localStorage (per browser, per origin): sessionId/appId/pwd/
#      apiKey persisted by getURIParam, the per-session app-session:* objects,
#      and the IDE backup state. This script cannot reach those; clear site
#      data for localhost:8080 in the browser.
#
# Pruning blobs out from under a LIVE session breaks its detoured-payload
# fetches and file history, so deletion is refused while a reflector is
# listening unless you pass --force (or combine with --restart-reflector,
# which makes it safe by construction: no reflector, no live sessions).
#
# out/files/deploy is deploy staging, not session data; it is never touched.

set -e

if [ ! -f ./newspeak_util.sh ]; then
    printf "\nERROR: Run this command from the Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_env.sh

PORT=9090
APPS="${NEWSPEAK}/out/files/apps"
REFLECTOR="${CROQUET_REFLECTOR:-${NEWSPEAK}/../croquet/packages/reflector}"
# Where the reflector keeps its persistence records. Mirrors reflector.js:
# CROQUET_LOCAL_PERSIST, else 'persist' under its working directory, which is
# the checkout because that is where this script starts it.
PERSIST="${CROQUET_LOCAL_PERSIST:-${REFLECTOR}/persist}"

MODE=report
DAYS=7
RESTART=no
FORCE=no
while [ $# -gt 0 ]; do
    case "$1" in
        --prune)
            MODE=prune
            case "${2:-}" in
                ''|--*) ;;
                *) DAYS="$2"; shift ;;
            esac
            ;;
        --all) MODE=all ;;
        --restart-reflector) RESTART=yes ;;
        --force) FORCE=yes ;;
        *)
            printf "Unknown argument: %s\n" "$1"
            exit 1
            ;;
    esac
    shift
done

# A record is DANGLING when the blobs it names are gone: persist/<app>/<id>.json
# with no apps/<app>/<id>/ beside it. Those are the ones that break a join.
dangling_records() {
    [ -d "${PERSIST}" ] || return 0
    find "${PERSIST}" -mindepth 2 -maxdepth 2 -name '*.json' 2>/dev/null | while read -r rec; do
        app="$(basename "$(dirname "${rec}")")"
        id="$(basename "${rec}" .json)"
        [ -d "${APPS}/${app}/${id}" ] || printf '%s\n' "${rec}"
    done
}

count_records() {
    [ -d "${PERSIST}" ] || { printf '0'; return; }
    find "${PERSIST}" -mindepth 2 -maxdepth 2 -name '*.json' 2>/dev/null | wc -l | tr -d ' '
}

reflector_pids() {
    lsof -nP -iTCP:"${PORT}" -sTCP:LISTEN -t 2>/dev/null || true
}

if [ "${RESTART}" = yes ]; then
    PIDS="$(reflector_pids)"
    if [ -n "${PIDS}" ]; then
        printf "Stopping reflector (pid %s)...\n" "${PIDS}"
        kill ${PIDS} 2>/dev/null || true
        sleep 1
    else
        printf "No reflector listening on %s.\n" "${PORT}"
    fi
    if [ ! -f "${REFLECTOR}/reflector.js" ]; then
        printf "ERROR: reflector not found at %s -- not restarting.\n" "${REFLECTOR}"
        exit 1
    fi
    # Emscripten's node, not the system one (broken node@12; see run-croquet-reflector.sh).
    NODE_BIN="$(ls -d "${EMSDK}"/node/*/bin 2>/dev/null | tail -1)"
    if [ -n "${NODE_BIN}" ] && [ -x "${NODE_BIN}/node" ]; then
        PATH="${NODE_BIN}:${PATH}"
        export PATH
    fi
    printf "Starting reflector (log: %s/reflector.log)...\n" "${REFLECTOR}"
    ( cd "${REFLECTOR}" && nohup node reflector.js --standalone --storage=none --no-loglatency > reflector.log 2>&1 & )
    sleep 1
    if [ -n "$(reflector_pids)" ]; then
        printf "Reflector restarted; all previous in-memory session state is gone.\n"
    else
        printf "WARNING: reflector did not come up; check %s/reflector.log\n" "${REFLECTOR}"
    fi
fi

if [ ! -d "${APPS}" ]; then
    printf "No session data: %s does not exist.\n" "${APPS}"
    exit 0
fi

case "${MODE}" in
    report)
        printf "Session blob usage under %s:\n\n" "${APPS}"
        du -sh "${APPS}" 2>/dev/null
        printf "\nPer appId:\n"
        du -sh "${APPS}"/* 2>/dev/null || printf "  (none)\n"
        printf "\nSession directories older than %s days (would be removed by --prune %s):\n" "${DAYS}" "${DAYS}"
        find "${APPS}" -mindepth 2 -maxdepth 2 -type d -mtime +"${DAYS}" -print 2>/dev/null || true
        printf "\nReflector persistence records in %s: %s\n" "${PERSIST}" "$(count_records)"
        DANGLING="$(dangling_records | wc -l | tr -d ' ')"
        if [ "${DANGLING}" -gt 0 ]; then
            printf "  %s of them DANGLING -- they name snapshots that no longer exist.\n" "${DANGLING}"
            printf "  A session with a dangling record cannot start: the reflector sends the\n"
            printf "  client to a missing file, the fetch 404s and Session.join rejects.\n"
            printf "  --prune and --all both remove these.\n"
        fi
        if [ -n "$(reflector_pids)" ]; then
            printf "\nReflector is RUNNING on %s (pid %s); its in-memory sessions survive pruning\nbut a pruned live session loses its stored blobs. Combine with\n--restart-reflector, or pass --force, to prune anyway.\n" "${PORT}" "$(reflector_pids)"
        else
            printf "\nNo reflector on %s; pruning is safe.\n" "${PORT}"
        fi
        printf "\nDry run only. Use --prune [DAYS] or --all to delete.\n"
        ;;
    prune|all)
        if [ -n "$(reflector_pids)" ] && [ "${RESTART}" = no ] && [ "${FORCE}" = no ]; then
            printf "Refusing to delete while a reflector is listening on %s:\nlive sessions may reference these blobs. Combine with --restart-reflector,\nor pass --force if you are sure no session you care about is live.\n" "${PORT}"
            exit 1
        fi
        if [ "${MODE}" = all ]; then
            printf "Removing ALL session directories under %s...\n" "${APPS}"
            find "${APPS}" -mindepth 1 -maxdepth 1 -type d -print -exec rm -rf {} +
        else
            printf "Removing session directories older than %s days...\n" "${DAYS}"
            find "${APPS}" -mindepth 2 -maxdepth 2 -type d -mtime +"${DAYS}" -print -exec rm -rf {} +
            # drop appId dirs left empty by the prune
            find "${APPS}" -mindepth 1 -maxdepth 1 -type d -empty -print -delete
        fi
        # The reflector's records must go with the blobs they name, or a join
        # is sent to a file that no longer exists. Computed AFTER the deletion
        # above, so every record whose snapshot just went is caught too.
        RECS="$(dangling_records)"
        if [ -n "${RECS}" ]; then
            printf "Removing %s reflector persistence record(s) left pointing at deleted snapshots...\n" \
                "$(printf '%s\n' "${RECS}" | wc -l | tr -d ' ')"
            printf '%s\n' "${RECS}" | while read -r rec; do rm -f "${rec}"; done
            find "${PERSIST}" -mindepth 1 -maxdepth 1 -type d -empty -print -delete 2>/dev/null || true
        else
            printf "No dangling reflector persistence records.\n"
        fi
        printf "Done. Remaining:\n"
        du -sh "${APPS}" 2>/dev/null || true
        ;;
esac
