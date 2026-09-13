#!/bin/sh
# Build ONLY out/CroquetHopscotchWebIDE-TEST.vfuel from the current working
# tree (uncommitted edits included), without emscripten and without touching
# the live artifacts. Mirrors build.sh steps 4e (BuildInfo stamp), 6-7
# (staging: psoup sources first, repo sources over them) and 8 (compile), in a
# fresh scratch directory each time so nothing stale is captured.
#
#   cd tool && ./build-croquet-test-vfuel.sh
#
# Then, e.g.:
#   NS_SUFFIX=-TEST <emsdk node 22> croquet-probes/setup-latejoin-probe.js
if [ ! -f ./newspeak_util.sh ]; then
    printf "\nERROR: Run this command from the Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_env.sh
set -e

STAGE=${NEWSPEAK}/scratch/croquet-test-stage
rm -rf "$STAGE" && mkdir -p "$STAGE"
cp "${PRIMORDIALSOUP}"/newspeak/*.ns "$STAGE"/
cp "${NEWSPEAK}"/*.ns "${NEWSPEAK}"/*.png "$STAGE"/

# Stamp BuildInfo in the STAGE only; the tree's placeholder is left alone.
IDE_SHA=$(git -C "${NEWSPEAK}" rev-parse --short HEAD 2>/dev/null || echo unknown)
IDE_DATE=$(git -C "${NEWSPEAK}" show -s --format=%cs HEAD 2>/dev/null || echo unknown)
VM_SHA=$(git -C "${PRIMORDIALSOUP}" rev-parse --short HEAD 2>/dev/null || echo unknown)
test -n "$(git -C "${NEWSPEAK}" status --porcelain --untracked-files=no 2>/dev/null)" && DIRTY=' (dirty)' || DIRTY=''
BUILT=$(date -u +%Y-%m-%dT%H:%MZ)
cat > "$STAGE/BuildInfo.ns" <<NSEOF
Newspeak3
'Root'
class BuildInfo packageUsing: manifest = Object new (
	(* Build/version stamp -- GENERATED for a TEST vfuel by
	tool/build-croquet-test-vfuel.sh. *)
) (
) : (
	public version = (
		^'${IDE_SHA} ${IDE_DATE}, VM ${VM_SHA}, built ${BUILT}${DIRTY} TEST'
	)
)
NSEOF

cd "$STAGE"
"${PRIMORDIALSOUP}"/out/ReleaseX64/primordialsoup \
    "${PRIMORDIALSOUP}"/out/snapshots/WebCompiler.vfuel \
    ./*.ns \
    ./*.png \
    RuntimeForCroquet HopscotchWebIDE "${NEWSPEAK}"/out/CroquetHopscotchWebIDE-TEST.vfuel

ls -la "${NEWSPEAK}"/out/CroquetHopscotchWebIDE-TEST.vfuel
