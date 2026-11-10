#!/bin/sh
# Build ONLY the two TEST snapshots of the IDE from the current working tree
# (uncommitted edits included), without emscripten and without touching the
# live artifacts:
#   out/CroquetHopscotchWebIDE-TEST.vfuel   the Croquet IDE, for the psoup probes
#   out/HopscotchWebIDE-TEST.vfuel          the plain IDE, which
#       croquet-probes/deploy-driver2.js boots headlessly to package the
#       Croquet JS deploy (out/CroquetJSIDE-TEST.*) - so that deploy is only as
#       current as this snapshot. Mirrors build.sh steps 4e (BuildInfo stamp), 6-7
# (staging: psoup sources first, repo sources over them) and 8 (compile), in a
# fresh scratch directory each time so nothing stale is captured.
#
#   cd tool && ./build-croquet-test-vfuel.sh [OVERLAY_DIR]
#
# OVERLAY_DIR, if given, holds .ns files copied over the staged sources last:
# instrumented variants for a probe run, without touching the working tree.
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
if [ -n "$1" ]; then
    echo "Overlaying $(ls "$1"/*.ns | wc -l | tr -d ' ') file(s) from $1"
    cp "$1"/*.ns "$STAGE"/
fi

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
	tool/build-croquet-test-vfuel.sh. Must answer everything the tracked
	placeholder does: version and dirty describe the SOURCES, builtAt is when
	this artifact was built and is what platform buildTime answers. Answering
	only version made every TEST image die during startup with
	'BuildInfo class doesNotUnderstand: #builtAt' (2026-09-21). *)
) (
) : (
	public builtAt = (
		^'${BUILT}'
	)
	public dirty = (
		^'${DIRTY}'
	)
	public version = (
		^'${IDE_SHA} ${IDE_DATE}, VM ${VM_SHA} TEST'
	)
)
NSEOF

cd "$STAGE"

# The compile below globs ./*.ns, so two sources declaring the same top-level
# class silently replace one another. See tool/check-duplicate-modules.py.
python3 "${NEWSPEAK}"/tool/check-duplicate-modules.py . || exit 1

"${PRIMORDIALSOUP}"/out/ReleaseX64/primordialsoup \
    "${PRIMORDIALSOUP}"/out/snapshots/WebCompiler.vfuel \
    ./*.ns \
    ./*.png \
    RuntimeForCroquet HopscotchWebIDE "${NEWSPEAK}"/out/CroquetHopscotchWebIDE-TEST.vfuel \
    RuntimeForHopscotchForHTML HopscotchWebIDE "${NEWSPEAK}"/out/HopscotchWebIDE-TEST.vfuel

ls -la "${NEWSPEAK}"/out/CroquetHopscotchWebIDE-TEST.vfuel "${NEWSPEAK}"/out/HopscotchWebIDE-TEST.vfuel
