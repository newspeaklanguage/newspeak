#!/bin/sh
# NEGATIVE CONTROL for croquet-probes/ampleforth-sync-probe.js.
#
# Builds out/CroquetHopscotchWebIDE-BUG.vfuel: the current tree, with the
# 2026-09-19 Ampleforth live-view fix UNDONE in the staged copy only. The
# working tree is never modified - Gilad's IDE saves land in it, so a build
# that edited it in place and restored it afterwards could silently eat one.
#
# The undo is the single line the fix added: the live view's write back to the
# raw pane is tagged 'liveview' (which isUserOrigin: accepts) instead of going
# out as a plain setValue (which it rejects, so nothing is published at all).
#
#   cd tool && ./build-bugged-test-vfuel.sh
#   NS_SNAPSHOT=CroquetHopscotchWebIDE-BUG.vfuel croquet-probes/run.sh ampleforth-sync-probe.js
#
# Expect the probe to FAIL its first assertion (LIVE-VIEW TYPING RECORDS
# EVENTS). A probe that passes here is not testing what it claims to.
if [ ! -f ./newspeak_util.sh ]; then
    printf "\nERROR: Run this command from the Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_env.sh
set -e

STAGE=${NEWSPEAK}/scratch/croquet-bug-stage
rm -rf "$STAGE" && mkdir -p "$STAGE"
cp "${PRIMORDIALSOUP}"/newspeak/*.ns "$STAGE"/
cp "${NEWSPEAK}"/*.ns "${NEWSPEAK}"/*.png "$STAGE"/

# Undo the fix in the staged copy. Fail loudly rather than build a snapshot
# that is quietly identical to the good one - that would turn the control
# into a second positive run and prove nothing.
BEFORE=$(grep -c "cm text: newHTML origin: 'liveview'" "$STAGE"/Documents.ns || true)
if [ "$BEFORE" != "1" ]; then
    printf "\nERROR: expected exactly 1 'liveview' write in Documents.ns, found %s.\n" "$BEFORE"
    printf "The fix moved; update this script rather than trusting its output.\n\n"
    exit 1
fi
sed -i '' "s/cm text: newHTML origin: 'liveview'/cm text: newHTML/" "$STAGE"/Documents.ns
grep -q "cm text: newHTML\." "$STAGE"/Documents.ns || { echo "ERROR: revert did not apply"; exit 1; }
echo "staged Documents.ns reverted to the pre-fix (unpublished) live-view write"

cat > "$STAGE/BuildInfo.ns" <<NSEOF
Newspeak3
'Root'
class BuildInfo packageUsing: manifest = Object new (
	(* Build/version stamp -- GENERATED for a NEGATIVE-CONTROL vfuel by
	tool/build-bugged-test-vfuel.sh. Ampleforth live-view fix REVERTED. *)
) (
) : (
	public version = (
		^'LIVEVIEW-BUG negative control, built $(date -u +%Y-%m-%dT%H:%MZ)'
	)
)
NSEOF

cd "$STAGE"
"${PRIMORDIALSOUP}"/out/ReleaseX64/primordialsoup \
    "${PRIMORDIALSOUP}"/out/snapshots/WebCompiler.vfuel \
    ./*.ns \
    ./*.png \
    RuntimeForCroquet HopscotchWebIDE "${NEWSPEAK}"/out/CroquetHopscotchWebIDE-BUG.vfuel

ls -la "${NEWSPEAK}"/out/CroquetHopscotchWebIDE-BUG.vfuel
