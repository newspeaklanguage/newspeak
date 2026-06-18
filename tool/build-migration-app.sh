#!/bin/sh
# build-migration-app.sh
#
# Builds NewspeakLazySlotMigrationApp.vfuel — the command-line driver that reads a
# .ns file, migrates hand-written lazy-init accessors to `lazy` slots, and writes
# the result back. Deps (NewspeakASTs, NewspeakPredictiveParsing, MetadataParsing)
# come from the primordialsoup/newspeak glob; the engine + app are added explicitly.

if [ ! -f ./newspeak_util.sh ]; then
    printf "\nERROR: run from the Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_util.sh
. ./newspeak_env.sh
check_dir_is_tool

PSOUP="${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup"
WEBCOMPILER="${PRIMORDIALSOUP}/out/snapshots/WebCompiler.vfuel"
OUT="${PRIMORDIALSOUP}/out/snapshots/NewspeakLazySlotMigrationApp.vfuel"

"$PSOUP" "$WEBCOMPILER" \
    "${PRIMORDIALSOUP}"/newspeak/*.ns \
    "${NEWSPEAK}/NewspeakLazySlotMigration.ns" \
    "${NEWSPEAK}/NewspeakLazySlotMigrationApp.ns" \
    RuntimeWithMirrorsForPrimordialSoup NewspeakLazySlotMigrationApp \
    "$OUT"

if [ -f "$OUT" ]; then
    printf "Built %s\n" "$OUT"
else
    printf "ERROR: build failed; %s not produced.\n" "$OUT"
    exit 1
fi
