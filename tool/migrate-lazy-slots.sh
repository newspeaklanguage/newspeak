#!/bin/sh
# migrate-lazy-slots.sh
#
# Copies both Newspeak source trees to a FRESH directory and runs the lazy-slot
# migration on the copy, in place. The working tree is never touched.
#
#   - reads every *.ns in the copy, migrates hand-written lazy-init accessors
#     (n_slot isNil ifTrue: [n_slot:: e]. ^n_slot) to proper `lazy n = e.` slots,
#   - writes changed files back into the copy,
#   - aggregates a report (per-file events + a summary with skip-reason tallies,
#     including the #slotWrittenElsewhere count that quantifies the immutable-only
#     assumption).
#
# Usage: ./migrate-lazy-slots.sh [dest-dir]
#   dest-dir defaults to <newspeak>/../lazy-slot-migration
#
# Requires the prebuilt NewspeakLazySlotMigrationApp.vfuel (see build-migration-app.sh).

if [ ! -f ./newspeak_util.sh ]; then
    printf "\nERROR: run from the Newspeak 'tool' directory.\n\n"
    exit 1
fi
. ./newspeak_util.sh
. ./newspeak_env.sh
check_dir_is_tool

PSOUP="${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup"
APP="${PRIMORDIALSOUP}/out/snapshots/NewspeakLazySlotMigrationApp.vfuel"
DEST="${1:-${NEWSPEAK}/../lazy-slot-migration}"

if [ ! -f "$APP" ]; then
    printf "\nERROR: %s not found. Build it first:\n  ./build-migration-app.sh\n\n" "$APP"
    exit 1
fi
if [ ! -f "$PSOUP" ]; then
    printf "\nERROR: primordialsoup VM not found at %s\n\n" "$PSOUP"
    exit 1
fi

printf "Migrating into a fresh copy at: %s\n" "$DEST"
rm -rf "$DEST"
mkdir -p "$DEST/newspeak" "$DEST/primordialsoup-newspeak"
cp "${NEWSPEAK}"/*.ns "$DEST/newspeak/"
cp "${PRIMORDIALSOUP}/newspeak"/*.ns "$DEST/primordialsoup-newspeak/"

REPORT="$DEST/MIGRATION_REPORT.txt"
: > "$REPORT"

n=0
for f in "$DEST/newspeak"/*.ns "$DEST/primordialsoup-newspeak"/*.ns; do
    n=$((n + 1))
    "$PSOUP" "$APP" "$f" >> "$REPORT" 2>&1
done
printf "Processed %d files.\n\n" "$n"

printf "================ MIGRATION SUMMARY ================\n"
awk '
/^FILE /{ files++;
          split($3,a,"="); t=a[2];
          split($4,b,"="); s=b[2];
          if (t>0) changed++;
          totT+=t; totS+=s }
/^S /{ reason[$3]++ }
/^ERR /{ errs++ }
END{
  printf "files scanned    : %d\n", files;
  printf "files changed    : %d\n", changed;
  printf "accessors migrated: %d\n", totT;
  printf "accessors skipped : %d\n", totS;
  printf "errors           : %d\n", errs+0;
  printf "\nskips by reason:\n";
  for (r in reason) printf "  %5d  %s\n", reason[r], r;
}' "$REPORT"
printf "==================================================\n"
printf "Full per-file report: %s\n" "$REPORT"
printf "Review the migrated copy, then diff against the originals, e.g.:\n"
printf "  diff -ru %s %s/newspeak\n" "$NEWSPEAK" "$DEST"
