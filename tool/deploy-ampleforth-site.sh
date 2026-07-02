#!/bin/sh

# Description:
#
#   Publishes an Ampleforth "site bundle" (deploy.<Root>.zip, produced by the
#   IDE's "Deploy for Web" menu item) to a target directory: it rsyncs the shared
#   one-time runtime from out/, then unzips the bundle's pages + document zips +
#   deploy-boot.js into the target. Git is left to you (review, then commit/push
#   in the target repo) — matching the other deploy-*.sh scripts.
#
#   The runtime is what primordialsoup.html + deploy-boot.js need at run time:
#   AmpleforthViewer.vfuel, primordialsoup.{html,js,wasm}, jszip.min.js,
#   vendor/*.js, CodeMirror/, deploy-boot.js, and the .png assets (eye background).
#
# Arguments:
#   1. <target-dir>   where to publish. A GitHub Pages checkout
#                     (e.g. ~/newspeaklanguage.github.io), or ../out to stage a
#                     LOCAL test (runtime is already there — just serve out/ at :8080).
#   2. <bundle.zip>   the deploy.<Root>.zip. Optional; defaults to the newest
#                     ~/Downloads/deploy.*.zip.
#
# Usage examples:
#   cd tool
#   ./deploy-ampleforth-site.sh ../out                      # local test into out/
#   ./deploy-ampleforth-site.sh ~/newspeaklanguage.github.io ~/Downloads/deploy.Home.zip

set -e
if [ ! -f ./newspeak_util.sh ]; then
  printf "\nRun this script from the Newspeak 'tool' directory.\n"; exit 1
fi

NEWSPEAK_OUT="${NEWSPEAK:-$(cd .. && pwd)}/out"
TARGET="$1"
BUNDLE="$2"

if [ -z "$TARGET" ]; then
  echo "Usage: ./deploy-ampleforth-site.sh <target-dir> [<bundle.zip>]"; exit 1
fi
if [ ! -d "$TARGET" ];       then echo "Missing target dir:   $TARGET";        exit 1; fi
if [ ! -d "$NEWSPEAK_OUT" ]; then echo "Missing build output: $NEWSPEAK_OUT";  exit 1; fi

# Default bundle = newest deploy.*.zip in ~/Downloads
if [ -z "$BUNDLE" ]; then
  BUNDLE=$(ls -t "$HOME/Downloads"/deploy.*.zip 2>/dev/null | head -1 || true)
fi
if [ -z "$BUNDLE" ] || [ ! -f "$BUNDLE" ]; then
  echo "No site bundle found. Pass deploy.<Root>.zip as the 2nd argument"
  echo "(looked for the newest ~/Downloads/deploy.*.zip)."; exit 1
fi

echo "Runtime : $NEWSPEAK_OUT  ->  $TARGET"
echo "Bundle  : $BUNDLE"
echo ""

# 1. One-time shared runtime (rsync -t: only when newer).
rsync -t "$NEWSPEAK_OUT/AmpleforthViewer.vfuel" "$TARGET/"
rsync -t "$NEWSPEAK_OUT/primordialsoup.html"    "$TARGET/"
rsync -t "$NEWSPEAK_OUT/primordialsoup.js"      "$TARGET/"
rsync -t "$NEWSPEAK_OUT/primordialsoup.wasm"    "$TARGET/"
rsync -t "$NEWSPEAK_OUT/deploy-boot.js"         "$TARGET/"
rsync -t "$NEWSPEAK_OUT/jszip.min.js"           "$TARGET/"
rsync -t "$NEWSPEAK_OUT"/*.png                  "$TARGET/" 2>/dev/null || true
if [ -d "$NEWSPEAK_OUT/vendor" ]; then
  mkdir -p "$TARGET/vendor"; rsync -t "$NEWSPEAK_OUT/vendor/"*.js "$TARGET/vendor/"
fi
if [ -d "$NEWSPEAK_OUT/CodeMirror" ]; then
  rsync -rt "$NEWSPEAK_OUT/CodeMirror/" "$TARGET/CodeMirror/"
fi

# 2. The site bundle (flat zip: index.html, <Name>.html, <Name>.zip, deploy-boot.js).
unzip -o "$BUNDLE" -d "$TARGET" >/dev/null
echo "Unzipped site pages + document zips into $TARGET"

echo ""
echo "Deployed to $TARGET."
echo "  Entry point: index.html"
echo "  Review, then commit/push in $TARGET (git is intentionally not run here)."
