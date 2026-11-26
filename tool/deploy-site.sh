#!/bin/sh
# Copyright (c) 2026-2027, Gilad Bracha. All rights reserved. Use of this source
# code is governed by a BSD-style license that can be found in the LICENSE file.
#
# Publishes a site of Newspeak documents into a directory, usually a GitHub
# Pages checkout (EURASIA_WEB_PUBLISHING_DESIGN_2026-11-23.md, section 2.4):
#
#   tool/deploy-site.sh TARGET [BUNDLE]
#
# 1. If BUNDLE is given (a deploy.<Root>.zip from Deploy for Web, in either
#    IDE), unzips its pages, document zips, images and index.html into TARGET.
# 2. Builds the Eurasia site runtime into TARGET with
#    eurasia/scripts/site-runtime.sh: the VM, the viewer image, deploy-boot.js,
#    eurasia-viewer.html, the libraries and the images. It is built from the
#    checkouts, not copied from out/; see eurasia/BUILDING.md for what that
#    needs. It comes after the bundle, so the runtime's deploy-boot.js wins
#    over the copy the bundle carries.
# 3. While psoup is still deploy-boot.js's default (or a fallback), the site
#    also needs psoup's runtime (AmpleforthViewer.vfuel, primordialsoup.*). A
#    site that has it keeps it as it is. To refresh it, set PSOUP_RUNTIME to a
#    directory that holds a built one (newspeak's out/ after tool/build.sh).
#
# 4. A site with a webIDE/ (newspeaklanguage.org's PWA) also gets the Eurasia
#    IDE (site-runtime.sh --with-ide): webIDE/eurasia.html is eurasia-ide.html
#    with <base href="/">, so that it lies within the service worker's scope
#    (webIDE/) while what it loads comes from the site's root, as psoup's
#    webIDE/index.html does, and it registers the service worker itself (one
#    may never open psoup's page); webIDE/index.html?eurasia opens it. The service
#    worker answers from its cache first, so an installed PWA sees a new
#    runtime only when sw.js changes: pwaVersion in webIDE/sw.js is bumped.
#
# It does not commit or push: review the result in TARGET, then commit there.
#
# The eurasia checkout is the one beside newspeak's, or $EURASIA.
set -eu
test $# -ge 1 -a $# -le 2 || { echo "usage: $0 TARGET [deploy.<Root>.zip]" >&2; exit 2; }
test -d "$1" || { echo "no such directory: $1" >&2; exit 1; }
TARGET=$(cd "$1" && pwd)
BUNDLE=${2:-}
NEWSPEAK=$(cd "$(dirname "$0")/.." && pwd)
EURASIA=$(cd "${EURASIA:-$NEWSPEAK/../eurasia}" && pwd)
export NEWSPEAK

if [ -n "$BUNDLE" ]; then
  test -f "$BUNDLE" || { echo "no such bundle: $BUNDLE" >&2; exit 1; }
  echo "== the bundle: $BUNDLE"
  unzip -o -q "$BUNDLE" -d "$TARGET"
  echo "$(unzip -Z1 "$BUNDLE" | grep -c '\.html$') pages"
fi

if [ -d "$TARGET/webIDE" ]; then
  echo "== the Eurasia site runtime, with the IDE (eurasia/scripts/site-runtime.sh --with-ide)"
  "$EURASIA/scripts/site-runtime.sh" --with-ide "$TARGET"
  echo "== the webIDE: webIDE/eurasia.html, and pwaVersion in webIDE/sw.js"
  awk '{ print } /<meta charset="utf-8">/ && !done { print "<base href=\"/\">"; print "<script>if (\"serviceWorker\" in navigator) navigator.serviceWorker.register(\"/webIDE/sw.js\");</script>"; done = 1 }' \
    "$TARGET/eurasia-ide.html" > "$TARGET/webIDE/eurasia.html"
  grep -q '<base href="/">' "$TARGET/webIDE/eurasia.html" || { echo "no <base> in webIDE/eurasia.html" >&2; exit 1; }
  if [ -f "$TARGET/webIDE/sw.js" ]; then
    awk '/^const pwaVersion = [0-9]+;/ { sub(/[0-9]+/, $4 + 1) } { print }' \
      "$TARGET/webIDE/sw.js" > "$TARGET/webIDE/sw.js.new" && mv "$TARGET/webIDE/sw.js.new" "$TARGET/webIDE/sw.js"
    grep '^const pwaVersion' "$TARGET/webIDE/sw.js"
  fi
else
  echo "== the Eurasia site runtime (eurasia/scripts/site-runtime.sh)"
  "$EURASIA/scripts/site-runtime.sh" "$TARGET"
fi

if [ -n "${PSOUP_RUNTIME:-}" ]; then
  echo "== psoup's runtime, from $PSOUP_RUNTIME"
  for f in AmpleforthViewer.vfuel primordialsoup.html primordialsoup.js primordialsoup.wasm; do
    cp "$PSOUP_RUNTIME/$f" "$TARGET/"
  done
elif [ ! -f "$TARGET/AmpleforthViewer.vfuel" ]; then
  echo "WARNING: $TARGET has no psoup runtime, which deploy-boot.js still boots by default;"
  echo "         set PSOUP_RUNTIME (newspeak's out/, built) to add it."
fi

echo "Deployed into $TARGET. Review it there (?eurasia boots Eurasia), then commit."
