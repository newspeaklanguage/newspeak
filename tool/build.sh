#!/bin/sh -x

# 1. Read utility functions and ensure (heuristically) directory is tool
if [ ! -f ./newspeak_util.sh ]; then printf "\n\nERROR: Run this command from Newspeak 'tool' directory. Current directory=%s. Exiting.\n\n" "$PWD"; exit 1; fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

# 2. If additional arguments are provided, they are assumed to be 3-tuples to compile.
# For example, if users want to build vfuel for 'CheckedItemApp.ns',
# they could provide build arguments as follows:
#   ./build.sh RuntimeForHopscotchForHTML CheckedItemApp CheckedItemApp.vfuel
additionalNs="$*"

# 3. Setup the emscripten environment needed to build primordialsoup.
# Emscripten must be installed in the $EMSDK directory, set in 'newspeak_env.sh'.
# To install emscripten and configure the version to use,
#   see https://github.com/newspeaklanguage/primordialsoup/blob/master/docs/building.md
# Emscripten 'latest' and '2.0.0' are tested
# In summary, to configure emscripten version:
#   - cd $EMSDK
#   - ./emsdk install  latest # or 2.0.0 instead of 'latest'
#   - ./emsdk activate latest # or 2.0.0 instead of 'latest'
# shellcheck source=/dev/null
. ${EMSDK}/emsdk_env.sh

# 4. Build primordialsoup from it's directory.
cd ${PRIMORDIALSOUP} || exit 1
./build os=emscripten arch=wasm

# 4-croquet. Build the Croquet variant of the VM: the same VM linked with
# meta/croquet-post.js (Croquet model/view + session join) instead of
# meta/custom-post.js, producing croquetpsoup.{html,js,wasm}. The script saves and
# restores the standard build and SConstruct around itself, and refuses to emit a
# croquetpsoup.js with no Croquet in it. MUST run after the standard build above,
# which it relies on having produced the files it saves.
./build-croquet.sh os=emscripten arch=wasm

# 4a. Build NewspeakParser.vfuel for parse-validate.sh script
./out/ReleaseX64/primordialsoup \
  ./out/snapshots/WebCompiler.vfuel \
  ./newspeak/*.ns \
  ${NEWSPEAK}/NewspeakParser.ns \
  RuntimeWithMirrorsForPrimordialSoup NewspeakParser ./out/snapshots/NewspeakParser.vfuel

# 4b. Build NewspeakTestRunner.vfuel for run-tests.sh script
./out/ReleaseX64/primordialsoup \
  ./out/snapshots/WebCompiler.vfuel \
  ./newspeak/*.ns \
  ${NEWSPEAK}/NewspeakTestRunner.ns \
  RuntimeWithMirrorsForPrimordialSoup NewspeakTestRunner ./out/snapshots/NewspeakTestRunner.vfuel

# 4c. Build NewspeakPrettyPrintApp.vfuel for tool/pretty-print.sh script
./out/ReleaseX64/primordialsoup \
  ./out/snapshots/WebCompiler.vfuel \
  ./newspeak/*.ns \
  ${NEWSPEAK}/NewspeakASTs.ns \
  ${NEWSPEAK}/NewspeakPrettyPrinter.ns \
  ${NEWSPEAK}/NewspeakPrettyPrintApp.ns \
  RuntimeWithMirrorsForPrimordialSoup NewspeakPrettyPrintApp ./out/snapshots/NewspeakPrettyPrintApp.vfuel

# 4d. Build NewspeakRoundTripCheckApp.vfuel for tool/round-trip-check.sh script
./out/ReleaseX64/primordialsoup \
  ./out/snapshots/WebCompiler.vfuel \
  ./newspeak/*.ns \
  ${NEWSPEAK}/NewspeakASTs.ns \
  ${NEWSPEAK}/NewspeakPrettyPrinter.ns \
  ${NEWSPEAK}/NewspeakRoundTripCheckApp.ns \
  RuntimeWithMirrorsForPrimordialSoup NewspeakRoundTripCheckApp ./out/snapshots/NewspeakRoundTripCheckApp.vfuel

# 4e. Build NewspeakAttachmentDiffApp.vfuel for tool/attachment-diff.sh script
./out/ReleaseX64/primordialsoup \
  ./out/snapshots/WebCompiler.vfuel \
  ./newspeak/*.ns \
  ${NEWSPEAK}/NewspeakASTs.ns \
  ${NEWSPEAK}/NewspeakPrettyPrinter.ns \
  ${NEWSPEAK}/NewspeakRoundTripCheckApp.ns \
  ${NEWSPEAK}/NewspeakAttachmentDiffApp.ns \
  RuntimeWithMirrorsForPrimordialSoup NewspeakAttachmentDiffApp ./out/snapshots/NewspeakAttachmentDiffApp.vfuel

# Back to 'newspeak'.
cd ${NEWSPEAK} || exit 1

# 4e. Work out this build's version stamp. It is WRITTEN later, in step 7c,
#     straight into out/ where the compiler reads it -- the committed
#     BuildInfo.ns is a 'development build' placeholder and is never touched.
#     It used to be written here, over the tracked file, and restored with a
#     `git checkout` after the compile. That left the tracked file dirty for the
#     whole build, and anything running git checkout/stash/branch in that window
#     replaced the stamp with the placeholder before the compile read it -- so a
#     deployed vfuel would claim to be a development build, with nothing saying
#     why, since the restore's own errors were discarded (2026-09-20).
IDE_SHA=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
IDE_DATE=$(git show -s --format=%cs HEAD 2>/dev/null || echo unknown)
VM_SHA=$(git -C ${PRIMORDIALSOUP} rev-parse --short HEAD 2>/dev/null || echo unknown)
# Tracked changes only (--untracked-files=no): scratch .md/.zip/etc. left in the
# tree shouldn't flag a build as dirty -- only uncommitted edits to tracked files do.
test -n "$(git status --porcelain --untracked-files=no 2>/dev/null)" && DIRTY=' (dirty)' || DIRTY=''
BUILT=$(date -u +%Y-%m-%dT%H:%MZ)
NS_VERSION="${IDE_SHA} ${IDE_DATE}, VM ${VM_SHA}"

# 5. Ensure the newspeak/out directory exists, and copy into it:
#   - The primordialsoup built primordialsoup.html, primordialsoup.js, primordialsoup.wasm
#   - All primordialsoup built snapshots of vfuel files such as WebCompiler.vfuel
#   - Note that primordialsoup.* have a copy in primordialsoup repo and multiple
#     copies in the newspeak repo. Deployments use the versions from the primordialsoup repo.
mkdir -p out
cp ${PRIMORDIALSOUP}/out/ReleaseEmscriptenWASM/primordialsoup.* out
cp ${PRIMORDIALSOUP}/out/ReleaseEmscriptenWASM/croquetpsoup.* out
# The Croquet client library: the LOCAL build of the patched fork
# (dev/web/croquet), which croquetpsoup.html and the JS deploys load as
# croquet.min.js. Stock CDN builds lack the NS patches (serializer own-property
# probes; files-server URL rebasing for cross-device fetches), so the staged
# copy must come from the fork. Rebuild it there with
#   packages/croquet/build.sh (or npm run build-prod-pub) when it changes.
cp ${PRIMORDIALSOUP}/../croquet/packages/croquet/pub/croquet.min.js out
cp ${PRIMORDIALSOUP}/out/snapshots/*.vfuel out
# 6. Copy Psoup Newspeak code
cp ${PRIMORDIALSOUP}/newspeak/*.ns out
# 7. Merge in Newspeak IDE dependencies
cp ./*.ns ./*.png out

# 7c. Stamp BuildInfo, into out/ ONLY, after the copy above has put the
#     placeholder there. Nothing copies *.ns into out/ after this point, so this
#     is the file step 8 compiles; the tracked BuildInfo.ns keeps its placeholder
#     and the working tree stays clean throughout. See step 4e for what this
#     ordering is protecting against.
cat > out/BuildInfo.ns <<NSEOF
Newspeak3
'Root'
class BuildInfo packageUsing: manifest = Object new (
	(* Build/version stamp -- GENERATED by tool/build.sh into out/ for this build.
	The committed copy of this file is a 'development build' placeholder and is
	deliberately left alone; this one is a build artefact and is not tracked.

	version and dirty describe the SOURCES; builtAt is when THIS image was
	built, and is what platform buildTime answers. *)
) (
) : (
	public builtAt = (
		^'${BUILT}'
	)
	public dirty = (
		^'${DIRTY}'
	)
	public version = (
		^'${NS_VERSION}'
	)
)
NSEOF
# deploy-boot.js: shared boot for web-deployed Ampleforth documents (see
# Documents>>deployForWeb:). Lean deployed pages reference it; it replays the
# real primordialsoup.html loader at runtime. Served from out/ and mirrored to
# deploy targets by the deploy scripts.
cp ./deploy-boot.js out
# TelescreenTemplate.zip: the presentation template new decks are cloned from.
# The tracked copy here is canonical - it was NOT, until 2026-08-26, when the
# copy actually in use lived in the untracked sibling web/docs and the tracked
# one had drifted a year behind it (see 07fb60d). Copying it on every build keeps
# out/ - and so every deployment served from it - in step with the repository,
# rather than with whatever happened to be lying in docs/.
cp ./TelescreenTemplate.zip out
# cp -R CodeMirror out # CodeMirror is copied during deploy

# 7a. Stage self-hosted third-party JS (isomorphic-git, lightning-fs).
# Vendored under vendor/ at the repo root and consumed by the deploy
# scripts. Mirror the whole dir so additions land automatically.
mkdir -p out/vendor
cp ./vendor/*.js out/vendor/

# 7b. Stage the test fixtures the probe batteries read over HTTP.
# testfixtures/mockai/v1/models is a fixed list-models payload, so
# croquet-probes/model-discovery-battery.js can exercise model discovery
# through OpenAICompatibleProvider with NO API key and a deterministic
# result; ProbeDoc.zip is a throwaway document for the coordinated
# document-load test, so that test does not depend on a real one staying
# put. Both are served by the front door from out/, which a clean build
# wipes - hence staging them here rather than leaving them in out/.
# Guarded: the fixtures are only needed to RUN the probe batteries, so a tree
# without them (or a checkout made before they were committed) should still
# build rather than die on a missing cp.
if [ -d ./testfixtures ]; then
    mkdir -p out/mockai/v1
    cp ./testfixtures/mockai/v1/models out/mockai/v1/
    cp ./testfixtures/*.zip out
else
    echo "NOTE: testfixtures/ absent - probe fixtures not staged (croquet-probes batteries will fail until it is)"
fi

cd ${NEWSPEAK}/out || exit 1

# The compile below reads ./*.ns from here, so this is the last moment at which
# a mis-stamped BuildInfo can be caught. Checked rather than assumed because the
# failure is silent by nature: a wrong stamp compiles perfectly and is only
# visible later, as a version string on the IDE's home page.
grep -qF "${BUILT}" BuildInfo.ns || {
    echo "error: out/BuildInfo.ns does not carry this build's stamp (${NS_VERSION})." >&2
    echo "       Refusing to compile an image that would misreport its provenance." >&2
    exit 1
}

# ${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
#     ${PRIMORDIALSOUP}/primordialsoup/out/snapshots/WebCompiler.vfuel \
#     *.ns \
#     *.png \
# not in 'out':    *.txt \
# not needed, included in html both index.html for WebIDE and primordialsoup.html:    CodeMirror/lib/codemirror.js \
# not needed, included in html both index.html for WebIDE and primordialsoup.html:    CodeMirror/addon/display/autorefresh.js \
#     RuntimeForHopscotchForHTML HopscotchWebIDE HopscotchWebIDE.vfuel \
#     RuntimeForElectron HopscotchWebIDE HopscotchElectronIDE.vfuel \
#     RuntimeForHopscotchForHTML Ampleforth Ampleforth.vfuel  \
#     RuntimeForHopscotchForHTML AmpleforthViewer AmpleforthViewer.vfuel  \
# not in git:   RuntimeForHopscotchForHTML Live22Submission Live22Submission.vfuel  \
# not in git:   RuntimeForHopscotchForHTML Smalltalks22Tutorial Smalltalks22.vfuel  \
# not in git:   RuntimeForHopscotchForHTML Live22Presentation Live22Presentation.vfuel  \
#     RuntimeForCroquet CounterApp CroquetCounterApp.vfuel \
#     RuntimeForHopscotchForHTML CounterApp CounterApp.vfuel \
#     RuntimeForHopscotchForHTML TodoMVCApp TodoMVCApp.vfuel \
#     RuntimeForCroquet TodoMVCApp CroquetTodoMVCApp.vfuel \
#     RuntimeForHopscotchForHTML TwoViewEditorApp TwoViewEditorApp.vfuel \
#     RuntimeForHopscotchForHTML TelescreenApp Telescreen.vfuel \
#     RuntimeForHopscotchForHTML ObjectPresenterDemo ObjectPresenterDemo.vfuel \
#     RuntimeForHopscotchForHTML BankAccountExemplarDemo BankAccountExemplarDemo.vfuel \
#     RuntimeForHopscotchForHTML HopscotchFontDemo HopscotchFontDemo.vfuel \
#     RuntimeForHopscotchForHTML HopscotchGestureDemo HopscotchGestureDemo.vfuel \
#     RuntimeForHopscotchForHTML HopscotchDemo HopscotchDemo.vfuel \
#     RuntimeForHopscotchForHTML Particles Particles.vfuel

#
# 8. Create vfuel files (ex: HopscotchWebIDE.vfuel)
#    from ns files (ex: HopscotchWebIDE.ns) and
#    additional resources (*.ns, *.png).
#
${PRIMORDIALSOUP}/out/ReleaseX64/primordialsoup \
    ${PRIMORDIALSOUP}/out/snapshots/WebCompiler.vfuel \
    ./*.ns \
    ./*.png \
    RuntimeForHopscotchForHTML HopscotchWebIDE HopscotchWebIDE.vfuel \
    RuntimeForHopscotchForHTML Ampleforth Ampleforth.vfuel  \
    RuntimeForHopscotchForHTML AmpleforthViewer AmpleforthViewer.vfuel  \
    RuntimeForCroquet CounterApp CroquetCounterApp.vfuel \
    RuntimeForHopscotchForHTML CounterApp CounterApp.vfuel \
    RuntimeForHopscotchForHTML TodoMVCApp TodoMVCApp.vfuel \
    RuntimeForCroquet TodoMVCApp CroquetTodoMVCApp.vfuel \
    RuntimeForHopscotchForHTML TwoViewEditorApp TwoViewEditorApp.vfuel \
    RuntimeForHopscotchForHTML TelescreenApp Telescreen.vfuel \
    RuntimeForHopscotchForHTML ObjectPresenterDemo ObjectPresenterDemo.vfuel \
    RuntimeForHopscotchForHTML BankAccountExemplarDemo BankAccountExemplarDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchFontDemo HopscotchFontDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchGestureDemo HopscotchGestureDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchDemo HopscotchDemo.vfuel \
    RuntimeForHopscotchForHTML Particles Particles.vfuel \
    RuntimeForCroquet HopscotchWebIDE CroquetHopscotchWebIDE.vfuel \
    RuntimeForCroquet AmpleforthViewer CroquetAmpleforthViewer.vfuel \
    RuntimeForCroquet HopscotchFontDemo CroquetHopscotchFontDemo.vfuel \
    RuntimeForCroquet HopscotchGestureDemo CroquetHopscotchGestureDemo.vfuel \
    RuntimeForCroquet HopscotchDemo CroquetHopscotchDemo.vfuel \
    "$additionalNs"

cd ${NEWSPEAK}/tool || exit 1
