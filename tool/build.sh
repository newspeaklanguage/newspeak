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

# Back to 'newspeak'.
cd ${NEWSPEAK} || exit 1

# 5. Ensure the newspeak/out directory exists, and copy into it:
#   - The primordialsoup built primordialsoup.html, primordialsoup.js, primordialsoup.wasm
#   - All primordialsoup built snapshots of vfuel files such as WebCompiler.vfuel
#   - Note that primordialsoup.* have a copy in primordialsoup repo and multiple
#     copies in the newspeak repo. Deployments use the versions from the primordialsoup repo.
mkdir --parent out
cp ${PRIMORDIALSOUP}/out/ReleaseEmscriptenWASM/primordialsoup.* out
cp ${PRIMORDIALSOUP}/out/snapshots/*.vfuel out
# 6. Copy Psoup Newspeak code
cp ${PRIMORDIALSOUP}/newspeak/*.ns out
# 7. Merge in Newspeak IDE dependencies
cp ./*.ns ./*.png out
# cp -R CodeMirror out # CodeMirror is copied during deploy

cd ${NEWSPEAK}/out || exit 1

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
    RuntimeForHopscotchForHTML CheckedItemApp CheckedItemApp.vfuel \
    "$additionalNs"

cd ${NEWSPEAK}/tool || exit 1
