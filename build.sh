#!/bin/sh -ex

# Set this to wherever you have emscripten installed.
EMSDK=~/software/emsdk

source $EMSDK/emsdk_env.sh

# We assume we cloned psoup into the directory above newspeak;
# change this if your psoup repo is elsewhere
pushd ../primordialsoup
./build os=emscripten arch=wasm
popd

# Back in 'newspeak'.
# Increase the pwaVersion in the PWA service worker, the newspeak/platforms/webIDE/sw.js
# This is required on every Newspeak build (strictly speaking,
#   only on every Newspeak deployment to HTTP server), for the PWA clients
#   to refresh all caches.
# Without the pwaVersion increase, PWA clients would not replace
#   the cached HopscotchWebIDE.vfuel with the new version,
#   unless forced by manual cache clean or similar

. ./increase-pwa-version.sh

# Ensure the newspeak/out directory exists, and copy into it:
#   - The primordialsoup built primordialsoup.html, primordialsoup.js, primordialsoup.wasm
#   - All primordialsoup built snapshots of vfuel files such as WebCompiler.vfuel
mkdir -p out
cp ../primordialsoup/out/ReleaseEmscriptenWASM/primordialsoup.* out
cp ../primordialsoup/out/snapshots/*.vfuel out
# Copy Psoup Newspeak code
cp ../primordialsoup/newspeak/*.ns out
# Merge in Newspeak IDE dependencies
cp *.ns *.png out
# Make sure we have CodeMirror where we need it
cp -R CodeMirror out

pushd out
../../primordialsoup/out/ReleaseX64/primordialsoup \
    ../../primordialsoup/out/snapshots/WebCompiler.vfuel \
    *.ns \
    *.png \
    *.txt \
    CodeMirror/lib/codemirror.js \
    CodeMirror/addon/display/autorefresh.js \
    RuntimeForHopscotchForHTML HopscotchWebIDE HopscotchWebIDE.vfuel \
    RuntimeForElectron HopscotchWebIDE HopscotchElectronIDE.vfuel \
    RuntimeForHopscotchForHTML Ampleforth Ampleforth.vfuel  \
    RuntimeForHopscotchForHTML AmpleforthViewer AmpleforthViewer.vfuel  \
    RuntimeForHopscotchForHTML Live22Submission Live22Submission.vfuel  \
    RuntimeForHopscotchForHTML Smalltalks22Tutorial Smalltalks22.vfuel  \
    RuntimeForHopscotchForHTML Live22Presentation Live22Presentation.vfuel  \
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
    RuntimeForHopscotchForHTML Particles Particles.vfuel
    
    
popd

