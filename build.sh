#!/bin/sh -ex

# Set this to wherever you have emscripten installed.
EMSDK=~/software/emsdk

source $EMSDK/emsdk_env.sh

# We assume we cloned psoup into the directory above newspeak;
# change this if your psoup repo is elsewhere
pushd ../primordialsoup
./build os=emscripten arch=wasm
popd

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
    CodeMirror/lib/codemirror.js \
    CodeMirror/addon/display/autorefresh.js \
    RuntimeForHopscotchForHTML HopscotchWebIDE HopscotchWebIDE.vfuel \
    RuntimeForElectron HopscotchWebIDE HopscotchElectronIDE.vfuel \
    RuntimeForHopscotchForHTML Ampleforth Ampleforth.vfuel  \
    RuntimeForHopscotchForHTML AmpleforthEditorApp AmpleforthEditor.vfuel  \    
    RuntimeForCroquet CounterApp CroquetCounterApp.vfuel \
    RuntimeForHopscotchForHTML CounterApp CounterApp.vfuel \
    RuntimeForHopscotchForHTML TodoMVCApp TodoMVCApp.vfuel \
    RuntimeForHopscotchForHTML TwoViewEditorApp TwoViewEditorApp.vfuel \
    RuntimeForHopscotchForHTML ObjectPresenterDemo ObjectPresenterDemo.vfuel \
    RuntimeForHopscotchForHTML BankAccountExemplarDemo BankAccountExemplarDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchFontDemo HopscotchFontDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchGestureDemo HopscotchGestureDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchDemo HopscotchDemo.vfuel \
    RuntimeForHopscotchForHTML Particles Particles.vfuel   
    
    
popd

