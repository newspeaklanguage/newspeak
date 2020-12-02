#!/bin/sh -ex

source build.sh
# If on a mac, leave the definition of APPVFUELPATH untouched.
#  If one Windows, if your app is located at x, then set
# APPVFUELPATH=x/resources/app/out/
APPVFUELPATH=/Applications/NewspeakIDE.app/Contents/Resources/app/out/
cp out/HopscotchWebIDE.vfuel $APPVFUELPATH

