#!/bin/sh

##
## Description:
##   This file sets environment variables for functions in 'newspeak_util.sh'.
##   It is sourced in all scripts running Newspeak build and deploy,
##   indirectly through 'newspeak_util.sh'.
##

#
# Environment variables for directories needed to build Newspeak.
# Modify them according to your directory structure, but do not push.
#
export EMSDK=~/personal/newspeak/emsdk                    # Emscripten directory
export NEWSPEAK=~/personal/newspeak/newspeak              # Newspeak directory
export PRIMORDIALSOUP=~/personal/newspeak/primordialsoup  # Primordialsoup directory
echo "$0: EXPORTING: EMSDK=$EMSDK, NEWSPEAK=$NEWSPEAK, PRIMORDIALSOUP=$PRIMORDIALSOUP"
