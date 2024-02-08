#!/bin/sh

##
## Description:
##   This file is sourced in any script running Newspeak build.
##   It does set environment variables, for functions in 'util.sh'.
##

#
# Environment variables for directories needed to build Newspeak.
# Modify them according to your directory structure, but do not push.
#
export EMSDK=~/software/emsdk                           # Emscripten directory
export NEWSPEAK=~/software/nswasm/newspeak              # Newspeak directory
export PRIMORDIALSOUP=~/software/nswasm/primordialsoup  # Primordialsoup directory
echo "$0: EXPORTING: EMSDK=$EMSDK, NEWSPEAK=$NEWSPEAK, PRIMORDIALSOUP=$PRIMORDIALSOUP"
