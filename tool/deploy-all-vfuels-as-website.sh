#!/bin/sh

# Released under the MIT License at https://opensource.org/license/mit/
# 
# Copyright (c) 2024 "Newspeak authors"
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.


# Description:
#
#   Deploys all '.vfuel' files listed in 'build.sh' as a website (as opposed to PWA).  
#   Copies all built files to the Newspeak HTTPs server directory
#   specified in the first argument.
#   By 'All built files' we mean all '.vfuel' files built by 'build.sh',
#   and miscellaneous js and html files supporting the website.

# Arguments:
#
#   1. http-server-dir
#   Note: there is no need for the second argument as in the PWA script -
#         we do not need a PWA version number.
#   See function 'args_parse_for_deploy_as_website' for details.

# Usage Examples:
#   1. Deploy files to server running from
#      the '~/servers/newspeak-http-server' directory
#     - cd tool
#     - ./deploy-all-vfuels-as-website.sh  ~/servers/newspeak-http-server
#   2. Deploy files to server running from
#      the '../out' directory.
#      This mimicks (I think) how the server ran before this change.
#      The advantage of serving from the '../out' directory is that 
#      *you ONLY need to run this 'deploy' script once, after, just keep running the 'build.sh' script.*
#     - cd tool
#     - ./deploy-all-vfuels-as-website.sh  ../out


#
# 1. Read utility functions and ensure (heuristically) directory is tool
#
if [ ! -f ./newspeak_util.sh ]; then printf "\n\nERROR: Run this command from Newspeak 'tool' directory. Current directory=%s. Exiting.\n\n" "$PWD"; exit 1; fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

# Check if user wishes to serve HTTP from the '../out' directory.
# Serving from the '../out' directory is a special case, because it allows
#   to run this deploy ('./deploy-all-vfuels-as-website.sh') only once.
# Subsequent runs of 'build.sh' place the '*vfuel' files compiled from the
#   changed '*.ns' files in the  '../out' directory from where the running server
#   picks up changes without the need to run this deploy
#   (the './deploy-all-vfuels-as-website.sh') again
#   (as long as the HTTP server was started by ./'serve-newspeak.sh PORT').

# 2. Parse arguments to set '$httpServerDir'.
args_parse_for_deploy_as_website "$@"

httpServerDirLastNode="${httpServerDir%/}"
httpServerDirLastNode="${httpServerDirLastNode##*/}"

if [ "$httpServerDirLastNode" = "out" ]; then
    echo "Special deploy to serve  Newspeak HTTP from the 'out' directory"
    echo ""
    # Setup CodeMirror with the structure expected by primordialsoup.html
    copy_codemirror_for_deploy_as_website
    # No need to copy files created by the './build.sh' anywhere,
    #   we will be serving from '../out' where the './build.sh' placed them already.
    # But copy the http server in case this runs the first time.
    rsync ./configure-http-server/*       "$httpServerDir/" # ending slash required bc globbing    
else
    echo "Deploying to serve Newspeak HTTP from the $httpServerDir directory"
    echo ""
    # Init the '$httpServerDir', and copy files created by './build.sh'
    # from '../out' to '$httpServerDir'
    init_http_dir_for_deploy
    copy_files_to_http_server_for_deploy_as_website
fi

#
# 3. Describe to user what to do next
#
echo ""
echo "-------------------------------------------------------------------------"
echo "SUCCESS: Deployed latest build from '$NEWSPEAK/out' to '$httpServerDir'."
echo
echo "NEXT: cd '$httpServerDir', then run './serve-newspeak.sh PORT' to start "
echo        "the HTTP server on PORT (unless already running)."
echo
echo "AFTER: In the browser, access any vfuel on a URL such as"
echo "        'http://localhost:PORT/primordialsoup.html?snapshot=HopscotchWebIDE.vfuel'"
echo "        'http://localhost:PORT/primordialsoup.html?snapshot=CounterApp.vfuel'"
echo "         etc"
echo "-------------------------------------------------------------------------"
echo ""
