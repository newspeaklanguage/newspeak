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
#   Deploys the 'HopscotchWebIDE.vfuel' as a Progressive Web App (PWA) (as opposed to a website).
#   Copies all built files to the Newspeak HTTPs server directory
#   specified in the first argument, and updates the PWA Service Worker version file
#   specified in the second argument. The updated version is used as the PWA cache version.
#   By 'All built files' we mean the 'HopscotchWebIDE.vfuel' and miscellaneous js and html files
#   supporting the PWA, as well as the script 'serve-newspeak.sh', which starts the HTTP server.

# Arguments:
#
#   1. http-server-dir
#   2. pwa-version-file 
#   See function 'args_parse_for_deploy_as_pwa' for details

# Usage Examples:
#
#   1. Deploy files to server running from
#      the '~/servers/newspeak-http-server' directory, serving as 'localhost'.
#      - cd tool
#      - ./deploy-webide-vfuel-as-pwa.sh  ~/servers/newspeak-http-server  localhost
#
#   2. Deploy files to server running from
#      the '~/servers/newspeak-http-server' directory, serving as 'newspeaklanguage.org'
#      - cd tool
#      - ./deploy-webide-vfuel-as-pwa.sh  ~/servers/newspeak-http-server  newspeaklanguage.org
#
#      'newspeaklanguage.org' is a special case in the sense that git does NOT ignore
#      it's version file, the '$NEWSPEAK/pwa-deployed-versions/newspeaklanguage.org.version'.
#      This ensures the global uniqueness of the PWA version served from 'https://newspeaklanguage.org'.
#
#   3. Deploy files to server running from
#      the '../out' directory, serving as 'localhost'.
#      This mimicks (I think) how the server ran before this change.
#      The advantage of serving from the '../out' directory is that 
#      *you ONLY need to run this 'deploy' script once, after, just keep running the 'build.sh' script.*
#      - cd tool
#      - ./deploy-webide-vfuel-as-pwa.sh  ../out  localhost


#
# 1. Read utility functions and ensure (heuristically) directory is tool
#
if [ ! -f ./newspeak_util.sh ]; then printf "\n\nERROR: Run this command from Newspeak 'tool' directory. Current directory=%s. Exiting.\n\n" "$PWD"; exit 1; fi
. ./newspeak_util.sh
set -o errexit
check_dir_is_tool

#
# 2. Parse arguments, init the http directory, and copy all files to the http directory
#
args_parse_for_deploy_as_pwa "$@"
init_http_dir_for_deploy
# n/a for pwa deploy, as codemirror is already in webIDE tree: copy_codemirror_for_deploy_as_pwa
copy_files_to_http_server_for_deploy_as_pwa

#
# 3. Describe to user what to do next
#
echo ""
echo "-------------------------------------------------------------------------"
echo "SUCCESS: Deployed latest build from '$NEWSPEAK/out' to '$httpServerDir'."
echo
echo "NEXT: cd '$httpServerDir', then run './serve-newspeak.sh PORT' to start "
echo "      the HTTP server on PORT (unless already running)."
echo
echo "AFTER: In the browser, access the installed Newspeak IDE on a URL such as"
echo "       'http://localhost:PORT/webIDE'."
echo ""
echo "       Note: If http serves a public site such as 'mynewspeakapp.net', then the URL is"
echo "             'https://mynewspeakapp.net:PORT/webIDE'."
echo "-------------------------------------------------------------------------"
echo ""
