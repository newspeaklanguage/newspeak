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

##
## Description:
##   This file is sourced in any script running Newspeak build.
##   It does set environment variables, and defines a few functions.
##

#
# Read environment variables for directories needed to build Newspeak.
#
. ./newspeak_env.sh


#
# Performs a heuristic check if the current directory is newspeak's 'tool';
# exits with non-zero if not true, otherwise ends succesfully.
#

check_dir_is_tool() {
    newspeakDir=${PWD%/*}
    currNodeDir=${PWD##*/}
    if [ "${currNodeDir}" != "tool" ] || [ ! -d "${newspeakDir}/platforms/webIDE" ]; then
        echo
        echo "Please change directory to the 'tool' directory of Newspeak before running this command. Current directory(PWD)=$PWD. Exiting."
        echo
        exit 1
    fi
}

#
# For both website and pwa deployments, heuristically validates
#   the '$httpServerDir' is an intended deployment directory:
#   If it exists, it contains the server marker file 'NEWSPEAK_SERVER_MARKER',
#   otherwise it asks for confirmation.
# Initializes the server directory marker file 'NEWSPEAK_SERVER_MARKER',
#   and for the pwa deployment, also
#   the version file '$pwaVersionPath'
#
init_http_dir_for_deploy() {
    
    # If the $httpServerDir exists, assume deploy already did run to that directory.
    if [ -d "$httpServerDir" ]; then
        if [ ! -f "$httpServerDir/NEWSPEAK_SERVER_MARKER" ]; then
            # But if the $httpServerDir does NOT contain file 'NEWSPEAK_SERVER_MARKER'
            #   user may be specifying a wrong directory by mistake. Explain and exit.
            echo "The first argument http-server-dir='$httpServerDir',"
            echo "  specifies the Newspeak HTTP deployment directory."
            echo "Yet, the directory does not contain the file NEWSPEAK_SERVER_MARKER,"
            echo "  which may indicate a directory name typo."
            echo "If you are sure to continue deploying Newspeak to "
            echo "  http-server-dir='$httpServerDir',"
            echo "  answer 'y' to continue (other response means quit). [y/n]: "
            read -r answer
            if [ "$answer" != "y" ]; then
                echo "Responded '$answer'."
                echo "If the '$httpServerDir' "
                echo "  is the intended deployment directory, delete it,"
                echo "  or create a file named NEWSPEAK_SERVER_MARKER in the directory".
                exit 1
            fi
        fi
    else
        echo "Deploying Newspeak  HTTP server to directory '$httpServerDir' for the FIRST TIME."
        mkdir -p "$httpServerDir"
        touch "$httpServerDir/NEWSPEAK_SERVER_MARKER"
    fi

    if [ -z "${pwaVersionPath}" ]; then
        echo "pwaVersionPath is not set, deploying as website."
        echo ""
    else
        echo "pwaVersionPath is set, deploying as PWA."
        echo ""
        # Test if the version file ${pwaVersionPath}.version exists;
        #   else create it with initial version number 1.
        # Note that for git non-ignored deployments, such as 'newspeaklanguage.org',
        # the file on "$pwaVersionPath" should be in git, but we do not check for that.
        if [ ! -f "$pwaVersionPath" ]; then
            echo "1" >  "$pwaVersionPath"
        fi
    fi
}



#
# Validates and parses arguments expected for the script 'deploy_webide_vfuel_as_pwa.sh'
#
args_parse_for_deploy_as_pwa() {
    deployUsage="

    $0  http-server-dir   pwa-version-file 
       - Copies 'all built files' into the directory http-server-dir.
         'all built files' are:
          - all vfuel files compiled by 'build.sh' (plus)
          - primordialsoup.js and primordialsoup.wasm
          - the directory 'webIDE' 
       - Updates the PWA version in 'pw.js' during it's copy to the 'http-server-dir'

    Arguments:
      - 'http-server-dir' is the base directory where the HTTP server runs.
      - 'pwa-version-file' is the name of the PWA version file
          without the '.version' suffix.
          The file is located in the directory 'pwa-deployed-versions',
          Customarily should be the same as the hostname
          served from the directory in the first argument, the 'http-server-dir'.
        Examples: 'localhost', 'newspeaklanguage.org'

"

    if [ $# -ne 2 ]; then
        echo "Usage=$deployUsage"
        echo "Invalid argument count in \"$0 $*\"; specify two arguments, see Usage above."
        echo "Exiting."
        exit 1
    fi

    httpServerDir="$1"
    # pwaVersionFile="$2"
    pwaVersionPath="../pwa-deployed-versions/${2}.version"

    echo ""
    echo "$0: SETTING: httpServerDir=$httpServerDir, pwaVersionPath=$pwaVersionPath."
    echo ""
}

#
# Validates and parses arguments expected for the script 'deploy_all_vfuels_as_website.sh'
#
args_parse_for_deploy_as_website() {
    deployUsage="

    $0  http-server-dir 
       - Copies 'all built files' into the directory http-server-dir.
         'all built files' are:
          - all vfuel files compiled by 'build.sh' (plus)
          - primordialsoup.js and primordialsoup.wasm

    Arguments:
      - 'http-server-dir' is the base directory where the HTTP server runs.

"
    
    if [ $# -ne 1 ]; then
        echo "Usage=$deployUsage"
        echo "Invalid argument count in \"$0 $*\"; specify one argument, see Usage above."
        echo "Exiting."
        exit 1
    fi

    httpServerDir="$1"
    unset pwaVersionPath # unset, functions called later use it to recognize PWA deploy


    echo ""
    echo "$0: SETTING: httpServerDir=$httpServerDir"
    echo ""
}

# Increases PWA version in file '$pwaVersionPath', and sets variable 'pwaVersion'
increase_pwa_version() {

    if [ -z "$pwaVersionPath" ] || [ ! -f "$pwaVersionPath" ]; then echo "PWA version file pwaVersionPath=$pwaVersionPath does not exist or variable not set, exiting."; exit 1; fi

    pwaVersion=$(cat "$pwaVersionPath")

    case $pwaVersion in
        ''|*[!0-9]*) echo "pwaVersion=$pwaVersion not an integer, exiting"; exit 1 ;;
    esac    

    pwaVersion=$((pwaVersion + 1))

    echo $pwaVersion > "$pwaVersionPath"
    
}

# Copies sw.js from the git directory to http server directory, increasing the PWA version.
#
# Increase the pwaVersion in the PWA service worker, the newspeak/platforms/webIDE/sw.js
# This is required on every Newspeak build (strictly speaking,
#   only on every webIDE build), for the PWA clients to refresh all caches.
# Without the pwaVersion increase, PWA clients would not replace
#   the cached HopscotchWebIDE.vfuel with the new version,
#   unless forced by manual cache clean or similar.
copy_sw_to_http_dir_increasing_pwa_version() {

    increase_pwa_version

    swGitPath="$NEWSPEAK/platforms/webIDE/sw.js"
    swHttpServerPath="$httpServerDir/webIDE/sw.js"

    if [ ! -f "$swGitPath" ]; then echo "Service worker file swGitPath=$swGitPath does not exist, exiting."; exit 1; fi

    sed -E "s/^const pwaVersion = 1;$/const pwaVersion = $pwaVersion;/" "$swGitPath" > "$swHttpServerPath"

    # echo "Copied sw.js to swHttpServerPath=$swHttpServerPath, version is now $(cat "$swHttpServerPath")"
    echo "Copied sw.js to swHttpServerPath=$swHttpServerPath, new pwaVersion=$pwaVersion"
    
}

#
# For deployment served as a website (as opposed to a PWA deployment),
#   (website deployment is accessed as: 'http://myhost:port/primordialsoup.html?snapshot=CounterApp.vfuel',
#   for example: 'http://localhost:8081/primordialsoup.html?snapshot=HopscotchWebIDE.vfuel').
#
# This function copies the required codemirror files from it's git location at
#   'platforms/webIDE/public/assets/lib' to the location assumed by the git file
#   'primordialsoup.html'.
# 
# This is only actually required for serving the Web IdE using 'HopscotchWebIDE.vfuel',
#   but copied for any vfuel served as a website.
#
copy_codemirror_for_deploy_as_website() {
    # Ensures the server directory contains CodeMirror directories
    #   expected by 'primordialsoup.html' and copies CodeMirror
    #   files from git in the directories.
    mkdir --parent "$httpServerDir/CodeMirror/lib/"
    mkdir --parent "$httpServerDir/CodeMirror/addon/display/"
    cp ../platforms/webIDE/public/assets/lib/codemirror.js "$httpServerDir/CodeMirror/lib/"
    cp ../platforms/webIDE/public/assets/lib/codemirror.css "$httpServerDir/CodeMirror/lib/"
    cp ../platforms/webIDE/public/assets/lib/codemirror_autorefresh.js "$httpServerDir/CodeMirror/addon/display/autorefresh.js"
}

#
# Copies all files common to PWA and WEBSITE deployment to the server directory.
#
# httpServerDirLastNode="${httpServerDir%/}"
# httpServerDirLastNode="${httpServerDirLastNode##*/}"
#
copy_common_files_to_http_server_dir_for_deploy() {

    if [ -z "$1" ]; then echo "Internal error, exiting." exit 1; fi
    
    httpLibDir="$1"
    echo "Setting and making httpLibDir=$httpLibDir"
    mkdir --parent "$httpLibDir/"
    
    # 1. Copy top level images to the top of the server directory, (to the same level as webIDE).
    # The top location is needed due to a serialization bug where image aliens
    # always look for images on top level of server, e.g. http://localhost:8081/clearImage.png
    rsync "$NEWSPEAK"/*.png               "$httpServerDir/" # ending slash required bc globbing
    
    # 2. Copy server-start files to server directory
    rsync ./configure-http-server/*       "$httpServerDir/" # ending slash required bc globbing
    
    # 3. Copy results of primordialsoup 'build' to the server directory
    rsync "$NEWSPEAK/out/primordialsoup.js"     "$httpLibDir/"
    rsync "$NEWSPEAK/out/primordialsoup.wasm"   "$httpLibDir/"

}

#
# Copies all necessary files to run the Newspeak HTTP server serving
# the webIDE as a PWA to the server directory, the "$httpServerDir".
#
# With this structure, the webIDE PWA is accessed similar to
#   'http://localhost:8081/webIDE'
#
copy_files_to_http_server_for_deploy_as_pwa() {

    httpLibDir="$httpServerDir/webIDE/public/assets/lib"
    echo "Setting and making httpLibDir=$httpLibDir"
    mkdir --parent "$httpLibDir/"

    copy_common_files_to_http_server_dir_for_deploy "$httpLibDir"

    # Copy the whole git webIDE to server directory to deploy as PWA
    rsync -r "$NEWSPEAK/platforms/webIDE" "$httpServerDir"

    # Copy results of newspeak/tool/build.sh to the server directory
    #   1. Of all .vfuels, ONLY the HopscotchWebIDE.vfuel is copied, so this runs ONLY webIDE
    rsync "$NEWSPEAK/out/HopscotchWebIDE.vfuel" "$httpLibDir/"
    #   2. Copy primordialsoup.wasm and primordialsoup.js
    rsync "$NEWSPEAK/out/primordialsoup.wasm" "$httpLibDir/"
    rsync "$NEWSPEAK/out/primordialsoup.js" "$httpLibDir/"

    # Increase the pwaVersion managed in pwaVersionPath
    # and copy the 'sw.js' with the increased version to the webIDE
    copy_sw_to_http_dir_increasing_pwa_version
}

#
# Copies all necessary files to run the Newspeak HTTP server serving
# any vfuel generated by "build.sh" as a WEBSITE to the server directory,
# the "$httpServerDir".
#
# With this structure, any vfuel is accessed similar to
#   'http://localhost:8081/primordialsoup.html?snapshot=CounterApp.vfuel'
#
copy_files_to_http_server_for_deploy_as_website() {

    copy_codemirror_for_deploy_as_website

    httpLibDir="$httpServerDir"
    echo "Setting and making httpLibDir=$httpLibDir"
    mkdir --parent "$httpLibDir/"
    
    copy_common_files_to_http_server_dir_for_deploy "$httpLibDir"

    # Copy results of newspeak/tool/build.sh to the server directory
    #   ALL vfuel files are copied
    rsync $NEWSPEAK/out/*.vfuel "$httpLibDir/"
    rsync $NEWSPEAK/out/primordialsoup.html "$httpLibDir/"
}

