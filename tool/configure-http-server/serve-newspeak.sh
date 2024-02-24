#!/bin/sh -e

# Ensure user provided a port number

if [ $# -ne 1 ] || [ "$(echo "$1" | grep -E '^[[:digit:]]{1,}$')" = "" ]; then
    echo "When starting the Newspeak HTTP server, please always specify numerical port number as the first argument."
    echo "Usage: $0 portNumber"
    echo "Exiting."
    exit 1
fi

port=$1

# Use a comment to help user run
nextStep="
If you deployed a webIDE as Progressive Web App (PWA), access it on a URL such as
       'http://localhost:$port/webIDE'.

If you deployed a vfuel file as a website, access the vfuel on a URL such as
        'http://localhost:$port/primordialsoup.html?snapshot=HopscotchWebIDE.vfuel'
        'http://localhost:$port/primordialsoup.html?snapshot=CounterApp.vfuel'
         etc
"

# Start the server

if command -v python3; then
    echo "Starting Newspeak HTTP on port=$port using Python3"
    echo "$nextStep"
    python3 ./server3.py "$port"
elif command -v python; then
    version=$(python --version 2>&1)
    case "$version" in
        *'Python 3'*)
         echo "Starting Newspeak HTTP on port=$port using Python3"    
         echo "$nextStep"
         python ./server3.py "$port";;
       *'Python 2'*)
         echo "Starting Newspeak HTTP on port=$port using Python2"    
         echo "$nextStep"
         python ./server2.py "$port";;
       *'Python 1'*)
         echo "Cannot serve Newspeak from localhost. Python 2 or 3 is needed to run the web server, but you have Python 1. Upgrade to Python 2 or 3."; exit 1 ;;
       *)
    echo "Cannot serve Newspeak from localhost. Python 2 or 3 is needed to run the web server, but Python version not recognized"; exit 1 ;;
    esac
else
    echo "Cannot serve Newspeak from localhost. Python is needed to run the web server, but Python could not be found on this system"
    exit 1
fi


