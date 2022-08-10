#!/bin/sh -e
cd out

if command -v python3 &> /dev/null
then
    python3 ./server3.py
elif command -v python &> /dev/null
then
    version=`python --version 2>&1`
    case "$version" in
       *'Python 3'*)
         python ../server3.py;;
       *'Python 2'*)
         python ../server2.py;;
       *'Python 1'*)
         echo "Cannot serve Newspeak from localhost. Python 2 or 3 is needed to run the web server, but you have Python 1. Upgrade to Python 2 or 3.";;
       *)
    echo "Cannot serve Newspeak from localhost. Python is needed to run the web server, but Python version not recognized";;
    esac
else
    echo "Cannot serve Newspeak from localhost. Python is needed to run the web server, but Python could not be found on this system"
    exit
fi




