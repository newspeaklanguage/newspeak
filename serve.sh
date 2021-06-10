#!/bin/sh -e
cd out

if ! command -v python &> /dev/null
then
    echo "Python could not be found on this system"
    exit
fi

version=`python --version 2>&1`
case "$version" in
  *'Python 3'*)
      python ../server3.py;;
  *'Python 2'*)
      python ../server.py;;
  *)
      echo "Python version not recognized";;
esac

