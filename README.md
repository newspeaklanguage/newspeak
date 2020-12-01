# Newspeak

[Newspeak](http://www.newspeaklanguage.org/) is a new programming language in the tradition of Self and Smalltalk.

For pre-built VMs and images, see
[newspeaklanguage.org/downloads](http://www.newspeaklanguage.org/downloads).

If you intend to develop with the new Web IDE, read on:

* The Web IDE is still experimental. Caveat Emptor.

First, download the electron app:
* [For Mac (Intel)](https://newspeaklanguage.org/NewspeakIDE.app.zip)
* [For Windows](https://newspeaklanguage.org/newspeakIDE.zip)


At the moment, we recommend the following setup (this will
definitely change - such complexity is not the way we intend to do things at the
Ministry of Truth).

Set up a directory for your work, say, nswasm

```
mkdir nswasm
cd nswasm
```

and then clone this repo under it.

In the same directory, clone
https://github.com/newspeaklanguage/primordialsoup.

Thus, your directory structure looks like:

```
               nswasm
               
                 |        |
      newspeak    primordialsoup
```


Follow the instructions at

https://github.com/newspeaklanguage/primordialsoup/blob/master/docs/building.md

in the primordialsoup repo to set up the required dependencies for
primordialsoup, and switch to the extraRevs branch.

```
cd primordialsoup
git checkout extraRevs
```

You'll also want to download CodeMirror from https://codemirror.net/.

Place it in the top level of the newspeak repo.

In the top level of the newspeak repository, you should find the script
build.sh. It assumes Emscripten is in ~/software/emsdk/; you will
want to adjust that to reflect where you have installed emscripten.

Running build.sh should build the psoup VM as well as  the vfuel file for
the Newspeak IDE. 

```
source build.sh
```

HopscotchWebIDE.vfuel should now exist in the ./out subdirectory of the
newspeak repository.

You can access it by running a web server, using the serve.sh script:

```
source serve.sh
```
The serve.sh script will run a python web server and will tell you that you
can access the IDE by pointing a web browser at:

http://localhost:8080/primordialsoup.html?snapshot=HopscotchWebIDE.vfuel

You can edit server.py to change the port used. It is often convenient to have the web server running all the time.

If you make changes to the Newspeak code used in the IDE, just run build.sh again.

Another option is to rebuild the vfuel file for the IDE, and copy it into
the electron application. That way you don't need to run a web server.
The script updateApp.sh provides a template for this. On a mac, it should work
out of the box:

```
source updateApp.sh
```

Otherwise, you'll need to modify it as described
in the script. 



