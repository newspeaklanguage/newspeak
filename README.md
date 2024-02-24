# 1. Newspeak

[Newspeak](http://www.newspeaklanguage.org/) is a new programming language in the tradition of Self and Smalltalk.

The Newspeak IDE is delivered via the web at [https://www.newspeaklanguage.org/webIDE/](https://www.newspeaklanguage.org/webIDE/)  as a Progressive Web App (PWA). 
This means that you can install it locally on your device, and then run it 
without needing an internet connection. Updates are delivered
automatically whenever you are online - this is enabled by the PWA.

If you are testing or developing in Newspeak, the online version is all you need.
You could stop here and consult the Newspeak resources linked above.

But you may decide to build and serve Newspeak or your own Newspeak application locally. 
The sections explain how to do so.

Note: below, the terms 'serve', 'server' refer to 
      'serve in a HTTP server', 'HTTP server' or similar.

# 2. How to build, deploy, and serve Newspeak applications

This is only a terse introduction to creating and serving Newspeak applications.

A Newspeak application is a Newspeak object which adheres to a few
specific API naming conventions.  Its class can be saved to a `.ns`
source file, and used to create an instance that is serialized into a
binary `.vfuel`, which is deployed and served.

**Note:**: You can usually run the application inside the IDE for
  purposes of testing and development, provided you have the source
  code loaded in the IDE. We won't discuss that here - this document
  is focused on application deployment.

A `.vfuel` file can be created from its source class in one of two ways:

1. From the locally served or online [Newspeak IDE](http://www.newspeaklanguage.org/webIDE) by clicking the **[deploy]** link beside the application class.  This process is not described in this document.

2. From a command line, by first saving the application class to a `.ns` source file, then running the `build.sh` script described below.  To use this command line method, you need to install several items.  This process is described in the [Building Newspeak from scratch](#3.-building-newspeak-from-scratch) section and its subsections.

To serve a Newspeak application in a HTTP server, you need a binary file with `.vfuel` extension, one or more HTML files, and at least two files, 'primordialsoup.js' and 'primordialsoup.wasm' (both created by `build.sh`), and potentially other application specific resources.

# 3. Building Newspeak from scratch

TL;DR: If you want to build the Newspeak IDE or any Newspeak
application from scratch, follow the installation steps in section 3.1
and subsection 3.1.1 (each only needs to be performed once). Then
follow the steps in section 4.1 (for the Newspeak IDE running as a
PWA) or 4.2 (for any application, running as a website). The steps in section 4.1 or 4.2 are repeated after after any change in the application.

In addition to using the online version of the [Newspeak IDE](http://www.newspeaklanguage.org/webIDE/), you can build, deploy, and serve the Newspeak system, or any Newspeak application, on your computer. There may be a few reasons to build and use the Newspeak system this way:

- You just want to learn how to do it.
- You want to write, build, and serve your own Newspeak application (a `.vfuel` file), or serve the Newspeak IDE from your own HTTP server for local or public consumption.

Read and follow the steps below to build Newspeak locally (on your computer) from scratch.

## 3.1 Building Newspeak: installing required software

This is needed one-time only.

Building Newspeak locally requires some software to be downloaded,
cloned from Github, or installed: *Newspeak*, *Primordialsoup* and
it's dependencies and targets: *Emscripten*, *Scons*, and *g++-multilib*. Details of how to install the required software are below.

The default directories for installing *Newspeak*, *Primordialsoup* and *Emscripten* are determined by environment variables set in `newspeak/tool/newspeak_env.sh`. These variables and their default values are 
 
```sh
export EMSDK=~/software/emsdk                           # Emscripten directory
export NEWSPEAK=~/software/nswasm/newspeak              # Newspeak directory
export PRIMORDIALSOUP=~/software/nswasm/primordialsoup  # Primordialsoup directory
```

We use these defaults throughout the rest of this document. If you wish to use different directories, you will need to do two things: 

- Adjust references to the above directory names in this document
- After cloning Newspeak in the steps below, edit the file `newspeak/tool/newspeak_env.sh` and adjust the directory names to your situation.

The installation steps:

1. Start with creating a directory for Newspeak and Primordialsoup, `~/software/nswasm` and then clone this repo under it.
2. In `~/software/nswasm`, also clone <https://github.com/newspeaklanguage/primordialsoup> and switch to the branch called `extraRevs`.

You can use the following commands to execute 1. and 2. just above:

```sh
mkdir ~/software/nswasm
cd ~/software/nswasm # Adjust to your directory path
git clone https://github.com/newspeaklanguage/newspeak.git
git clone https://github.com/newspeaklanguage/primordialsoup.git
cd primordialsoup
git checkout extraRevs
```

To be clear: at this point, you should now have a directory named `~/software/nswasm`, with two
subdirectories; `newspeak`, containing this repository, and `primordialsoup`, containing the `extraRevs` branch of <https://github.com/newspeaklanguage/primordialsoup>.

**Important:** If you are using 'non default' directories for your installation, now edit the file `newspeak/tool/newspeak_env.sh`, change the exported variables there, and save the file. 

### 3.1.1 Building Newspeak: installing Primordialsoup dependencies

Next, you will need to install software needed by the Primordialsoup build. 

Unless you are targetting Fuchsia, follow steps 1 to 3 in this section to install and build Primordialsoup and its dependencies.

1. **Install and configure Emscripten and Primordialsoup dependencies:** building Primordial Soup requires a C++ compiler and SCons.

    - On Debian/Ubuntu:
        ```sh
        sudo apt-get install g++-multilib scons
        ```
    - On Opensuse:
        ```sh
        sudo zypper install scons
        sudo zypper install -t pattern devel_basis   devel_C_C++   32bit 
        ```
    - On macOS, install XCode and SCons.

    - On Windows, install Visual Studio and SCons.
    
2. **Install and configure the Emscripten SDK (`emsdk`):** Emscripten
   is a compiler that compiles C and C++ sources to WebAssembly, which
   can then be executed by browsers. 

    Clone the Emscripten SDK (`emsdk`) using these steps
    ```sh
    # Set the Newspeak environment.
    cd ~/software/nswasm/newspeak # Adjust to your directory path
    . ./tool/newspeak_env.sh      # The '. ' at the beginning is required
    
    # Clone the emsdk
    cd $EMSDK/..
    git clone https://github.com/emscripten-core/emsdk.git
    
    # Install the emsdk version 2.0.0
    cd emsdk
    ./emsdk install 2.0.0
    ./emsdk activate 2.0.0
    . ./emsdk_env.sh
    
    # List the emsdk installed
    ./emsdk list
    ```
    
    Note: '2.0.0' is the default supported version of `emsdk`. To use the latest Emscripten SDK, you can replace '2.0.0' with 'latest' in the script above.  BUT, if you do that, you also have to edit the scons build file named `SConstruct` in the `$PRIMORDIALSOUP` directory, and replace the following line
    ```python
       '-s', 'EXPORTED_FUNCTIONS=["_load_snapshot", "_handle_message", "_handle_signal"]',
    ```
    with
    ```python
       '-s', 'EXPORTED_FUNCTIONS=["_load_snapshot", "_handle_message", "_handle_signal", "_free", "_malloc"]',
       '-s', 'EXPORTED_RUNTIME_METHODS=["stringToUTF8"]',
    ```
    to be clear, the first (default) works with `emsdk` version '2.0.0', the second with 'latest'. As of February 12 2024, 'latest' emsdk corresponds to version '3.1.53'.

3. **Build Primordialsoup (optional):** You can now build primordialsoup to make sure everything installed. This step is not necessary as Primordialsoup build is part of the Newspeak build in the next section - but running it should catch any dependencies issues early.

    ```sh
    cd ~/software/nswasm/primordialsoup # Adjust to your directory path
    . ../newspeak/tool/newspeak_env.sh  # Set EMSDK var for next line
    . $EMSDK/emsdk_env.sh               # Setup emsdk's environment
    ./build os=emscripten arch=wasm     # Build wasm using emscripten
    ```
    
    There should be no errors in the last step, and you should see directories in the `out` directory under `primordialsoup`, notably there should be files `primordialsoup/out/ReleaseEmscriptenWASM/{primordialsoup.html,primordialsoup.js,primordialsoup.wasm}` and `primordialsoup/out/snapshots/WebCompiler.vfuel` which are used in the Newspeak build. If there are errors, you may be missing some `primordialsoup` dependencies described in the section above.
    

Note: For original instructions of Primordialsoup dependencies that include Fuchsia as a target, follow the instructions at <https://github.com/newspeaklanguage/primordialsoup/blob/master/docs/building.md>.

## 3.2 Building and deploying Newspeak applications: lifecycle

The above section [Building Newspeak: installing required software](#3.1-building-newspeak:-installing-required-software) including its subsection [Building Newspeak: installing Primordialsoup dependencies](#3.1.1-building-newspeak:-installing-primordialsoup-dependencies) **only needs to be performed once during installation**. 

This section and sections below describe the repeated 'build', 'deploy', 'serve' lifecycle of Newspeak applications.

**Important:** All scripts to build and deploy a Newspeak application are in the `newspeak/tool` directory, and must be executed from the `newspeak/tool` directory. The Newspeak IDE is only one possible Newspeak application.

The term **build** refers to the process which creates the `.vfuel`
binary files from the application source `.ns` files.  The script
`newspeak/tool/build.sh` is the build script. You need to run a 'build' to regenerate the application's `.vfuel`
file.

Before creating a `.vfuel`, you should ensure that you have
saved any modified source code it depends upon, be it one of the Newspeak core classes, or a class that is a part of your application.

The term **deploy** refers to the process of copying the Newspeak application `.vfuel` file and other files and resources (`.html`, `.js`, `.png`) to the 'deploy directory' where an HTTP server is or will be running.  The 'deploy' step also copies scripts that can start an HTTP server to the 'deploy directory'.  Newspeak applications can be deployed in two ways: as a regular website or as a Progressive Web App (PWA). 
- *Deploying as a website*: is performed by the script `deploy-all-vfuels-as-website.sh`.  Running this script deploys all `.vfuel` files built by the script `newspeak/tool/build.sh`.
- *Deploying as a PWA*: Currently, only the Newspeak IDE application
  binary `HopscotchWebIDE.vfuel` (referred to as `webIDE`) can be
  deployed and served as a PWA out of the box. This deployment of the
  `webIDE` is performed by the script
  `newspeak/tool/deploy-webide-vfuel-as-pwa.sh`.

Note: If you want to deploy other application's `.vfuel` as a PWA, you can clone the directory structure under [webIDE](https://github.com/newspeaklanguage/newspeak/tree/master/platforms/webIDE), rename it, make changes to `index.html`, `manifest.json`, `sw.js`, `primordialsoup-setup.js`, remove files not applicable to your application, and replace `HopscotchWebIDE.vfuel` with your application's `.vfuel`. 

Refer to section [4. Building, deploying, and serving Newspeak application(s)](4.-Building,-deploying,-and-serving-Newspeak applications) for more details regarding the two deployment methods.

The term **serve** refers to running the HTTP server in a directory
where the Newspeak application was 'deploy'ed. You also need to start
the HTTP server in the 'deployment directory' in order to run the
application outside the development environment.



## 3.3 Building Newspeak applications: the build.sh script

The script `newspeak/tool/build.sh` builds primordialsoup, followed by building the `.vfuel` files listed in the script, then copies the `.vfuel` files to the `newspeak/out` directory along with other files needed to serve the application in the `.vfuel` binary. It **must** be executed from the `newspeak/tool` directory. 

Below are two examples of building:

1. **The default build:** This works out of the box, as described above.  Use this if you are starting to build Newspeak.
    ```sh 
    cd ~/software/nswasm/newspeak # Adjust to your directory path
    cd tool
    ./build.sh
    ```
2. **The extended build:**  Can be used to build your own application's `.vfuel`. As an example, your application is in class 'CheckedItemApp' (saved to the file 'CheckedItemApp.ns').  You can build its `.vfuel` either by editing the 'build.sh' and adding the appropriate line, or using this extended method. The arguments are one or more 3-tuples describing the runtime, the application class, and the vfuel name. Here is the example build.
    ```sh 
    cd ~/software/nswasm/newspeak # Adjust to your directory path
    cd tool
    ./build.sh RuntimeForHopscotchForHTML CheckedItemApp CheckedItemApp.vfuel
    ```

# 4. Building, deploying, and serving Newspeak applications

As described in [Building and deploying Newspeak: lifecycle](#Building-and-deploying-Newspeak-applications:-lifecycle), Newspeak applications can be deployed and served as a Progressive Web App (PWA), or a 'regular' website.  Currently, only the Newspeak IDE application, the `webIDE`, can be deployed and served as a PWA out of the box.

Reflecting the above, there are two 'deploy' scripts, `deploy-webide-vfuel-as-pwa.sh` and `deploy-all-vfuels-as-website.sh`. Both require an argument containing a name of the directory from which the Newspeak applications are served by the script `serve-newspeak.sh`. The first (PWA) deploy script also requires a name of the PWA version file (usually 'localhost'; otherwise 'newspeaklanguage.org', 'myApp.com' or similar).


## 4.1 Building, deploying, and serving Newspeak IDE as a Progressive Web Application (PWA)

Currently, only the Newspeak IDE application binary
`HopscotchWebIDE.vfuel` can be deployed and served as a PWA out of the
box (any other `.vfuel` application you have can be deployed as a website, see later items).

The PWA deployment of the `HopscotchWebIDE.vfuel` is performed by the script `newspeak/tool/deploy-webide-vfuel-as-pwa.sh`. 

Read and run the following script steps to *build*, *deploy*, and *serve* the `HopscotchWebIDE.vfuel` as a **PWA**. 

Assuming you started the application server for the PWA app on port 8081 in the script steps below, the application can be accessed at a URL <http://localhost:8081/webIDE>. 

```sh
# Build Step: 
#   Should be run at least once, and after any change to a Newspeak source file.
#   Builds all '.vfuel' files listed in the 'build.sh' 
#   and places them to the 'out' directory. 
#   Note: The listed '.vfuel' files include the 'HopscotchWebIDE.vfuel'.

cd ~/software/nswasm/newspeak # Adjust to your directory path
cd tool
./build.sh
   
# Deploy Step:
#
#   Deploys the 'HopscotchWebIDE.vfuel' as a Progressive Web App (PWA) (as opposed to a website).
#   Copies all built files to the Newspeak HTTPs server directory
#   specified in the first argument, and updates the PWA Service Worker version file
#   specified in the second argument. The updated version is used as the PWA cache version.
#   By 'All built files' we mean the 'HopscotchWebIDE.vfuel' and miscellaneous js and html files
#   supporting the PWA, as well as the script 'serve-newspeak.sh', which starts the HTTP server.
#
# Arguments:
#
#   1. http-server-dir
#   2. pwa-version-file 
#   See function 'args_parse_for_deploy_as_pwa' for details
#
# Usage Examples:
#
#   1. Deploy files to server running from
#      the '~/servers/newspeak-http-server' directory, serving as 'localhost'
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
#      *you ONLY need to run the 'deploy' script once, after, just keep running the 'build.sh' script.*
#      - cd tool
#      - ./deploy-webide-vfuel-as-pwa.sh  ../out  localhost

httpServerRunPath=~/servers/newspeak-http-server # Adjust to where you want HTTP server running

./deploy-webide-vfuel-as-pwa.sh $httpServerRunPath localhost

# Start HTTP server: 
# 
#   One time only - rerunning the above 'Build step' and 'Deploy step' does not
#                    require server restart

cd "$httpServerRunPath"
./serve-newspeak.sh 8081

# Next: If your './serve-newspeak.sh 8081' serves 'localhost', (then your second argument 
#       to './deploy-webide-vfuel-as-pwa.sh' should also be 'localhost'), and you can 
#       access the webIDE binary `HopscotchWebIDE.vfuel` from the browser as:
#
#     http://localhost:8081/webIDE
#
```

Running the above commands would build, deploy, and serve the `HopscotchWebIDE.vfuel` as a PWA.
    
## 4.2 Building, deploying, and serving any Newspeak application (.vfuel) as a website
    
The script `newspeak/tool/deploy-all-vfuels-as-website.sh` deploys all `.vfuel` files built and copied into the `newspeak/out` directory as a **website**.

Read and run the following script steps to *build*, *deploy*, and *serve* any `.vfuel` application as a **website**.

Assuming you started the application server for the website on port 8081 in the script steps below, each built `.vfuel` file can be accessed similar to <http://localhost:8081/primordialsoup.html?snapshot=HopscotchWebIDE.vfuel>, <http://localhost:8081/primordialsoup.html?snapshot=CounterApp.vfuel>, etc.

```sh
# Build Step: 
#   Should be run at least once, and after any change to a Newspeak source file.
#   Builds all '.vfuel' files listed in the 'build.sh' 
#   and places them to the 'out' directory. 

cd ~/software/nswasm/newspeak # Adjust to your directory path
cd tool
./build.sh
   
# Deploy Step:
#
#   Deploys all '.vfuel' files listed in 'build.sh' as a website (as opposed to PWA).  
#   Copies all built files to the Newspeak HTTPs server directory
#   specified in the first argument.
#   By 'All built files' we mean all '.vfuel' files built by 'build.sh',
#   and miscellaneous js and html files supporting the website.
#
# Arguments:
#
#   1. http-server-dir
#   Note: there is no need for the second argument as in the PWA script -
#         we do not need a PWA version number.
#   See function 'args_parse_for_deploy_as_website' for details
#
# Usage Examples:
#   1. Deploy files to server running from
#      the '~/servers/newspeak-http-server' directory
#     - cd tool
#     - ./deploy-all-vfuels-as-website.sh  ~/servers/newspeak-http-server
#   2. Deploy files to server running from
#      the '../out' directory.
#      This mimicks (I think) how the server ran before this change 
#      The advantage of serving from the '../out' directory is that 
#      *You ONLY need to run this 'deploy' script once, after, just keep running the 'build.sh' script.*
#     - cd tool
#     - ./deploy-all-vfuels-as-website.sh  ../out

httpServerRunPath=~/servers/newspeak-http-server # Adjust to where you want HTTP server running

./deploy-all-vfuels-as-website.sh $httpServerRunPath

# Start HTTP server: 
# 
#   One time only - rerunning the above 'Build step' and 'Deploy step' does not
#                    require server restart

cd "$httpServerRunPath"
./serve-newspeak.sh 8081

# Next: If your './serve-newspeak.sh 8081' serves 'localhost',
#       you can access the '.vfuel' application from the browser as:
#
#     http://localhost:8081/primordialsoup.html?snapshot=HopscotchWebIDE.vfuel
#     http://localhost:8081/primordialsoup.html?snapshot=CounterApp.vfuel
#     etc
#
```

