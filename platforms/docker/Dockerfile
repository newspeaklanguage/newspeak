# Making Newspeak build in a Docker container (author: Mircea Trofimciuc) 
FROM emscripten/emsdk

# Clonning the required repos
RUN git clone https://github.com/newspeaklanguage/newspeak.git
RUN git clone https://github.com/newspeaklanguage/primordialsoup -b extraRevs
RUN git clone https://github.com/codemirror/CodeMirror.git -b 5.62.0

# Installing the primordialsoup dependencies
RUN sudo apt-get update
RUN sudo apt-get -y install g++-multilib scons 

# Installing python
RUN sudo apt install python3.8

# Building primordialsoup
RUN cd primordialsoup && ./build

# Build CodeMirror for JS
RUN cd CodeMirror && npm i && npm run build

# Copying CodeMirror to the right directory
RUN cp -R CodeMirror newspeak/CodeMirror

# Setting emsdk vars
RUN . /emsdk/emsdk_env.sh

# remove the emsdk settings in build
RUN sed '2,6d' newspeak/build.sh > newspeak/new_build.sh

# Building Newspeak 
RUN cd newspeak && chmod 777 new_build.sh && bash new_build.sh

# Serve Newspeak on 8080
# RUN python3 /src/newspeak/server3.py









