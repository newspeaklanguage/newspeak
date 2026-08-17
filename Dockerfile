# Stage 1: build PrimordialSoup ----------------------------
FROM emscripten/emsdk:4.0.12 AS psbuild

WORKDIR /src
RUN \
  addgroup --gid 1001 --system app                      && \
  adduser --no-create-home --shell /bin/false              \
    --disabled-password --uid 1001 --system --group app && \
  chown -R app:app /src                                 && \
  apt-get update && apt-get -y --no-install-recommends install g++-multilib scons

ADD https://github.com/newspeaklanguage/primordialsoup/archive/refs/heads/extraRevs.zip /tmp
ADD https://github.com/codemirror/codemirror5/archive/refs/tags/5.62.0.zip /tmp/
RUN chmod +r /tmp/*.zip
USER app

RUN \
  unzip /tmp/extraRevs.zip && mv primordialsoup-extraRevs primordialsoup && \
  cd primordialsoup && ./build os=emscripten arch=wasm                   && \
  unzip /tmp/5.62.0.zip && mv codemirror5-5.62.0 CodeMirror              && \
  echo "cache = /tmp/node_modules/.cache/npm" > /src/CodeMirror/.npmrc   && \
  cd /src/CodeMirror && npm i && npm run build

# Stage 2: build Newspeak ----------------------------------
FROM debian:bookworm-slim AS nsbuild

ARG nsbuilddir=/src/newspeak/out
ARG psbuilddir=/src/primordialsoup/out
ARG psdir=/src/primordialsoup
ARG additionalNs
WORKDIR /src
RUN \
  addgroup --gid 1001 --system app && \
  adduser --no-create-home --shell /bin/false \
    --disabled-password --uid 1001 --system --group app && \
  chown -R app:app /src

USER app
COPY --chown=app:app . /src/newspeak/

COPY --chown=app:app --from=psbuild /src/CodeMirror /src/newspeak/CodeMirror
COPY --chown=app:app --from=psbuild \
  $psbuilddir/ReleaseX64/primordialsoup $psbuilddir/snapshots/WebCompiler.vfuel \
  $psdir/

RUN mkdir $nsbuilddir
COPY --chown=app:app --from=psbuild \
  $psbuilddir/ReleaseEmscriptenWASM/primordialsoup.* \
  $psbuilddir/snapshots/*.vfuel \
  $nsbuilddir/

COPY --chown=app:app --from=psbuild /src/primordialsoup/newspeak/*.ns $nsbuilddir/

RUN \
  cp /src/newspeak/*.ns /src/newspeak/*.png $nsbuilddir/ && \
  cd $nsbuilddir && $psdir/primordialsoup \
    $psdir/WebCompiler.vfuel \
    ./*.ns \
    ./*.png \
    RuntimeForHopscotchForHTML HopscotchWebIDE HopscotchWebIDE.vfuel \
    RuntimeForElectron HopscotchWebIDE HopscotchElectronIDE.vfuel \
    RuntimeForHopscotchForHTML Ampleforth Ampleforth.vfuel  \
    RuntimeForHopscotchForHTML AmpleforthViewer AmpleforthViewer.vfuel  \
    RuntimeForCroquet CounterApp CroquetCounterApp.vfuel \
    RuntimeForHopscotchForHTML CounterApp CounterApp.vfuel \
    RuntimeForHopscotchForHTML TodoMVCApp TodoMVCApp.vfuel \
    RuntimeForCroquet TodoMVCApp CroquetTodoMVCApp.vfuel \
    RuntimeForHopscotchForHTML TwoViewEditorApp TwoViewEditorApp.vfuel \
    RuntimeForHopscotchForHTML TelescreenApp Telescreen.vfuel \
    RuntimeForHopscotchForHTML ObjectPresenterDemo ObjectPresenterDemo.vfuel \
    RuntimeForHopscotchForHTML BankAccountExemplarDemo BankAccountExemplarDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchFontDemo HopscotchFontDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchGestureDemo HopscotchGestureDemo.vfuel \
    RuntimeForHopscotchForHTML HopscotchDemo HopscotchDemo.vfuel \
    RuntimeForHopscotchForHTML Particles Particles.vfuel \
    "$additionalNs"

# stage 3: deployment --------------------------------------
FROM emscripten/emsdk:4.0.12 AS final
RUN addgroup --gid 1001 --system app && \
    adduser --no-create-home --shell /bin/false \
      --disabled-password --uid 1001 --system --group app && \
    chown -R app:app /src

USER app
COPY --chown=app:app --from=nsbuild /src/newspeak/out/ /src/
COPY --chown=app:app \
  platforms/webIDE/public/assets/lib/codemirror.js \
  platforms/webIDE/public/assets/lib/codemirror.css /src/CodeMirror/lib/
COPY --chown=app:app \
  platforms/webIDE/public/assets/lib/codemirror_autorefresh.js \
  /src/CodeMirror/addon/display/autorefresh.js
COPY --chown=app:app docker-entrypoint.sh /
RUN chmod +x /docker-entrypoint.sh
EXPOSE 8080
ENTRYPOINT ["/bin/sh", "/docker-entrypoint.sh"]
