# Newspeak on Croquet — running it

Living reference for the collaborative platform described in
`newspeaklanguage.github.io/pubs/newspeak_on_croquet.pdf`. Companion to
`BUILD_NOTES.md`. Last verified 2026-08-16: the IDE syncing live across Chrome,
Safari and Firefox.

## TL;DR

```sh
cd tool && ./run-croquet-reflector.sh          # ws://localhost:9090
```
```
http://localhost:8080/croquetpsoup.html
    ?snapshot=CroquetHopscotchWebIDE.vfuel
    &sessionId=<something-fresh>
    &pwd=<anything>
    &appId=org.newspeaklanguage.ide
    &reflector=ws://localhost:9090
```

## The hosted service is gone; we self-host

- `api.croquet.io` does not answer (HTTP 000, though DNS still resolves).
- `croquet.io/keys` 404s; `multisynq.io` and `/coder` return 403, so no new key
  can be obtained.
- `@croquet/croquet@2.0.4` is the **latest** release and **hardcodes**
  `signServer: "https://api.croquet.io/sign"`. Upgrading does not help; the
  successor package `@multisynq/client` would need a v2 key we cannot get.
- API keys are versioned by their first character: `1…` Croquet, `2…` Multisynq.
  The client rejects anything else with `Invalid API key`.

**Why self-hosting sidesteps all of it** — from the client's `getBackend`:

```js
if (pc.offline)          return {apiKey:"none", signServer:"none", reflector:"none"};
if (h.box || h.reflector) return {apiKey:"none", signServer:"none", reflector:h.reflector};
```

Passing `reflector=` returns *before* the key-format check, and `verifyApiKey`
short-circuits on `signServer === "none"`. **No key is needed or read.**

## URI parameters

| parameter | required | who reads it | what it does |
|---|---|---|---|
| `snapshot` | yes | our boot page | which `.vfuel` to load. Not a Croquet parameter. |
| `reflector` | yes (for us) | Croquet | points at our reflector **and disables key verification** |
| `pwd` | **yes** | Croquet | end-to-end encryption password; `Session.join` throws without it. Never sent to the server; any constant is fine locally. |
| `appId` | yes | Croquet | application identifier, reverse-DNS by convention. Participates in the session id, so two appIds are two different sessions. |
| `sessionId` | yes | Croquet | the session *name*. See the warning below. |
| `files` | **yes, for file handling** | Croquet | file-server base URL. See below. |
| `apiKey` | **present, value ignored** | `Session.join` (presence only) | `Session.join` throws `no apiKey provided` if the option is absent, *before* the `reflector=` branch that ignores its value. So pass `apiKey=none`. Omitting it appears to work only in a browser where `getURIParam` finds an old value in localStorage; a fresh profile shows a blank page. |
| `box` | alternative | Croquet | Croquet-in-a-Box; same key-skipping branch as `reflector` |
| `debug` | optional | Croquet | e.g. `debug=session,snapshots` |

**Use a fresh `sessionId` per test run.** The actual session id is derived from
name + appId + a hash of the code, so reusing a name across apps can collide —
we saw `CroquetCounterApp` and the IDE land on the same id. Worse, a session
carries a stored **event history** that replays into every joining client (see
§3.1 of the paper: our state is in the Newspeak heap, not the Croquet model, so
we replay events rather than restore a snapshot). Stale sessions therefore
resurrect old events and produce slow, divergent, browser-dependent startups.

## The file server (`files=`)

Drag-and-drop, file reading and snapshot upload all need one: Croquet events are
too small to carry file payloads, so the data is stored on a file server and only a
handle travels as an event (paper §3.2.1).

There is a catch in how the client resolves it:

```js
uploadServer(t) {
  if ("string" == typeof h.files) { ...return {url, apiKey: null} }
  const {apiKey, signServer} = this.getBackend(t);
  if ("none" === signServer && !pc.offline) throw Error("no file server configured");
```

The file server **is** the sign server — so the very `reflector=` branch that frees
us from an API key also removes file storage, and any file operation fails with
`no file server configured`. But `files=` is consulted *first*, so passing it
restores file handling while staying keyless.

`out/server3.py` implements it: `PUT` to store (creating intermediate
directories), `GET` to retrieve, confined to `out/files/`. That is the whole
protocol — nginx in croquet-in-a-box does it with `dav_methods PUT` plus
`create_full_put_path`. Serving it from the same origin as the page means no CORS
is required, though the headers are sent anyway. Add to the URL:

```
&files=http://localhost:8080/files
```

The alternative is croquet-in-a-box (`../croquet/server/croquet-in-a-box`), a
Docker Compose bundle of reflector + web server + file server on port 8888, where
`box=/` replaces both `reflector=` and `files=`.

## The reflector

Apache-2.0, from `github.com/croquet/croquet`, checked out at `../croquet`
(`packages/reflector`, `@croquet/reflector` 2.6.2). `tool/run-croquet-reflector.sh`
starts it, installing dependencies on first run.

- Port **9090** is hardcoded in `reflector.js` (`const PORT = 9090`) with no CLI or
  environment override.
- Runs with `--standalone --storage=none --no-loglatency`: no Google Cloud
  dependencies, snapshots in memory only.
- Logs raw JSON, one object per line — grep it:
  `grep '"event":"join"' reflector.log`. Useful events: `join`, `user-joined`,
  `send-sync`, `end`.
- **For cross-device use**, run it on an internet-reachable host and point
  `reflector=` at it. No key, no account, no domain registration. Note `ws://`
  from an `https://` page is blocked — that needs `wss://` and a certificate.
  Options and tradeoffs (Tailscale / plain-HTTP VPS / TLS via Caddy or
  Cloudflare Tunnel) in `CROQUET_INTERNET_DEPLOYMENT_2026-08-20.md`.

## Serve with a threaded HTTP server

`out/server3.py` used `socketserver.TCPServer`, which is **single-threaded**. With
HTTP/1.1 keep-alive each browser holds its connection open, so three browsers
wedged the server completely: every request timed out and assets (CodeMirror,
images) silently failed to load, which looked like per-browser Croquet flakiness.
It is now a `ThreadingTCPServer`. Testing collaboration inherently needs several
browsers, so this matters more here than anywhere else.

## Build pipeline

`tool/build.sh` builds the Croquet VM and vfuels; see `BUILD_NOTES.md`. Specifics:

- `primordialsoup/build-croquet.sh` relinks the VM with `meta/croquet-post.js`
  (Croquet model/view) and `meta/croquet-pre.js` (the startup gate) instead of
  `meta/custom-post.js`, producing `croquetpsoup.{html,js,wasm}`.
- **The startup gate.** `HopscotchShell>>setupCroquetView` reads the JS global
  `theView`, but `Session.join` is asynchronous. `croquet-pre.js` holds an
  Emscripten *run dependency* across the join (`Module['preRun']` →
  `addRunDependency`), released in `NewspeakCroquetView`'s constructor via
  `removeRunDependency`. Without it Newspeak boots first and dies with
  `Alien doesNotUnderstand: #addSubscription:eventSpec:handler:`.
- Seven Croquet vfuels are built: IDE, AmpleforthViewer, Counter, TodoMVC and
  three Hopscotch demos.

## Keeping the Croquet copies in step

`HopscotchForCroquet.ns` and `RuntimeForCroquet.ns` are parallel copies of the UI
and runtime modules. They do not fail loudly when the originals grow, and two such
drifts broke startup as recently as 2026-08-16:

- `FileChooserFragment`'s override lacked `public`, **narrowing** a public member.
  Harmless until `AI_IDE_Support` added an eager
  `platform hopscotch FileChooserFragment` import →
  `MessageNotUnderstood: Hopscotch FileChooserFragment`.
- `RuntimeForCroquet` never got `editIcon`, added to the HTML runtime in July →
  `MessageNotUnderstood: Images editIcon`.

When adding a fragment, an image or a platform accessor, check the Croquet copy.
An override must repeat `public`; omitting it narrows access silently.

## Known gaps

- **No Croquet overrides** for `TimerFragment`, `CanvasFragment`,
  `AsyncContentComposer`, `DeferredContentComposer`, `WebTransclusionFragment` or
  `AmpleforthFragment`. These resolve content on client-local timing, which is a
  determinism hazard in a lock-step system. They will not raise — they will
  diverge.
- The AI chat stack has no overrides either; it probably wants
  `NonSyncingPresenter` rather than synchronizing.
- **NS2JS integration: DONE 2026-08-20** (headless 3-browser verification;
  interactive verification pending). `RuntimeForCroquetJS` + the deploy menu's
  *as Croquet Web Page* produce a four-file app whose page gates boot on
  `Session.join` and loads the **self-hosted patched Croquet client**
  (`out/croquet.min.js`) — the stock client is unusable in an NS2JS realm
  because its `$model`/`$class`/`$ref`/`$id`/`$value` serializer sentinels
  collide with `$`-mangled selector catchers on `Object.prototype`. Full
  record, including the three platform bugs found and the client build recipe:
  `CROQUET_NS2JS_INTEGRATION_2026-08-20.md`. Editors/detour/file drop not yet
  exercised on NS2JS; the Croquet IDE as a JS app stays blocked on the WeakRef
  ceiling.
- Offline work is out of scope by design (paper §7).
