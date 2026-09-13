# croquet-probes

Headless-browser probes for the Croquet platform. They drive a real IDE image
over the DevTools protocol, so they exercise the synchronized paths — election,
replay, late join — that no offline test can reach.

## Running one

```
NODE_PATH=<croquet>/packages/reflector/node_modules \
  ~/software/emsdk-main/node/22.16.0_64bit/bin/node croquet-probes/<probe>.js
```

emsdk's node 22, not the system one: the node on PATH here is a broken
homebrew node@12. `NODE_PATH` is only needed by probes that use `ws`.

Prerequisites, depending on the probe:

- the front door on :8080 (`python3 tool/cors-proxy.py --bus`) — all of them;
  `--bus` only for the bus probe
- the reflector on :9090 (`tool/run-croquet-reflector.sh`) — anything Croquet
- `NS_SUFFIX=-TEST` to run against `*-TEST.vfuel` rather than the live
  artifacts, which is what you want while iterating

## The batteries

These are the maintained ones. Each measures at the far end — the provider or
the agent counts the requests it received — rather than trusting a counter
inside the client under test.

| probe | asserts |
|---|---|
| `model-discovery-battery.js` | model discovery on both platforms: plain-platform regression guard, two-client election, late joiner converging from the recorded result, document load, and the deployed (non-loopback, no `/_ns`) shape. `plain` / `static` arguments run one section. |
| `completion-election-probe.js` | an HTTP model completion goes out ONCE per session: two clients get the same reply, a mock provider counts one POST, a late joiner's replay adds none. |
| `bus-election-probe.js` | the same for a bus completion, with the probe itself acting as the external agent on `/_ns/bus`. |

`harness.js` holds what they share: launching Chrome, attaching to the page,
booting the IDE, evaluating a doIt in a workspace, and a pass/fail counter.
Three probes had grown near-identical copies of it.

Fixtures live in `../testfixtures` and are staged into `out/` by
`tool/build.sh`; see the README there.

## The rest

The other files are diagnostics kept from particular investigations — the
eval-stall probes, the fragment-identity and menu probes, the deployment and
parity checks. They are not maintained and many name artifacts that no longer
exist. Read one before trusting it.

## Writing a new one

Two traps worth knowing, both learned the hard way:

- **Assert that the image booted.** A probe that skips this reports whatever a
  blank page reports, and a crashing image quietly passes tests about state it
  never created.
- **Check the observable discriminates.** Before trusting a negative result,
  confirm the same measurement goes the other way in the known-good case. A
  truncated `innerText`, or a count that is identical in both branches, will
  report "unchanged" forever.
