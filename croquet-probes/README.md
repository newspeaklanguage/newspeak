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

- the front door on :8080 (`python3 tool/cors-proxy.py --bus`) — all of them
  except `bus-locality-probe.js`, which starts its own; `--bus` only for the
  bus probes
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
| `chat-id-divergence-probe.js` | that a presenter's synchronized fragment tree does not change shape with client-local state. Builds a real `ChatStatusPresenter` in each of its states and counts what the minting ledger records; also checks that two clients doing the same things produce identical ledgers, so the ledger is not believed before it is shown not to cry wolf. |
| `bus-locality-probe.js` | that a bus completion goes out from the machine the AGENT is on, not from whichever client the reflector elected. Starts two front doors of its own on 8091/8092 and puts one client behind each; the agent subscribes only to the first. |

## The minting ledger

A synchronized fragment's id *is* its Croquet event address, and it comes from a
per-type counter incremented at construction — so clients agree about which
widget an event names only while they mint in the same order and number
(`CROQUET_SCOPED_FRAGMENT_IDS_2026-08-18.md`). When they stop agreeing, the
failure surfaces much later and somewhere else: "no subscriber for
nsbutton_/533", or a click landing on the wrong widget.

The ledger records the minting sequence so two clients can be diffed directly.
It is **opt-in** — recording costs a bridge crossing per construction — and the
flag is read once before the first fragment exists, so it cannot be switched on
mid-session:

```
localStorage.setItem('ns_mint_ledger', 'on')   // then reload
```

or `&mintLedger=on` in the page URL, which is what the probes pass.

Then, in each client's console:

```js
nsLedgerTotals()             // per-type counts: the cheap first comparison
nsLedgerBlockHashes(500)     // find the first differing block between clients
nsLedgerSlice(from, to)      // read that block; each entry names the presenter
nsLedgerReset()
```

Each entry is `{t: type, o: ordinal, s: scopePath, c: presenter}`. The `c` field
is the point: a bare ordinal says a divergence happened, a label says who caused
it.

`NS_WEB_ROOT` points a probe's own front doors at an alternate copy of `out/`.
Use it to try a runtime change (`croquetpsoup.js`, say) without writing into the
tree a live session is being served from: symlink every entry of `out/` into a
scratch directory, replace the files under test with real copies, and pass the
directory.

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
