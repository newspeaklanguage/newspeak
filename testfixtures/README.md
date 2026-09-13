# Test fixtures

Static files the probe batteries fetch over HTTP. `tool/build.sh` (step 7b)
stages them into `out/`, where the front door (`tool/cors-proxy.py`) serves
them. They live here rather than in `out/` because a clean build wipes `out/`,
and a battery whose fixture has silently vanished fails in a way that looks
like a product bug. The staging is guarded, so a tree without this directory
still builds — it just prints a note and the batteries cannot run.

## `mockai/v1/models`

A fixed OpenAI-style list-models payload, served at
`http://localhost:8080/mockai/v1/models`.

`croquet-probes/model-discovery-battery.js` points `OpenAICompatibleProvider`
at `http://localhost:8080/mockai/v1` as its `baseUrl`. That makes model
discovery testable with **no API key** — OpenAI-compatible providers accept an
empty one, because local servers (Ollama, mlx-omni-server) do not require it —
and against a payload that never changes, so the battery can assert an exact
list rather than whatever a vendor ships today.

Editing this file changes what the battery expects; keep `WANT` in the battery
in step with it.

## `ProbeDoc.zip`

A throwaway Ampleforth document for the coordinated document-load tests,
served at `http://localhost:8080/ProbeDoc.zip` and loaded through
`Documents>>loadFromServerNamed:`.

Derived from `ADoc.zip` by renaming the folder, the inner `.html`, and the
single `name = "ADoc"` attribute — so it is structurally a real document rather
than a hand-built approximation, which the loader would likely reject. It
exists so the tests do not depend on some real document staying in `out/` and
staying unchanged. Its content is irrelevant: the tests assert only that it
loads and that exactly one client fetched the zip.

Note that the document wrapper carries a `classBody` attribute nothing
validates, so do not hand-edit one — derive a new fixture from a real document
the way this one was.
