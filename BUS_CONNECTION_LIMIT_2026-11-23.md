# Chrome's per-host connection limit and the bus (2026-11-23)

## Symptom

In Gilad's Chrome, pages on `localhost:8080` stopped loading documents: opening a
MenuDirectory toggle showed "Loading …" forever, and "Open in new tab" gave a tab
that spun without ever showing the page. Every document failed alike. The same
URLs worked in Brave, in the Claude app's browser pane, and in headless Chrome.

## Cause (confirmed)

Chrome allows **6 concurrent HTTP/1.1 connections per host**. Requests beyond
that queue until a connection frees up. Every IDE tab holds one connection open
for its whole life: AI_IDE_Support opens an `EventSource` on
`GET /_ns/bus?token=…` (`openBusEventSourceAt:token:`, AI_IDE_Support.ns,
started from `startBus…` once per page) against `tool/cors-proxy.py --bus`. With
enough `localhost:8080` tabs open, the bus streams (and any other long-lived
requests) take all six, and every new request to that host, a menu's `.zip`, even
a new tab's page, waits indefinitely.

Confirmed in Gilad's Chrome: `http://localhost:8080/primordialsoup.html?…` never
committed, while the same page as `http://127.0.0.1:8080/…`, which Chrome counts
as a different host with its own six connections, loaded the full menu at once.
Brave works because it is a separate browser with its own pool.

## Workarounds now

- Close `localhost:8080` tabs (IDE tabs especially), then reload.
- Or use `127.0.0.1:8080` in place of `localhost:8080`: same server, a fresh
  pool. Note that it is a different origin, so its localStorage (API keys,
  drafts) and IndexedDB (saved Eurasia images) are separate from localhost's.

## Permanent fix (to do; host-services / bus owners)

Each tab must not hold its own permanent connection. Options:

1. **One bus connection per browser, shared by its tabs.** A SharedWorker opens
   the single `EventSource` and relays frames to the tabs (or one elected tab
   holds it and relays through a BroadcastChannel, with re-election when it
   closes). The bus token and named-agent addressing need care: the server
   currently treats each SSE connection as a listener (`?name=` on the SSE URL).
2. **HTTP/2.** Multiplexes all requests over one connection, so the per-host
   limit stops mattering. Needs TLS on localhost (a local certificate), and the
   server is `ThreadingHTTPServer` (HTTP/1.1 only), so it would need a different
   server or a TLS-terminating proxy in front.
3. **Open the bus only when used.** Connect when an agent actually needs the
   channel, and close it when idle. This reduces the problem but does not remove
   it while several tabs are active.

Option 1 is the robust one; option 2 removes the class of problem for any other
long-lived request too.

## Also worth checking

Whether anything else holds connections open per tab (long polls, other
EventSources, the Croquet bridge) and whether viewer pages open the bus at all:
a viewer only needs documents, not the agent channel.
