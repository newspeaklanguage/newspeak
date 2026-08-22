# An internet-visible Croquet server — options and tradeoffs

2026-08-20. Companion to `CROQUET_NOTES.md`, which covers running everything
locally. Nothing in our code needs to change for any option below: `reflector=`
and `files=` already accept arbitrary URLs.

## The pieces that must be reachable

1. **The reflector** — `node reflector.js`, plain WebSocket on port 9090
   (hardcoded in `reflector.js`; behind a proxy this is irrelevant, the proxy
   listens wherever and forwards to 9090). Run it under systemd/pm2 so it
   survives reboots.
2. **The file server** — `server3.py` (PUT/GET under `files/`) or nginx with
   `dav_methods PUT; create_full_put_path on;`. This is **not optional**: since
   the large-payload detour (2026-08-20), editor keystrokes in large buffers
   route through it, so collaborative editing requires it, not just
   drag-and-drop.
3. **The page and assets** — `croquetpsoup.{html,js,wasm}`, vfuels, CodeMirror,
   images, i.e. the contents of `out/`. Serving them from the same origin as the
   file server avoids CORS questions entirely (though `server3.py` sends
   permissive CORS headers anyway).

## The rule that shapes everything: mixed content

A page served over `https://` may only open `wss://` sockets and make
`https://` fetches. A page served over plain `http://` may use `ws://`. So the
scheme of the *page* dictates whether the reflector needs TLS. Everything else
follows from this.

## Tier 1 — Tailscale: your own devices, anywhere (~10 minutes)

If "internet-visible" means *my* laptop/tablet/second machine from anywhere,
this is the answer. Install Tailscale on the Mac and on each device; the
existing local setup then works unchanged across the tailnet:

```
http://<mac-tailnet-name>:8080/croquetpsoup.html?...&reflector=ws://<mac-tailnet-name>:9090&files=/files
```

- Zero open ports, zero certificates, WireGuard-encrypted.
- Page is `http://`, so `ws://` is allowed — no TLS anywhere.
- Limitation: only devices in the tailnet can join. (Tailscale Funnel can expose
  a single https port publicly, but then the wss problem returns — at that
  point use Tier 3.)

## Tier 2 — one cheap VPS, plain HTTP (~$5/mo)

rsync `out/` and the reflector checkout to a small VPS (Hetzner/DigitalOcean
class); run `server3.py 8080` and the reflector under systemd; open 8080 and
9090. URLs are exactly the local ones with the VPS hostname substituted.

- Works because the page is `http://` (so `ws://` is permitted).
- No TLS: acceptable for personal experiments given Croquet's E2E encryption
  (below), but the URL itself and asset traffic are cleartext.
- Secure-context-gated APIs degrade gracefully: `showSaveFilePicker` is
  unavailable over http, and `safeDownloadBlob` already falls back to the
  `<a download>` path.

## Tier 3 — proper TLS, sharable with anyone

Needs a (sub)domain, e.g. `croquet.bracha.org`. **Caution**: that zone lives in
GoDaddy DNS next to the ForwardEmail SPF/DKIM/_dmarc records — add records, do
not clobber (see `reference_bracha_org_email_dns`).

Pick one of:

- **Caddy on a VPS** — automatic Let's Encrypt, minimal config:

  ```
  croquet.bracha.org {
      handle /reflector* {
          reverse_proxy localhost:9090      # WebSocket upgrade is automatic
      }
      handle /files/* {
          reverse_proxy localhost:8080      # server3.py for PUT/GET
      }
      handle {
          root * /srv/newspeak-out
          file_server
      }
  }
  ```

  URL: `https://croquet.bracha.org/croquetpsoup.html?...`
  `&reflector=wss://croquet.bracha.org/reflector&files=https://croquet.bracha.org/files`

- **Cloudflare Tunnel** (`cloudflared`) from any machine, including the home
  Mac: gives https+wss on your domain with no open inbound ports and no
  certificate management. Two ingress rules (hostname → localhost:8080, a
  second hostname or path → localhost:9090).

- **croquet-in-a-box** (already checked out at
  `../croquet/server/croquet-in-a-box`): Docker Compose bundling reflector +
  nginx web/file server on one port, where `box=/` replaces both `reflector=`
  and `files=`. Still wants Caddy/cloudflared in front for TLS.

## Security realities

- **End-to-end encryption is real**: `pwd=` derives the session key; the
  reflector relays ciphertext and never sees content. The Data API encrypts
  stored blobs with the session key too, so detoured editor payloads and
  dropped files sit encrypted on the file server. Joining a session requires
  knowing sessionId + appId + pwd.
- **But there is no authentication**: anyone who can reach the reflector can
  create sessions and consume bandwidth; anyone who can reach the file server
  can `PUT` (our server3.py PUT is unauthenticated and unbounded — a
  disk-filling invitation on the open internet). For Tier 3, add a size cap
  and/or basic auth on PUT at the proxy, plus a cleanup cron for `files/`.
  Tiers 1–2 largely dodge this via the tailnet / obscurity.
- **Latency**: every interaction round-trips through the reflector; its
  location sets the interactive feel. One VPS near the participants is fine;
  cross-continent collaboration will notice.

## Recommendation

Start with **Tier 1 (Tailscale)** for personal multi-device use — it is ten
minutes and changes nothing. Graduate to **Tier 3 via Cloudflare Tunnel or
Caddy** when a session must be joinable by someone outside the tailnet.
