#!/usr/bin/env python3
"""Local host-services front door: static IDE serving, /_ns/ services, git proxy.

Design: HOST_SERVICES_DESIGN_2026-08-31.md — one origin, reserved /_ns/ paths,
discovery via /_ns/config, capabilities absent unless announced. Staging step 3
folds static serving in, so this replaces both server3.py (:8080) and the old
standalone CORS proxy (:9999) with ONE process answering on both ports:

The FRONT DOOR (default :8080) serves:
    /                        static files from --root (default <repo>/out),
                             with CORS and Cache-Control: no-cache (no-cache
                             means REVALIDATE: without it browsers serve a
                             stale/fresh MIX of psoup.js + .vfuel after a
                             rebuild and Newspeak crashes on boot)
    /files/...               the Croquet file server: PUT stores (with
                             create_full_put_path semantics), GET retrieves.
                             Croquet reads files= ahead of the sign server,
                             which restores keyless file storage when
                             reflector= is passed; events are too small for
                             file payloads, so blobs live here and only a
                             handle travels as an event
    /_ns/config              discovery: what this origin offers (JSON)
    /_ns/token               the auth token; answered ONLY to loopback
    /_ns/git/<host>/<path>   the git proxy at its permanent address
    (anything else under /_ns/ answers 404 — absent means unavailable)

The LEGACY listener (default :9999, --legacy-port 0 to disable) additionally
answers the old bare @isomorphic-git/cors-proxy convention —
    http://localhost:9999/<host>/<path>   ->   https://<host>/<path>
— for the clients that still point at it (per-repository proxy fields,
local_fetch's fallback, Host.ns's dev fallback). It serves /_ns/ too, no
static. It retires once those defaults migrate to /_ns/git on the front door.

The token is minted fresh at startup, never written to disk, never required
for git or static. Endpoints that will need it (/_ns/fetch, /_ns/bus) check
it via require_token(). /_ns/token answers only to loopback peers and only
to browser origins that are themselves loopback.

Binds loopback by default. --bind 0.0.0.0 restores server3.py's any-interface
reach (needed for phone / cross-device Croquet days; the token endpoint still
answers loopback only, but git proxying and /files writes are then open to
the LAN — the pre-existing dev tradeoff, now opt-in).

Run (from the newspeak repo root or anywhere — --root defaults beside tool/):
    python3 tool/cors-proxy.py                      # :8080 front door + :9999 legacy
    python3 tool/cors-proxy.py --bind 0.0.0.0       # cross-device day
    python3 tool/cors-proxy.py --reflector ws://localhost:9090   # announce Croquet

Standard-library only. No deps. Intended for development; in production
you'd run the equivalent on the same origin as the deployed IDE.
"""

import argparse
import functools
import json
import os
import secrets
import sys
import threading
import urllib.request
import urllib.error
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler


# Headers we forward from the browser request to the upstream git server.
# Case is normalized to lowercase below.
FORWARDED_REQUEST_HEADERS = {
    'accept',
    'accept-encoding',
    'accept-language',
    'authorization',
    'cache-control',
    'content-type',
    'cookie',
    'git-protocol',
    'pragma',
    'user-agent',
    'x-http-method-override',
}

# Headers we surface from the upstream response back to the browser. The
# browser sees them iff they're listed in Access-Control-Expose-Headers.
FORWARDED_RESPONSE_HEADERS = {
    'accept-ranges',
    'cache-control',
    'content-encoding',
    'content-language',
    'content-range',
    'content-type',
    'etag',
    'expires',
    'git-protocol',
    'last-modified',
    'vary',
}

# One merged CORS surface for every response class: the git set, the static
# set server3.py sent (DNT, Range, If-Modified-Since, X-Requested-With), the
# Croquet file-server headers, and our own token header.
ALLOWED_REQUEST_HEADERS = (
    'Accept, Accept-Encoding, Accept-Language, Authorization, Cache-Control, '
    'Content-Type, DNT, Git-Protocol, If-Modified-Since, Pragma, Range, '
    'User-Agent, X-Croquet-App, X-Croquet-Id, X-Croquet-Path, '
    'X-Croquet-Session, X-Croquet-Version, X-HTTP-Method-Override, '
    'X-NS-Token, X-Requested-With')

EXPOSED_RESPONSE_HEADERS = ', '.join(
    sorted(FORWARDED_RESPONSE_HEADERS | {'content-length'}))

CORS_HEADERS = [
    ('Access-Control-Allow-Origin', '*'),
    ('Access-Control-Allow-Methods', 'GET, POST, OPTIONS, HEAD, PUT, DELETE, PATCH'),
    ('Access-Control-Allow-Headers', ALLOWED_REQUEST_HEADERS),
    ('Access-Control-Expose-Headers', EXPOSED_RESPONSE_HEADERS),
    ('Access-Control-Max-Age', '600'),
]

LOOPBACK_PEERS = {'127.0.0.1', '::1', '::ffff:127.0.0.1'}
LOOPBACK_ORIGIN_HOSTS = {'localhost', '127.0.0.1', '[::1]'}

FILES_PREFIX = '/files/'

# Minted per run. The page fetches it from /_ns/token before its first
# token-gated /_ns/* call; nothing is pasted and nothing rests in localStorage.
TOKEN = secrets.token_urlsafe(32)

# Filled from CLI flags in main(); served verbatim by /_ns/config.
CONFIG = {
    'version': 1,
    'git': True,
    'fetch': False,
    'bus': False,
}


class HostServicesHandler(SimpleHTTPRequestHandler):

    server_version = 'ns-host/0.3'
    front_port = 8080          # overwritten in main()

    # Static responses get server3.py's headers appended in end_headers;
    # service/proxy responses manage their own and leave this False.
    _static_headers = False

    # ---- routing ---------------------------------------------------------

    def _handled_as_service(self, method):
        """/_ns/ services on every listener; the bare proxy convention only
        on the legacy listener. Answers True when the request was handled."""
        if self.path == '/_ns/config' or self.path.startswith('/_ns/config?'):
            self._serve_config(method)
            return True
        if self.path == '/_ns/token' or self.path.startswith('/_ns/token?'):
            self._serve_token(method)
            return True
        if self.path.startswith('/_ns/git/'):
            self._forward(method, self.path[len('/_ns/git/'):])
            return True
        if self.path == '/_ns' or self.path.startswith('/_ns/'):
            # Absent means unavailable: an unknown /_ns/ path is a capability
            # this origin does not offer, not a proxy target or a file.
            self._send_json(404, {'error': 'no such host service'})
            return True
        if self.server.server_address[1] != self.front_port:
            # Legacy listener: everything else is the old proxy convention.
            self._forward(method, self.path.lstrip('/'))
            return True
        return False

    # ---- host services ---------------------------------------------------

    def _serve_config(self, method):
        if method not in ('GET', 'HEAD'):
            return self._send_json(405, {'error': 'GET only'})
        self._send_json(200, CONFIG, head_only=(method == 'HEAD'))

    def _serve_token(self, method):
        # Loopback peers only, regardless of the bind address; and browser
        # origins must themselves be loopback, so an arbitrary web page open
        # in the same browser cannot script the token out of us.
        if method not in ('GET', 'HEAD'):
            return self._send_json(405, {'error': 'GET only'})
        if self.client_address[0] not in LOOPBACK_PEERS:
            return self._send_json(403, {'error': 'token is served to loopback clients only'})
        origin = self.headers.get('Origin')
        if origin is not None and not self._is_loopback_origin(origin):
            return self._send_json(403, {'error': 'token is not served to non-local origins'})
        self._send_json(200, {'token': TOKEN},
                        head_only=(method == 'HEAD'),
                        allow_origin=origin)

    @staticmethod
    def _is_loopback_origin(origin):
        # Origin is scheme://host[:port]; compare the host part only.
        hostport = origin.split('://', 1)[-1]
        if hostport.startswith('['):                    # [::1]:8080
            host = hostport.split(']', 1)[0] + ']'
        else:
            host = hostport.split(':', 1)[0]
        return host in LOOPBACK_ORIGIN_HOSTS

    def require_token(self):
        """For token-gated endpoints (/_ns/fetch, /_ns/bus when they land).
        Answers True if the request carries the token; sends 401 otherwise.
        Accepted as an X-NS-Token header or a token= query parameter."""
        supplied = self.headers.get('X-NS-Token')
        if supplied is None and 'token=' in self.path:
            query = self.path.split('?', 1)[-1]
            for part in query.split('&'):
                if part.startswith('token='):
                    supplied = part[len('token='):]
        if supplied == TOKEN:
            return True
        self._send_json(401, {'error': 'missing or wrong token; fetch /_ns/token first'})
        return False

    def _send_json(self, status, payload, head_only=False, allow_origin=None):
        body = json.dumps(payload).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json')
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        if allow_origin is not None:
            # Echo the (already vetted) origin rather than *.
            self.send_header('Access-Control-Allow-Origin', allow_origin)
            self.send_header('Vary', 'Origin')
        else:
            self.send_header('Access-Control-Allow-Origin', '*')
        self.end_headers()
        if not head_only:
            self.wfile.write(body)

    # ---- the git proxy (/_ns/git/ everywhere; bare convention on legacy) --

    def _forward(self, method, path):
        if not path:
            self.send_error(400, 'Bad Request: missing target host')
            return
        host, _, rest = path.partition('/')
        if not host:
            self.send_error(400, 'Bad Request: missing host')
            return
        url = f'https://{host}/{rest}'

        headers = {}
        for raw_name in self.headers:
            if raw_name.lower() in FORWARDED_REQUEST_HEADERS:
                headers[raw_name] = self.headers[raw_name]
        headers.setdefault('User-Agent', self.server_version)

        body = None
        if method in ('POST', 'PUT', 'PATCH'):
            length = int(self.headers.get('Content-Length', '0'))
            if length:
                body = self.rfile.read(length)

        req = urllib.request.Request(url, data=body, method=method, headers=headers)
        try:
            upstream = urllib.request.urlopen(req, timeout=30)
        except urllib.error.HTTPError as e:
            self._send_with_cors(e.code, dict(e.headers or {}))
            try:
                self.wfile.write(e.read())
            except Exception:
                pass
            return
        except urllib.error.URLError as e:
            self.send_error(502, f'Bad Gateway: {e}')
            return

        self._send_with_cors(upstream.status, dict(upstream.getheaders()))
        try:
            while True:
                chunk = upstream.read(64 * 1024)
                if not chunk:
                    break
                self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _send_with_cors(self, status, upstream_headers):
        self.send_response(status)
        for name, value in upstream_headers.items():
            if name.lower() in FORWARDED_RESPONSE_HEADERS:
                self.send_header(name, value)
        for name, value in CORS_HEADERS:
            self.send_header(name, value)
        self.end_headers()

    # ---- static + Croquet file store (front door only) -------------------

    def end_headers(self):
        # server3.py's contract for static content: permissive CORS (the page
        # may be served from elsewhere) and Cache-Control: no-cache, i.e.
        # REVALIDATE (If-Modified-Since -> 304) — see module docstring for
        # the stale-mix boot crash this prevents.
        if self._static_headers:
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Access-Control-Allow-Methods', 'GET, PUT, OPTIONS')
            self.send_header('Access-Control-Allow-Headers', ALLOWED_REQUEST_HEADERS)
            self.send_header('Access-Control-Expose-Headers', 'Content-Length, Content-Range')
            self.send_header('Cache-Control', 'no-cache')
        super().end_headers()

    def _put_file(self):
        # The Croquet file server: PUT to store, GET to retrieve — the whole
        # protocol (nginx's dav_methods PUT + create_full_put_path in
        # croquet-in-a-box). Writes are confined to FILES_PREFIX.
        self._static_headers = True
        if not self.path.startswith(FILES_PREFIX):
            self.send_error(403, 'PUT is only allowed under %s' % FILES_PREFIX)
            return
        # translate_path normalises away '..' and anchors at --root.
        dest = os.path.abspath(self.translate_path(self.path))
        root = os.path.abspath(os.path.join(self.directory, FILES_PREFIX.strip('/')))
        if os.path.commonpath([dest, root]) != root:
            self.send_error(403, 'PUT outside the files directory')
            return
        try:
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            length = int(self.headers.get('Content-Length', 0))
            remaining = length
            with open(dest, 'wb') as f:
                while remaining > 0:
                    chunk = self.rfile.read(min(65536, remaining))
                    if not chunk:
                        break
                    f.write(chunk)
                    remaining -= len(chunk)
        except OSError as e:
            self.send_error(500, 'PUT failed: %s' % e)
            return
        self.send_response(201, 'Created')
        self.send_header('Content-Length', '0')
        self.end_headers()

    # ---- verbs -----------------------------------------------------------

    def do_GET(self):
        if self._handled_as_service('GET'):
            return
        self._static_headers = True
        super().do_GET()

    def do_HEAD(self):
        if self._handled_as_service('HEAD'):
            return
        self._static_headers = True
        super().do_HEAD()

    def do_PUT(self):
        if self._handled_as_service('PUT'):
            return
        self._put_file()

    def do_POST(self):
        if self._handled_as_service('POST'):
            return
        self._send_json(405, {'error': 'POST is not accepted for static paths'})

    def do_DELETE(self):
        if self._handled_as_service('DELETE'):
            return
        self._send_json(405, {'error': 'DELETE is not accepted for static paths'})

    def do_PATCH(self):
        if self._handled_as_service('PATCH'):
            return
        self._send_json(405, {'error': 'PATCH is not accepted for static paths'})

    def do_OPTIONS(self):
        self.send_response(204)
        for name, value in CORS_HEADERS:
            self.send_header(name, value)
        self.send_header('Content-Length', '0')
        self.end_headers()

    def log_message(self, fmt, *args):
        sys.stderr.write(f'[ns-host] {self.command} {self.path} -> {fmt % args}\n')


HostServicesHandler.extensions_map['.wasm'] = 'application/wasm'


def main():
    parser = argparse.ArgumentParser(description='Newspeak host-services front door')
    parser.add_argument('port', nargs='?', type=int, default=8080,
                        help='front-door port: static + /files + /_ns (default 8080)')
    parser.add_argument('--legacy-port', type=int, default=9999,
                        help='extra listener answering the bare cors-proxy convention (default 9999; 0 disables)')
    parser.add_argument('--bind', default='127.0.0.1',
                        help='interface to bind (default loopback; 0.0.0.0 for cross-device days)')
    parser.add_argument('--root', default=None,
                        help='static root (default: the out/ beside this script\'s repo)')
    parser.add_argument('--reflector', default=None,
                        help='announce a local Croquet reflector, e.g. ws://localhost:9090')
    parser.add_argument('--croquet-files', default='/files',
                        help='origin-relative Croquet file-server path (announced only with --reflector)')
    args = parser.parse_args()

    if args.reflector:
        CONFIG['croquet'] = {'reflector': args.reflector, 'files': args.croquet_files}

    root = args.root or os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'out'))
    if not os.path.isdir(root):
        print(f'WARNING: static root {root} does not exist; static requests will 404')

    HostServicesHandler.front_port = args.port
    handler = functools.partial(HostServicesHandler, directory=root)

    if args.legacy_port and args.legacy_port != args.port:
        legacy = ThreadingHTTPServer((args.bind, args.legacy_port), handler)
        threading.Thread(target=legacy.serve_forever, daemon=True).start()
        print(f'legacy proxy listening on http://{args.bind}:{args.legacy_port} '
              f'(bare /<host>/<path> convention, plus /_ns)')

    server = ThreadingHTTPServer((args.bind, args.port), handler)
    print(f'front door listening on http://{args.bind}:{args.port}')
    print(f'  static root: {root} (CORS + no-cache; PUT under {FILES_PREFIX})')
    print(f'  discovery:   /_ns/config -> {json.dumps(CONFIG)}')
    print(f'  token:       /_ns/token (loopback clients only)')
    print(f'  git proxy:   /_ns/git/<host>/<path> -> https://<host>/<path>')
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nShutting down.')


if __name__ == '__main__':
    main()
