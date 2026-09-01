#!/usr/bin/env python3
"""Local host-services front door (and CORS proxy for isomorphic-git).

Design: HOST_SERVICES_DESIGN_2026-08-31.md — one origin, reserved /_ns/ paths,
discovery via /_ns/config, capabilities absent unless announced.

Serves two families of paths:

1. The legacy @isomorphic-git/cors-proxy convention, unchanged:
       http://localhost:9999/<host>/<path>   ->   https://<host>/<path>
   Existing clients (the Repositories.ns clone path, local_fetch's proxy
   fallback) keep working untouched, with no token.

2. Reserved host-services paths. '_' is illegal in hostnames, so /_ns/ can
   never collide with a proxied host:
       /_ns/config              discovery: what this origin offers (JSON)
       /_ns/token               the auth token; answered ONLY to loopback
       /_ns/git/<host>/<path>   the git proxy at its permanent address
   Anything else under /_ns/ answers 404 — absent means unavailable.

The token is minted fresh at startup and served at /_ns/token, never written
to disk here and never required for the legacy git convention. Endpoints that
will need it (/_ns/fetch, /_ns/bus) check it via require_token() when they
arrive. /_ns/token answers only to loopback peers, and only to browser
origins whose host is itself loopback — so a public web page scripting
requests at localhost cannot read it.

Binds loopback by default. --bind 0.0.0.0 restores the old any-interface
behavior (the token endpoint still answers loopback only).

Run:
    python3 tool/cors-proxy.py                # loopback:9999
    python3 tool/cors-proxy.py 8888           # loopback:8888
    python3 tool/cors-proxy.py --reflector ws://localhost:9090
                                              # announce local Croquet

Standard-library only. No deps. Intended for development; in production
you'd run the equivalent on the same origin as the deployed IDE.
"""

import argparse
import json
import secrets
import sys
import urllib.request
import urllib.error
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler


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

EXPOSED_RESPONSE_HEADERS = ', '.join(sorted(FORWARDED_RESPONSE_HEADERS))

CORS_HEADERS = [
    ('Access-Control-Allow-Origin', '*'),
    ('Access-Control-Allow-Methods', 'GET, POST, OPTIONS, HEAD, PUT, DELETE, PATCH'),
    ('Access-Control-Allow-Headers',
        'Accept, Accept-Encoding, Accept-Language, Authorization, '
        'Cache-Control, Content-Type, Git-Protocol, Pragma, User-Agent, '
        'X-HTTP-Method-Override, X-NS-Token'),
    ('Access-Control-Expose-Headers', EXPOSED_RESPONSE_HEADERS),
    ('Access-Control-Max-Age', '600'),
]

LOOPBACK_PEERS = {'127.0.0.1', '::1', '::ffff:127.0.0.1'}
LOOPBACK_ORIGIN_HOSTS = {'localhost', '127.0.0.1', '[::1]'}

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


class HostServicesHandler(BaseHTTPRequestHandler):

    server_version = 'ns-host/0.2'

    # ---- routing ---------------------------------------------------------

    def _route(self, method):
        if self.path == '/_ns/config' or self.path.startswith('/_ns/config?'):
            return self._serve_config(method)
        if self.path == '/_ns/token' or self.path.startswith('/_ns/token?'):
            return self._serve_token(method)
        if self.path.startswith('/_ns/git/'):
            return self._forward(method, self.path[len('/_ns/git/'):])
        if self.path == '/_ns' or self.path.startswith('/_ns/'):
            # Absent means unavailable: an unknown /_ns/ path is a capability
            # this origin does not offer, not a proxy target.
            return self._send_json(404, {'error': 'no such host service'})
        # Legacy convention: /<host>/<path>.
        return self._forward(method, self.path.lstrip('/'))

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

    # ---- the proxy (legacy and /_ns/git/) --------------------------------

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

    # ---- verbs -----------------------------------------------------------

    def do_GET(self):    self._route('GET')
    def do_POST(self):   self._route('POST')
    def do_HEAD(self):   self._route('HEAD')
    def do_PUT(self):    self._route('PUT')
    def do_DELETE(self): self._route('DELETE')
    def do_PATCH(self):  self._route('PATCH')

    def do_OPTIONS(self):
        self.send_response(204)
        for name, value in CORS_HEADERS:
            self.send_header(name, value)
        self.send_header('Content-Length', '0')
        self.end_headers()

    def log_message(self, fmt, *args):
        sys.stderr.write(f'[ns-host] {self.command} {self.path} -> {fmt % args}\n')


def main():
    parser = argparse.ArgumentParser(description='Newspeak host-services front door')
    parser.add_argument('port', nargs='?', type=int, default=9999)
    parser.add_argument('--bind', default='127.0.0.1',
                        help='interface to bind (default loopback; 0.0.0.0 for the old any-interface behavior)')
    parser.add_argument('--reflector', default=None,
                        help='announce a local Croquet reflector, e.g. ws://localhost:9090')
    parser.add_argument('--croquet-files', default='/files',
                        help='origin-relative Croquet file-server path (announced only with --reflector)')
    args = parser.parse_args()

    if args.reflector:
        CONFIG['croquet'] = {'reflector': args.reflector, 'files': args.croquet_files}

    server = ThreadingHTTPServer((args.bind, args.port), HostServicesHandler)
    print(f'host services listening on http://{args.bind}:{args.port}')
    print(f'  discovery:  /_ns/config -> {json.dumps(CONFIG)}')
    print(f'  token:      /_ns/token (loopback clients only)')
    print(f'  git proxy:  /_ns/git/<host>/<path> and legacy /<host>/<path> -> https://<host>/<path>')
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nShutting down.')


if __name__ == '__main__':
    main()
