#!/usr/bin/env python3
"""Minimal CORS proxy for isomorphic-git.

Matches the @isomorphic-git/cors-proxy URL convention:
    http://localhost:9999/<host>/<path>   ->   https://<host>/<path>

Forwards GET/POST (and HEAD/PUT/DELETE/PATCH for completeness), preserves
the headers isomorphic-git needs (Authorization, Content-Type, User-Agent,
etc.), and answers OPTIONS preflights with permissive CORS headers.

Run:
    python3 tool/cors-proxy.py            # listen on 9999
    python3 tool/cors-proxy.py 8888       # listen on 8888

Standard-library only. No deps. Intended for development; in production
you'd run @isomorphic-git/cors-proxy or equivalent on the same origin as
the deployed IDE.
"""

import sys
import urllib.request
import urllib.error
from http.server import HTTPServer, BaseHTTPRequestHandler


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
        'X-HTTP-Method-Override'),
    ('Access-Control-Expose-Headers', EXPOSED_RESPONSE_HEADERS),
    ('Access-Control-Max-Age', '600'),
]


class CorsProxyHandler(BaseHTTPRequestHandler):

    server_version = 'cors-proxy/0.1'

    def _forward(self, method):
        path = self.path.lstrip('/')
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

    def do_GET(self):    self._forward('GET')
    def do_POST(self):   self._forward('POST')
    def do_HEAD(self):   self._forward('HEAD')
    def do_PUT(self):    self._forward('PUT')
    def do_DELETE(self): self._forward('DELETE')
    def do_PATCH(self):  self._forward('PATCH')

    def do_OPTIONS(self):
        self.send_response(204)
        for name, value in CORS_HEADERS:
            self.send_header(name, value)
        self.send_header('Content-Length', '0')
        self.end_headers()

    def log_message(self, fmt, *args):
        sys.stderr.write(f'[cors-proxy] {self.command} {self.path} -> {fmt % args}\n')


def main():
    port = 9999
    if len(sys.argv) > 1:
        port = int(sys.argv[1])
    server = HTTPServer(('0.0.0.0', port), CorsProxyHandler)
    print(f'CORS proxy listening on http://localhost:{port}')
    print(f'URL convention: http://localhost:{port}/<host>/<path>  ->  https://<host>/<path>')
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nShutting down.')


if __name__ == '__main__':
    main()
