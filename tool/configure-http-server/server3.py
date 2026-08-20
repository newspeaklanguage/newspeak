import http.server
import socketserver
import sys
import os

print(sys.argv)
if len(sys.argv) != 2:
    print('Missing port number argument, exiting')
    quit()

PORT = int(sys.argv[1])
print('PORT=', PORT)

class Handler(http.server.SimpleHTTPRequestHandler):
    # Croquet file server. When a client passes reflector=, getBackend() answers
    # signServer:"none" -- which is what lets us skip API key validation with no
    # key at all -- but uploadServer() then throws "no file server configured".
    # Croquet reads files= ahead of the sign server, so pointing it here restores
    # file storage while staying keyless. Needed for drag-and-drop, file reading
    # and snapshot upload: Croquet events are too small for file payloads, so the
    # data goes to the file server and only a handle travels as an event.
    #
    # nginx in croquet-in-a-box does this with `dav_methods PUT` plus
    # `create_full_put_path`; that is all the protocol amounts to: PUT to store,
    # GET to retrieve. Serving it from this same origin means no CORS is needed,
    # though the headers below are sent anyway so the page can be served from
    # elsewhere. Writes are confined to FILES_PREFIX.
    FILES_PREFIX = '/files/'

    def _cors(self):
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'GET, PUT, OPTIONS')
        self.send_header('Access-Control-Allow-Headers',
                         'DNT,User-Agent,X-Requested-With,If-Modified-Since,'
                         'Cache-Control,Content-Type,Range,X-Croquet-App,'
                         'X-Croquet-Id,X-Croquet-Session,X-Croquet-Version,'
                         'X-Croquet-Path')
        self.send_header('Access-Control-Expose-Headers',
                         'Content-Length,Content-Range')

    def end_headers(self):
        self._cors()
        # no-cache means REVALIDATE, not "don't cache": the browser may keep a
        # copy but must check freshness (If-Modified-Since -> 304) before using
        # it. Without this, browsers apply heuristic freshness and serve stale
        # croquetpsoup.js / .vfuel after a rebuild -- and a stale/fresh MIX of
        # those two crashes Newspeak during boot with a blank screen, since each
        # side calls functions only the other version defines.
        self.send_header('Cache-Control', 'no-cache')
        super().end_headers()

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header('Content-Length', '0')
        self.end_headers()

    def do_PUT(self):
        if not self.path.startswith(self.FILES_PREFIX):
            self.send_error(403, 'PUT is only allowed under %s' % self.FILES_PREFIX)
            return
        # translate_path normalises away '..' and anchors at the serving directory.
        dest = self.translate_path(self.path)
        root = os.path.join(os.getcwd(), self.FILES_PREFIX.strip('/'))
        if os.path.commonpath([os.path.abspath(dest), root]) != root:
            self.send_error(403, 'PUT outside the files directory')
            return
        try:
            os.makedirs(os.path.dirname(dest), exist_ok=True)   # create_full_put_path
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
    # To set top server DIRECTORY, e.g. "webIDE" explicitly, we could use:
    # def __init__(self, *args, **kwargs):
    #     super().__init__(*args, directory=DIRECTORY, **kwargs)
    # By default undefined, which causes start in pwd of the executed script.

Handler.extensions_map['.wasm'] = 'application/wasm'

# ThreadingTCPServer, not TCPServer: the single-threaded server handles one
# connection at a time, and HTTP/1.1 keep-alive means each browser holds its
# connection open. Testing Croquet collaboration needs several browsers at once,
# which wedged the server completely -- every request timing out, so assets like
# CodeMirror and images silently failed to load and apps hung on startup.
class ThreadingHandler(socketserver.ThreadingTCPServer):
    daemon_threads = True      # don't block exit on open keep-alive connections
    allow_reuse_address = True # restart without waiting out TIME_WAIT

with ThreadingHandler(("", PORT), Handler) as httpd:
    print ("Python3: server3.py serving at port", PORT)
    httpd.serve_forever()
