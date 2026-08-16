import http.server
import socketserver
import sys

print(sys.argv)
if len(sys.argv) != 2:
    print('Missing port number argument, exiting')
    quit()

PORT = int(sys.argv[1])
print('PORT=', PORT)

class Handler(http.server.SimpleHTTPRequestHandler):
    pass
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
