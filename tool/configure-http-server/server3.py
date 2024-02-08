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

with socketserver.TCPServer(("", PORT), Handler) as httpd:
    print ("Python3: server3.py serving at port", PORT)
    httpd.serve_forever()
