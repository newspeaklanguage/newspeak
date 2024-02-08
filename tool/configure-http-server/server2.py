import SimpleHTTPServer
import SocketServer
import sys

print(sys.argv)
if len(sys.argv) != 2:
    print('Missing port number argument, exiting')
    quit()

PORT = int(sys.argv[1])
print('PORT=', PORT)

class Handler(SimpleHTTPServer.SimpleHTTPRequestHandler):
    pass

Handler.extensions_map['.wasm'] = 'application/wasm'

httpd = SocketServer.TCPServer(("", PORT), Handler)

print "my-server.py serving at port", PORT
httpd.serve_forever()
