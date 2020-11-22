
import Cocoa
import SwiftUI

import GCDWebServer

protocol feedBack {
    func output()
}

@NSApplicationMain
class AppDelegate: NSObject, NSApplicationDelegate {
    
    var window: NSWindow!
    var server: GCDWebServer!
    
    func applicationDidFinishLaunching(_ aNotification: Notification) {
        // Create the SwiftUI view that provides the window contents.
        let contentView = ContentView()
        
        // Create the window and set the content view.
        window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 480, height: 300),
            styleMask: [.titled, .closable, .miniaturizable, .resizable, .fullSizeContentView],
            backing: .buffered, defer: false)
        window.isReleasedWhenClosed = false
        window.center()
        window.setFrameAutosaveName("Main Window")
        window.contentView = NSHostingView(rootView: contentView)
        window.makeKeyAndOrderFront(nil)
        
        server = GCDWebServer()
        server.addGETHandler(forBasePath: "/",
                                directoryPath: Bundle.main.resourcePath!,
                                indexFilename: "primoridalsoup.html",
                                cacheAge: 3600,
                                allowRangeRequests: true)
                
        server.start(withPort: 1234, bonjourName: "Hopscotch")
    }
    
    func applicationWillTerminate(_ aNotification: Notification) {
    }
    
}


struct AppDelegate_Previews: PreviewProvider {
    static var previews: some View {
        /*@START_MENU_TOKEN@*/Text("Hello, World!")/*@END_MENU_TOKEN@*/
    }
}
