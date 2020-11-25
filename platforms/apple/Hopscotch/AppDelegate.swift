
import Cocoa
import SwiftUI

protocol feedBack {
    func output()
}

@NSApplicationMain
class AppDelegate: NSObject, NSApplicationDelegate {
        
    var window: NSWindow!
    var server: GCDWebServer!
    
    private var contentView : ContentView!
    
    private let runtimeKey = "runtime"
    private let runtimeName = "vm"
    
    func applicationDidFinishLaunching(_ aNotification: Notification) {

        self.contentView = ContentView()

        window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 480, height: 300),
            styleMask: [.titled,
                        .closable,
                        .miniaturizable,
                        .resizable,
                        .fullSizeContentView],
            backing: .buffered,
            defer: false)
        window.isReleasedWhenClosed = false
        window.tabbingMode = .disallowed
        window.center()
        window.setFrameAutosaveName("Main Window")
        window.contentView = NSHostingView(rootView: contentView)
        window.makeKeyAndOrderFront(nil)
        
        if self.hasUserRuntimePath() {
            self.loadRuntime()
        } else {
            self.selectRuntimeDestination()
        }
    }
    
    private func runtimeBundlePath() -> String {
        if let path = Bundle.main.resourcePath {
            return path + "/" + self.runtimeName
        } else {
            let alert: NSAlert = NSAlert()
            alert.messageText = "Unable to locate Newspeak environment."
            alert.beginSheetModal(for: self.window) { _ in
            }
        }
        return ""
    }
    
    private func runtimePath() -> String {
        
        let defaults = UserDefaults.standard
        if let path = defaults.string(forKey: self.runtimeKey) {
            if !path.isEmpty {
                return path
            }
        }
        return self.runtimeBundlePath()
    }
    
    private func hasUserRuntimePath() -> Bool {
        let defaults = UserDefaults.standard
        if let path = defaults.string(forKey: self.runtimeKey) {
            if !path.isEmpty {
                if (FileManager.default.fileExists(atPath: path)) {
                    return true
                } else {
                    defaults.removeObject(forKey: self.runtimeKey)
                }
            }
        }
        return false
    }

    private func selectRuntimeDestination() {
        
        let openPanel = NSOpenPanel()
        openPanel.canChooseFiles = false
        openPanel.canChooseDirectories = true
        openPanel.beginSheetModal(for: self.window, completionHandler: {
            result in if result == .OK {
                if let url = openPanel.url {
                    self.copyRuntime(url)
                }
            }
            self.loadRuntime()
        })
    }
    
    private func copyRuntime(_ url : URL) {
        
        let fileManager = FileManager.default
        let destination = url.path + "/" + self.runtimeName
        if (fileManager.fileExists(atPath: destination)) {
            let alert: NSAlert = NSAlert()
            alert.messageText = "Runtime already exists at location."
            alert.beginSheetModal(for: self.window) { _ in
            }
            return
        }

        let runtimePath = self.runtimeBundlePath()
        if runtimePath.isEmpty{
            self.alertRuntimeNotFound()
        } else {
            do {
                let source = URL(fileURLWithPath: runtimePath)
                let dest = URL(fileURLWithPath: destination)
                try fileManager.copyItem(at: source, to: dest)
                
                let defaults = UserDefaults.standard
                defaults.set(destination, forKey: self.runtimeKey)
            }
            catch let error as NSError {
                print("\(error)")
                self.alertRuntimeNotCreated()
                return
            }
        }
    }
    
    private func loadRuntime() {
        
        let path = self.runtimePath()
        if !path.isEmpty {
            GCDWebServer.setLogLevel(3)
            server = GCDWebServer()
            server.addGETHandler(forBasePath: "/",
                                 directoryPath: path,
                                 indexFilename: "",
                                 cacheAge: 0,
                                 allowRangeRequests: true)
            server.start(withPort: 1234, bonjourName: "Hopscotch")
            
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.5, execute: {
                self.contentView.load()
                print("Loaded runtime: \(path)")
            })
            
        } else {
            self.alertRuntimeNotCreated()
        }
    }
    
    private func alertRuntimeNotFound() {
        let alert: NSAlert = NSAlert()
        alert.messageText = "Unable to locate Newspeak environment "
        alert.beginSheetModal(for: self.window) { _ in
        }
    }
    
    private func alertRuntimeNotCreated() {
        let alert: NSAlert = NSAlert()
        alert.messageText = "Unable to create Newspeak environment "
        alert.beginSheetModal(for: self.window) { _ in
        }
    }
}

struct AppDelegate_Previews: PreviewProvider {
    static var previews: some View {
        /*@START_MENU_TOKEN@*/Text("Hello, World!")/*@END_MENU_TOKEN@*/
    }
}
