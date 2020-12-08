
import Cocoa
import SwiftUI

protocol feedBack {
    func output()
}

@NSApplicationMain
class AppDelegate: NSObject, NSApplicationDelegate {
        
    var window: NSWindow!
    
    private var contentView : ContentView!
    
    private let runtimeKey = "runtime"
    private let runtimeName = "newspeak"
    
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
        
        self.loadRuntime()
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
        return self.runtimeBundlePath()
    }
    
    private func loadRuntime() {
        
        let path = self.runtimePath()
        if !path.isEmpty {
            let url = URL(fileURLWithPath: path)
            self.contentView.load(url)
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
