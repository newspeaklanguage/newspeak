
import SwiftUI

struct ContentView: View {
    
    @ObservedObject var store = WebViewStore()
    
    var body: some View {        
        WebView(webView: store.webView).onAppear {
        }
        .onAppear() {            
            self.load()
        }
    }
    
    private func load() {
        let appDelegate = NSApplication.shared.delegate as! AppDelegate
        if var url = appDelegate.server.serverURL {
            url.appendPathComponent("primordialsoup.html?snapshot=HopscotchWebIDE.vfuel")
            let request = URLRequest(url: url)
            self.store.webView.load(request)
        }
    }
}

struct ContentView_Previews: PreviewProvider {
    
    static var store = WebViewStore()

    static var previews: some View {
        WebView(webView: store.webView)
    }
}
