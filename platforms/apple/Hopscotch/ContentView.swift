
import SwiftUI

struct ContentView: View {
    
    @ObservedObject var store = WebViewStore()
    
    var body: some View {        
        WebView(webView: store.webView).onAppear {
        }
    }
    
    func load(_ url: URL) {
        var url = url
        url.appendPathComponent("primordialsoup.html")
        url.appendQueryItem(name: "snapshot", value: "HopscotchWebIDE.vfuel")
        let request = URLRequest(url: url)
        self.store.webView.load(request)
    }
}

struct ContentView_Previews: PreviewProvider {
    
    static var store = WebViewStore()
    
    static var previews: some View {
        WebView(webView: store.webView)
    }
}

extension URL {

    mutating func appendQueryItem(name: String, value: String?) {

        guard var urlComponents = URLComponents(string: absoluteString) else { return }

        var queryItems: [URLQueryItem] = urlComponents.queryItems ??  []
        let queryItem = URLQueryItem(name: name, value: value)
        queryItems.append(queryItem)
        urlComponents.queryItems = queryItems
        self = urlComponents.url!
    }
}
