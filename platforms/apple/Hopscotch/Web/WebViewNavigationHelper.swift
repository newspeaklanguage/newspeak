
import Foundation
import WebKit

struct MimeType {
    var type:String
    var fileExtension:String
}

protocol WebViewNavigationHelperDelegate {
    func fileDownloadedAtURL(url:URL)
}

class WebViewNavigationHelper : NSObject {
    
    var webView : WKWebView
    var mimeTypes : [MimeType]
    var delegate :WebViewNavigationHelperDelegate
    
    init(webView:WKWebView, mimeTypes:[MimeType], delegate:WebViewNavigationHelperDelegate) {
        self.webView = webView
        self.mimeTypes = mimeTypes
        self.delegate = delegate
        super.init()
        webView.navigationDelegate = self
    }
}

extension WebViewNavigationHelper: WKNavigationDelegate {
    
    func webView(_ webView: WKWebView,
                 decidePolicyFor navigationAction: WKNavigationAction,
                 decisionHandler: @escaping (WKNavigationActionPolicy) -> Void) {
        if let navigationURL = navigationAction.request.url {
            if (navigationURL.absoluteString.contains("blob")) {
                downloadBlob(navigationURL: navigationURL)
                decisionHandler(.cancel)
                return
            }
        }
        decisionHandler(.allow)
    }
        
    func downloadBlob(navigationURL: URL) {
        
        let script = """
            var xhr = new XMLHttpRequest();
            xhr.open('GET', '\(navigationURL.absoluteString)', true);

            xhr.onload = function() {
                if (this.status == 200) {
                    var blob = this.response;
                    window.webkit.messageHandlers.readBlob.postMessage(blob);
                    var reader = new FileReader();
                    reader.readAsBinaryString(blob);
                    reader.onloadend = function() {
                        window.webkit.messageHandlers.readBlob.postMessage(reader.result);
                    }
                }
            };
            xhr.send();
        """
        
        self.webView.evaluateJavaScript(script) { (results, error) in
            
            if let results = results {
                print(results)
            }

            if let error = error {
                print(error)
            }
        }
    }
}
