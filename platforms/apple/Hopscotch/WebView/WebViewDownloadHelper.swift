
import Foundation
import WebKit

struct MimeType {
    var type:String
    var fileExtension:String
}

protocol WKWebViewDownloadHelperDelegate {
    func fileDownloadedAtURL(url:URL)
}

class WKWebviewDownloadHelper : NSObject {
    
    var webView : WKWebView
    var mimeTypes : [MimeType]
    var delegate :WKWebViewDownloadHelperDelegate
    
    init(webView:WKWebView, mimeTypes:[MimeType], delegate:WKWebViewDownloadHelperDelegate) {
        self.webView = webView
        self.mimeTypes = mimeTypes
        self.delegate = delegate
        super.init()
        webView.navigationDelegate = self
    }
    
    private func downloadData(fromURL url:URL,
                              fileName:String,
                              completion:@escaping (Bool, URL?) -> Void) {
        webView.configuration.websiteDataStore.httpCookieStore.getAllCookies() { cookies in
            let session = URLSession.shared
            session.configuration.httpCookieStorage?.setCookies(cookies, for: url,
                                                                mainDocumentURL: nil)
            let task = session.downloadTask(with: url) { localURL,
                                                         urlResponse,
                                                         error in
                if let localURL = localURL {
                    let destinationURL = self.moveDownloadedFile(url: localURL,
                                                                 fileName: fileName)
                    completion(true, destinationURL)
                }
                else {
                    completion(false, nil)
                }
            }
            
            task.resume()
        }
    }
    
    private func getDefaultFileName(forMimeType mimeType:String) -> String {
        for record in self.mimeTypes {
            if mimeType.contains(record.type) {
                return "default." + record.fileExtension
            }
        }
        return "default"
    }
    
    private func getFileNameFromResponse(_ response:URLResponse) -> String? {
        if let httpResponse = response as? HTTPURLResponse {
            let headers = httpResponse.allHeaderFields
            if let disposition = headers["Content-Disposition"] as? String {
                let components = disposition.components(separatedBy: " ")
                if components.count > 1 {
                    let innerComponents = components[1].components(separatedBy: "=")
                    if innerComponents.count > 1 {
                        if innerComponents[0].contains("filename") {
                            return innerComponents[1]
                        }
                    }
                }
            }
        }
        return nil
    }
    
    private func isMimeTypeConfigured(_ mimeType:String) -> Bool {
        for record in self.mimeTypes {
            if mimeType.contains(record.type) {
                return true
            }
        }
        return false
    }
    
    private func moveDownloadedFile(url:URL, fileName:String) -> URL {
        let tempDir = NSTemporaryDirectory()
        let destinationPath = tempDir + fileName
        let destinationURL = URL(fileURLWithPath: destinationPath)
        try? FileManager.default.removeItem(at: destinationURL)
        try? FileManager.default.moveItem(at: url, to: destinationURL)
        return destinationURL
    }
}

extension WKWebviewDownloadHelper: WKNavigationDelegate {
    
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
