import Combine
import SwiftUI
import WebKit

public struct WebView: View {
    
    public let webView: WKWebView
    
    public class Coordinator: NSObject,
                              WKScriptMessageHandler,
                              WKUIDelegate,
                              WebViewNavigationHelperDelegate {
        
        private var parent: WebView
        private var helper : WebViewNavigationHelper!
        
        init(_ parent: WebView) {
            self.parent = parent
        }
        
        #if os(macOS)
        public func webView(_ webView: WKWebView,
                            runJavaScriptAlertPanelWithMessage message: String,
                            initiatedByFrame frame: WKFrameInfo,
                            completionHandler: @escaping () -> Void) {
            let alert: NSAlert = NSAlert()
            alert.messageText = message
            alert.beginSheetModal(for: webView.window!) { response in
                completionHandler()
            }
        }
        
        public func webView(_ webView: WKWebView,
                            runOpenPanelWith parameters: WKOpenPanelParameters,
                            initiatedByFrame frame: WKFrameInfo,
                            completionHandler: @escaping ([URL]?) -> Void) {
            let openPanel = NSOpenPanel()
            openPanel.canChooseFiles = true
            openPanel.allowsMultipleSelection = parameters.allowsMultipleSelection
            openPanel.canChooseDirectories = parameters.allowsDirectories
            openPanel.beginSheetModal(for: self.parent.webView.window!,
                                      completionHandler: {
                result in if result == .OK {
//                    var files = [URL]()
//                    for url in openPanel.urls {
//                        files.append(URL(string: url.path)!)
//                    }
                    completionHandler(openPanel.urls)
                } else {
                    completionHandler(nil)
                }
            })
        }
        
        public func webView(_ webView: WKWebView,
                            decidePolicyFor navigationResponse: WKNavigationResponse,
                            decisionHandler: @escaping (WKNavigationResponsePolicy) -> Void) {
            decisionHandler(.allow)
        }
        
        public func userContentController(_ userContentController: WKUserContentController,
                                          didReceive message: WKScriptMessage) {
            if message.name == "logHandler" {
                print("LOG: \(message.body)")
                return
            }

            if message.name == "readBlob" {
                if let text = message.body as? String {

                    let dialog = NSSavePanel()
                    dialog.title = "Save"
                    dialog.showsResizeIndicator = true
                    dialog.beginSheetModal(for: self.parent.webView.window!, completionHandler: {
                        result in if result == .OK {
                            do {
                                try text.write(to: dialog.url!,
                                               atomically: true,
                                               encoding: String.Encoding.utf8)
                            } catch {
                                print("Unable to save file")
                            }
                        }
                    })
                }
                return
            }
        }
        
        public func fileDownloadedAtURL(url: URL) {
        }
        
        public func registerNavigationHelper() {
            let mimeTypes = [MimeType(type: "pdf", fileExtension: "pdf")]
            self.helper = WebViewNavigationHelper(webView: parent.webView,
                                                  mimeTypes:mimeTypes,
                                                  delegate: self)
        }
        #endif
    }
    
    public func makeCoordinator() -> Coordinator {
        Coordinator(self)
    }
    
    func goBack(){
        self.webView.goBack()
    }
    
    func goForward(){
        self.webView.goForward()
    }
    
    func reload(){
        self.webView.reload()
    }
    
    public init(webView: WKWebView) {
        self.webView = webView
    }
}

#if !os(macOS)
// MARK: - UIViewRepresentable

extension WebView: UIViewRepresentable {
    public typealias UIViewType = UIViewContainerView<WKWebView>
    
    public func makeUIView(context: UIViewRepresentableContext<WebView>) -> WebView.UIViewType {
        return UIViewContainerView()
    }
    
    public func updateUIView(_ view: WebView.UIViewType, context: UIViewRepresentableContext<WebView>) {
        if view.contentView !== webView {
            view.contentView = webView
        }
    }
}
#endif

#if os(macOS)
// MARK: - NSViewRepresentable

extension WebView: NSViewRepresentable {
    
    public typealias NSViewType = NSViewContainerView<WKWebView>
    
    public func makeNSView(context: Context) -> WebView.NSViewType {
        return NSViewContainerView()
    }
    
    public func updateNSView(_ view: WebView.NSViewType, context: Context) {
        
        if view.contentView !== webView {
            view.contentView = webView
            if let webview = view.contentView {
                webview.uiDelegate = context.coordinator
                context.coordinator.registerNavigationHelper()
                
                self.webView
                    .configuration
                    .userContentController
                    .add(context.coordinator,
                         name: "readBlob")
                                
                let logHandler = """
                    function captureLog(msg) {
                        window.webkit.messageHandlers.logHandler.postMessage(msg);
                    }
                    window.console.log = captureLog;
                """
                let logHandlerScript = WKUserScript(source: logHandler,
                                          injectionTime: .atDocumentEnd,
                                          forMainFrameOnly: false)
                self.webView
                    .configuration
                    .userContentController
                    .addUserScript(logHandlerScript)
                
                // register the bridge script that listens for the output
                self.webView
                    .configuration
                    .userContentController
                    .add(context.coordinator,
                         name: "logHandler")
            }
        }
    }
}

#endif
