import Combine
import SwiftUI
import WebKit

public struct WebView: View {
    
    public let webView: WKWebView
    
    public class Coordinator: NSObject,
                              WKScriptMessageHandler,
                              WKUIDelegate,
                              WKWebViewDownloadHelperDelegate {
        
        private var parent: WebView
        private var helper : WKWebviewDownloadHelper!
        
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
            openPanel.begin { (result) in
                if result == NSApplication.ModalResponse.OK {
                    if let url = openPanel.url {
                        completionHandler([url])
                    }
                } else if result == NSApplication.ModalResponse.cancel {
                    completionHandler(nil)
                }
            }
        }
        
        public func webView(_ webView: WKWebView,
                            decidePolicyFor navigationResponse: WKNavigationResponse,
                            decisionHandler: @escaping (WKNavigationResponsePolicy) -> Void) {
            decisionHandler(.allow)
        }
        
        public func userContentController(_ userContentController: WKUserContentController,
                                          didReceive message: WKScriptMessage) {            
        }
        
        public func fileDownloadedAtURL(url: URL) {
            //            DispatchQueue.main.async {
            //                let activityVC = UIActivityViewController(activityItems: [url], applicationActivities: nil)
            //                activityVC.popoverPresentationController?.sourceView = self.view
            //                activityVC.popoverPresentationController?.sourceRect = self.view.frame
            //                activityVC.popoverPresentationController?.barButtonItem = self.navigationItem.rightBarButtonItem
            //                self.present(activityVC, animated: true, completion: nil)
            //            }
        }
        
        public func registerDownloadHelper() {
            let mimeTypes = [MimeType(type: "ms-excel", fileExtension: "xls"),
                             MimeType(type: "pdf", fileExtension: "pdf")]
            helper = WKWebviewDownloadHelper(webView: parent.webView,
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
                context.coordinator.registerDownloadHelper()
                
                self.webView
                    .configuration
                    .userContentController
                    .add(context.coordinator, name: "readBlob")
            }
        }
    }
}

#endif

