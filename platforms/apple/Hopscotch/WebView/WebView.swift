import WebKit
import SwiftUI
import Combine

public struct WebView: View {
    
    public let webView: WKWebView
    
    public class Coordinator: NSObject, WKUIDelegate {
        
        var parent: WebView

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
            }
        }
    }
}

#endif
