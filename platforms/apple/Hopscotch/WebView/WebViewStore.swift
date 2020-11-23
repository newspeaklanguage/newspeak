import WebKit
import Combine

public class WebViewStore: ObservableObject {
    
    private var observers = Set<NSKeyValueObservation>()
    //private var schemeHandler: SchemeHandler!
    
    @Published public var webView: WKWebView {
        didSet {
            setupObservers()
        }
    }

    public init() {
        
        let config = WKWebViewConfiguration()
        //self.schemeHandler = SchemeHandler(config)
        self.webView = WKWebView(frame: .zero, configuration: config)
                
        self.webView
          .configuration
          .preferences
          .setValue(true, forKey: "allowFileAccessFromFileURLs")
        
        self.webView
            .configuration
            .preferences
            .javaScriptEnabled = true

        #if DEBUG
        self.webView
          .configuration
          .preferences
          .setValue(true, forKey: "developerExtrasEnabled")
        #endif
                        
        setupObservers()
    }

    private func setupObservers() {
        
        func subscriber<Value>(for keyPath: KeyPath<WKWebView, Value>) -> NSKeyValueObservation {
            return webView.observe(keyPath, options: [.prior]) { _, change in
                if change.isPrior {
                    self.objectWillChange.send()
                }
            }
        }
        
        // Observers for all KVO compliant properties
        observers = [
            subscriber(for: \.title),
            subscriber(for: \.url),
            subscriber(for: \.isLoading),
            subscriber(for: \.estimatedProgress),
            subscriber(for: \.hasOnlySecureContent),
            subscriber(for: \.serverTrust),
            subscriber(for: \.canGoBack),
            subscriber(for: \.canGoForward)
        ]
    }

    deinit {
        observers.forEach {
            // Not even sure if this is required?
            // Probably wont be needed in future betas?
            $0.invalidate()
        }
    }
}

extension WebViewStore {
    
    func update(_ HTML: String, baseURL: URL) {
        webView.evaluateJavaScript("window.pageYOffset") { [weak self] object, error in
            self?.webView.loadHTMLString(HTML, baseURL: baseURL)

            if let offset = object as? Int {
                self?.scrollTo(offset)
            }
        }
    }

    private func scrollTo(_ YOffset: Int) {
        let script = "window.scrollTo(0, \(YOffset));"
        let scrollScript = WKUserScript(source: script, injectionTime: .atDocumentEnd, forMainFrameOnly: true)
        self.webView.configuration.userContentController.addUserScript(scrollScript)
    }
}

// MARK: - WKURLSchemeHandler

class SchemeHandler: NSObject, WKURLSchemeHandler {

    init(_ config: WKWebViewConfiguration) {
        super.init()

        config.setURLSchemeHandler(self, forURLScheme: "blob")
    }

    func webView(_ webView: WKWebView, start urlSchemeTask: WKURLSchemeTask) {
        print("Processing request for URL: \(urlSchemeTask.request.url?.absoluteString ?? "")")
//        guard let urlString = urlSchemeTask.request.url?.absoluteString else {
//            return
//        }
//
//        if urlString == Constant.articleURLString, let data = Constant.articleHTML.data(using: .utf8) {
//            let response = URLResponse(url: URL(string: "some")!, mimeType: "text/html", expectedContentLength: data.count, textEncodingName: "utf-8")
//            urlSchemeTask.didReceive(response)
//            urlSchemeTask.didReceive(data)
//            urlSchemeTask.didFinish()
//        } else if urlString == Constant.scriptURLString, let data = Constant.script.data(using: .utf8) {
//            let response = URLResponse(url: URL(string: "some")!, mimeType: "application/javascript", expectedContentLength: data.count, textEncodingName: "utf-8")
//            urlSchemeTask.didReceive(response)
//            urlSchemeTask.didReceive(data)
//            urlSchemeTask.didFinish()
//        }

    }

    func webView(_ webView: WKWebView, stop urlSchemeTask: WKURLSchemeTask) {
        print("Stopping request for URL: \(urlSchemeTask.request.url?.absoluteString ?? ""))")
    }

}
