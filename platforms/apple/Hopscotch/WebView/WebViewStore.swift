import WebKit
import Combine

public class WebViewStore: ObservableObject {
    private var observers = Set<NSKeyValueObservation>()

    @Published public var webView: WKWebView {
        didSet {
            setupObservers()
        }
    }

    public init(webView: WKWebView = .init()) {
        self.webView = webView

        self.webView
          .configuration
          .preferences
          .setValue(true, forKey: "allowFileAccessFromFileURLs")
        
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
