//
//  NSViewContainerView.swift
//  WebView
//
//  Created by Ben Chatelain on 5/5/20.
//

#if os(macOS)
import AppKit

public class NSViewContainerView<ContentView: NSView>: NSView {
    var contentView: ContentView? {
        willSet {
            contentView?.removeFromSuperview()
        }

        didSet {
            if let contentView = contentView {
                addSubview(contentView)
                contentView.translatesAutoresizingMaskIntoConstraints = false

                NSLayoutConstraint.activate([
                    contentView.leadingAnchor.constraint(equalTo: leadingAnchor),
                    contentView.trailingAnchor.constraint(equalTo: trailingAnchor),
                    contentView.topAnchor.constraint(equalTo: topAnchor),
                    contentView.bottomAnchor.constraint(equalTo: bottomAnchor)
                ])
            }
        }
    }
}
#endif
