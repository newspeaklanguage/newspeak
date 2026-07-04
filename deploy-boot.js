// deploy-boot.js — shared boot for deployed Ampleforth documents.
//
// Each deployed page is lean:
//   <body data-ampleforth-doc="Name">
//     <div id="ampleforth-ssr"> ...crawlable static prose... </div>
//     <script src="deploy-boot.js"></script>
//
// This script: (1) reads the document name, (2) points the URL at
// AmpleforthViewer + <Name>.zip, (3) removes the static fallback once the live
// UI mounts, and (4) boots the runtime by REPLAYING the standard
// primordialsoup.html loader — fetched at runtime — so there is no second copy
// of the pinned boot boilerplate to drift out of sync.
(function () {
  var docName = document.body.getAttribute('data-ampleforth-doc') || '';
  var url = new URL(window.location), changed = false;
  if (!url.searchParams.get('snapshot')) { url.searchParams.set('snapshot', 'AmpleforthViewer.vfuel'); changed = true; }
  if (!url.searchParams.get('docName') && docName) { url.searchParams.set('docName', docName); changed = true; }
  if (changed) history.replaceState(null, '', url);

  var ssr = document.getElementById('ampleforth-ssr');
  if (ssr) {
    var obs = new MutationObserver(function (muts) {
      for (var i = 0; i < muts.length; i++) {
        var added = muts[i].addedNodes;
        for (var j = 0; j < added.length; j++) {
          var n = added[j];
          if (n.nodeType === 1 && n.id !== 'ampleforth-ssr' && n.tagName !== 'SCRIPT') {
            obs.disconnect();
            requestAnimationFrame(function () { if (ssr && ssr.parentNode) ssr.parentNode.removeChild(ssr); });
            return;
          }
        }
      }
    });
    obs.observe(document.body, { childList: true });
  }

  // Replay the standard loader's <script>/<link>/<style>. IMPORTANT: load
  // primordialsoup.js (the WASM runtime) LAST. It boots as soon as it loads and
  // immediately runs main: -> loadFromServerNamed: -> JSZip loadAsync:, so every
  // vendor lib it reaches for (jszip, isomorphic-git, ...) must already be present.
  // Replaying in document order raced the WASM boot against jszip.min.js (loaded
  // later in the chain), intermittently DNU-ing on an undefined JSZip. Deferring
  // primordialsoup.js to the end guarantees the libs are loaded before boot.
  fetch('primordialsoup.html').then(function (r) { return r.text(); }).then(function (html) {
    var loaded = new DOMParser().parseFromString(html, 'text/html');
    var nodes = Array.prototype.slice.call(loaded.querySelectorAll('script, link, style'));
    var boot = nodes.filter(function (n) { return n.tagName === 'SCRIPT' && (n.getAttribute('src') || '').indexOf('primordialsoup.js') !== -1; });
    nodes = nodes.filter(function (n) { return boot.indexOf(n) === -1; }).concat(boot);
    (function next(i) {
      if (i >= nodes.length) return;
      var src = nodes[i];
      if (src.tagName === 'SCRIPT') {
        var s = document.createElement('script');
        for (var a = 0; a < src.attributes.length; a++) s.setAttribute(src.attributes[a].name, src.attributes[a].value);
        s.async = false;
        if (src.getAttribute('src')) { s.onload = s.onerror = function () { next(i + 1); }; document.body.appendChild(s); }
        else { s.textContent = src.textContent; document.body.appendChild(s); next(i + 1); }
      } else { document.head.appendChild(src.cloneNode(true)); next(i + 1); }
    })(0);
  });
})();
