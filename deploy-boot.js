// deploy-boot.js — shared boot for deployed Ampleforth documents.
//
// Each deployed page is lean:
//   <body data-ampleforth-doc="Name">
//     <div id="ampleforth-ssr"> ...crawlable static prose... </div>
//     <script src="deploy-boot.js"></script>
//
// This script reads the document name, removes the static fallback once the
// live UI mounts, and boots the document viewer on one of two runtimes
// (EURASIA_WEB_PUBLISHING_DESIGN_2026-11-23.md, section 2.2):
//
// - psoup: points the URL at AmpleforthViewer.vfuel + <Name>.zip and replays
//   the standard primordialsoup.html loader, fetched at run time, so there is
//   no second copy of its pinned boot boilerplate.
// - Eurasia: loads the libraries, then runs viewer/base.eus on eurasia_web.wasm
//   through eurasia.mjs. The URL is left alone: the viewer reads the name from
//   data-ampleforth-doc, or from ?docName= on a page without one
//   (eurasia-viewer.html).
//
// The runtime is DEFAULT_RUNTIME, unless the page's body says otherwise
// (data-ampleforth-runtime="psoup" or "eurasia"), and the URL overrides both
// (?psoup or ?eurasia). On Eurasia, ?interpret runs without the compiler.
//
// Eurasia's files are fetched relative to this script, so a page in a
// subdirectory that loads ../deploy-boot.js finds the runtime beside it;
// psoup's, as before, relative to the page.
(function () {
  // psoup while Eurasia is offered beside it; 'eurasia' once the sites swap.
  var DEFAULT_RUNTIME = 'psoup';

  var script = document.currentScript;
  var base = new URL('.', script ? script.src : window.location.href);
  var here = new URL(window.location);
  var docName = document.body.getAttribute('data-ampleforth-doc') || '';
  var runtime = here.searchParams.has('eurasia') ? 'eurasia'
    : here.searchParams.has('psoup') ? 'psoup'
    : document.body.getAttribute('data-ampleforth-runtime') || DEFAULT_RUNTIME;

  var ssr = document.getElementById('ampleforth-ssr');
  if (ssr) {
    var obs = new MutationObserver(function (muts) {
      for (var i = 0; i < muts.length; i++) {
        var added = muts[i].addedNodes;
        for (var j = 0; j < added.length; j++) {
          var n = added[j];
          if (n.nodeType === 1 && n.id !== 'ampleforth-ssr' && n.tagName !== 'SCRIPT' && n.tagName !== 'LINK') {
            obs.disconnect();
            requestAnimationFrame(function () { if (ssr && ssr.parentNode) ssr.parentNode.removeChild(ssr); });
            return;
          }
        }
      }
    });
    obs.observe(document.body, { childList: true });
  }

  function at(path) { return new URL(path, base).href; }

  // Appends the scripts one after the other, each after the previous has
  // loaded, then calls done.
  function loadScripts(srcs, done) {
    (function next(i) {
      if (i >= srcs.length) { done(); return; }
      var s = document.createElement('script');
      s.src = at(srcs[i]);
      s.async = false;
      s.onload = function () { next(i + 1); };
      s.onerror = function () { fail('cannot load ' + srcs[i]); };
      document.body.appendChild(s);
    })(0);
  }

  function fail(message) {
    console.error('deploy-boot:', message);
    var p = document.createElement('p');
    p.textContent = 'The live document could not start: ' + message;
    document.body.appendChild(p);
  }

  // Eurasia. The libraries are the ones eurasia/web/libs holds; every one must
  // be loaded before the VM, which starts the viewer as soon as it runs.
  var EURASIA_LIBRARIES = [
    'vendor/buffer-6.0.3.bundle.min.js',
    'CodeMirror/lib/codemirror.js',
    'CodeMirror/addon/display/autorefresh.js',
    'jszip.min.js',
    'vendor/isomorphic-git-1.38.4.umd.min.js',
    'vendor/lightning-fs-4.6.2.min.js',
    'vendor/isomorphic-git-1.38.4-http-web.umd.js',
    'vendor/diff_match_patch-2019-07.js',
    'custom-post.js'
  ];

  function bootEurasia() {
    var css = document.createElement('link');
    css.rel = 'stylesheet';
    css.href = at('CodeMirror/lib/codemirror.css');
    document.head.appendChild(css);
    loadScripts(EURASIA_LIBRARIES, function () {
      window.Buffer = window.buffer.Buffer;
      function bytes(path) {
        return fetch(at(path)).then(function (r) {
          if (!r.ok) throw new Error('cannot fetch ' + path + ': ' + r.status);
          return r.arrayBuffer();
        }).then(function (b) { return new Uint8Array(b); });
      }
      var jit = here.searchParams.has('interpret') ? 0 : 1;
      Promise.all([import(at('eurasia.mjs')), bytes('eurasia_web.wasm'), bytes('viewer/base.eus')])
        .then(function (parts) {
          return parts[0].run(parts[1], parts[2], { print: function (line) { console.log(line); }, jit: jit });
        })
        .then(function (result) {
          if (result.status === 'exited') console.log('eurasia: exited ' + result.code);
        })
        .catch(function (e) { fail(e.message); });
    });
  }

  // psoup. Replay the standard loader's <script>/<link>/<style>. IMPORTANT:
  // load primordialsoup.js (the WASM runtime) LAST. It boots as soon as it
  // loads and immediately runs main: -> loadFromServerNamed: -> JSZip
  // loadAsync:, so every vendor lib it reaches for (jszip, isomorphic-git, ...)
  // must already be present. Replaying in document order raced the WASM boot
  // against jszip.min.js (loaded later in the chain), intermittently DNU-ing on
  // an undefined JSZip. Deferring primordialsoup.js to the end guarantees the
  // libs are loaded before boot.
  function bootPsoup() {
    var url = new URL(window.location), changed = false;
    if (!url.searchParams.get('snapshot')) { url.searchParams.set('snapshot', 'AmpleforthViewer.vfuel'); changed = true; }
    if (!url.searchParams.get('docName') && docName) { url.searchParams.set('docName', docName); changed = true; }
    if (changed) history.replaceState(null, '', url);
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
  }

  if (runtime === 'eurasia') bootEurasia(); else bootPsoup();
})();
