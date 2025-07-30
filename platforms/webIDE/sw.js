// Service worker lifecycle - summary
// 
//    - From https://developer.mozilla.org/en-US/docs/Web/Progressive_web_apps/Tutorials/CycleTracker/Service_workers:
//      - Once the PWA is installed on the user's machine, THE ONLY WAY to inform
//        the browser that there are updated files to be retrieved is to change
//        the service worker (this file, sw.js) on the server.
// 
//    - Corollary: The only way for a PWA website to force an update of the service worker
//        is to make a bit-change on the server's service worker (the sw.js).
// 
//        Such enforced update of the service worker, causes the browser to call
//        one-time 'install' and 'activate' on the service worker, which the service worker
//        can use to delete old caches and cache the new assets.
//
// Service worker lifecycle - processing in Newspeak
//
//   - The modified service worker sw.js is partly based on the link in the summary section above.
//   - The Newspeak web page index.html's calls navigator.register on this script,
//     the sw.js (the service worker).
//   - During the above registration, this sw.js file is compared to the server version.
//   - ONLY if the server sw.js changes:
//       the PWA starts to install the new server version sw.js to the local PWA;
//       this local install is done by triggering listeners registered
//       on the 'install' and 'activate' events on the
//       local running sw.js. We use the 'activate' event to update the local PWA caches.
//     else:
//       only further lifecycle events such as 'fetch' are trigerred on the sw.js.
//
// Sources:
//
//   - https://developer.mozilla.org/en-US/docs/Web/Progressive_web_apps/Tutorials/CycleTracker/Service_workers
//   - https://web.dev/articles/service-worker-lifecycle
//   - https://stackoverflow.com/questions/49739438/when-and-how-does-a-pwa-update-itself
// 
// Goals:
//
//  - During the PWA update of the Newspeak webIDE, we generally want to update
//    the cached resources.
//  - Also (I assume) we want to keep the cache-first strategy of looking up
//    resources, currently implemented in the 'fetch' event.
//    I assume cache-first is used for simplicity and savind the server resources.
//
// Goals implementation:
//
//  - Any time we want to force the PWA to update caches, we change some bits
//    on the server's sw.js.
//  - The changed bits happen to be a 'version number',
//    which we also use to version the cache, and to delete the old cache versions.
//  - The bits change will cause the PWA to 'install' and 'activate' the new sw.js,
//    by triggering the 'install' and 'activate' events on the listeners which the sw.js registered.
//    The 'install' event is triggered only once ever, when the server's sw.js is changed.
//  - After 'install', the 'activate' event is triggered.
//  - We use the 'version' number to version caches, and we use the 'activate'
//    event listener to delete old caches.

//
// The version of the cache in the 'caches' global variable.
// 
// The version should be updated (increased) every time the server wants to force
// the client PWAs to update. Any change in the service worker
// causes the browser to activate the new service worker, which in turn,
// updates the caches, by using a new name for the cache, and deleting
// the old cache in the 'activate' event listener (code also added in this commit).
// 
// The version update can be done either manually (we rely on this),
// or by applying some framework that generates this sw.js worker script.

const pwaVersion = 689;

// Cache name used by the 'caches' global variable.
// The pwaCacheName now includes the pwaVersion;
// old pwaVersion of cache is deleted in the 'activate' event listener.

const pwaCacheName = 'newspeak-ide-cache-version-' + pwaVersion;

// Resources cached initially

const pwaAppResources = [
    '/',
    // '/index.html', // consider adding, but '/' fetches index.html as well
    
    '/webIDE/public/assets/lib/primordialsoup-setup.js',
    '/webIDE/public/assets/lib/primordialsoup.js',
    '/webIDE/public/assets/lib/codemirror.js',
    '/webIDE/public/assets/lib/codemirror_autorefresh.js',
    '/webIDE/public/assets/lib/jszip.min.js',
    
    '/webIDE/public/assets/lib/codemirror.css',
    '/webIDE/public/assets/lib/primordialsoup.wasm',
    '/webIDE/public/assets/lib/HopscotchWebIDE.vfuel',

    // Top level images
    // The vfuel images aliens generate requests from top level - not right, but currently so.
    // Luckily, requests for images on top level are not outside of service worker scope,
    // as the scope looks at the source of the request - which is below /webIDE/, so in scope.
    
    '/accept16px.png',
    '/ampleforthDocument.png',
    '/cancel16px.png',
    '/classPresenterImage.png',
    '/classUnknownImage.png',
    '/clearImage.png',
    '/disclosureClosedImage.png',
    '/disclosureOpenImage.png',
    '/downloadImage.png',
    '/findImage.png',
    '/helpImage.png',
    '/hsAddImage.png',
    '/hsBackImage.png',
    '/hsCollapseImage.png',
    '/hsDropdownImage.png',
    '/hsExpandImage.png',
    '/hsForwardImage.png',
    '/hsHistoryImage.png',
    '/hsHomeImage.png',
    '/hsNewImage.png',
    '/hsRefreshImage.png',
    '/itemReferencesImage.png',
    '/languageNewspeak3.png',
    '/peekingeye1610.png',
    '/privateImage.png',
    '/protectedImage.png',
    '/publicImage.png',
    '/saveImage.png',
];

// Add all resources to cache.
// Intended to be called in 'initialize' for pwaAppResources.

const addAllResourcesToCache = async (resources, cacheName) => {
    const cache = await caches.open(cacheName);
    // Cache.addAll() takes an array of URLs, makes a request and fetches
    // the response for each, then adds each request/response to the cache.
    await cache.addAll(resources);
};

// Cache the request / response in cache named cacheName.
// The response must be cloned from fetch, cacheName should be pwaCacheName.
// Intended to be called in 'fetch' for assets fetched from network
//   (when request.url is not in pwaAppResources)

const putInCache = async (request, response, cacheName) => {
    const cache = await caches.open(cacheName);
    await cache.put(request, response);
};

// Find match for the passed request in the passed cacheName, obtaining response.
// If no such request is cached, returns undefined.
// Intended to be called in 'fetch' to get response of cached request/response.

const getMatchingCachedResponseFor = async (request, cacheName) => {
    const cache = await caches.open(cacheName);
    const cachedResponse = await cache.match(request.url);
    return cachedResponse;
};

// Fetch the url in the passed request, looking into cache first.
// If the request url is not in cache, go to network, and cache the result

// Fetch the url in the passed request using cache-first strategy:
//   Cache-match the cached response with the request url and return it if exists.
//   If no matching cached response exists, go to network,
//     cache the response, and return it.
//   Catch exception of both cache and network failure,
//     return 408 response or fetchErrorUrl.

const fetchCacheFirst = async({ request, cacheName, fetchErrorUrl }) => {
    
    const cachedResponse = await getMatchingCachedResponseFor(request, cacheName);
    
    // If response exists in cache, return it.
    if (cachedResponse !== undefined) {
        return cachedResponse;
    }
            
    // To support requesting resources not cached during 'install',
    // go to network, cache and return the network response.
    
    try {
        const url = request.url;                
        console.log(`[ServiceWorker:fetch:fetchCacheFirst] caching resource from net: ${url}`);
        
        const networkResponse = await fetch(request);
        
        // Response may be used only once, unless cloned.
        // So put networkResponse clone to cache for future multi-use,
        // and return the networkResponse for current use.
        putInCache(request, networkResponse.clone(), cacheName);
        
        return networkResponse;
        
    } catch (error) {
        const errorText = `Error fetching url=${url} from site.`;
        console.error(errorText);
        // could get error image from cache: return caches.match(fetchErrorUrl);
        return new Response(errorText, {
            status: 408,
            headers: { 'Content-Type': 'text/plain' },
        });
    }
};

// Add listener to service worker for service worker receiving the 'install' event.
// This event is emitted (and the listener called) when a new service worker
// is being installed.
// The event.waitUntil waits and keeps the new service worker
// in the 'installing' phase until the tasks here complete - that is,
// the install waits until all pwaAppResources are added to cache.

self.addEventListener('install', (event) => {
    console.log('[ServiceWorker:install:start]');
    // Skip waiting causes 'activate' (does old cache delete) to be called immediately after 'install'.
    // See https://web.dev/articles/service-worker-lifecycle#skip_the_waiting_phase
    self.skipWaiting();

    // wait until the callback is done (addAllResourcesToCache)
    event.waitUntil(
        (async () => {
            console.log('[ServiceWorker:install:event.waitUntil->callback:start] Caching all static resources.');
            // Async add all pwaAppResources to pwaCache
            addAllResourcesToCache(pwaAppResources, pwaCacheName);
            console.log('[ServiceWorker:install:event.waitUntil->callback:end] Caching all static resources.');
        })()
    );
});

// Add listener to service worker for service worker receiving the 'activate' event.
// The listener deletes old caches..
//
// Note: After update, on first start of the PWA, if we did NOT call skipWaiting,
//       we would see both old and new cache in debuggers.
//       However, the PWA would still correctly use the old cache in 'fetch'es!
//       See https://web.dev/articles/service-worker-lifecycle:
//

self.addEventListener('activate', (event) => {
    console.log('[ServiceWorker:activate:start]');
    event.waitUntil(
        (async () => {
            console.log('[ServiceWorker:activate:event.waitUntil->callback] Deleting old caches.');
            const names = await caches.keys();
            // Promise.all() takes list of promises and returns a single Promise
            // which 'then' method resolves all promises in list before resolving self.
            await Promise.all(
                // All caches that belong to this service worker,
                // except the current (pwaVersion) cache, delete.
                names.map((name) => {
                    if (name !== pwaCacheName) {
                        return caches.delete(name);
                    } else {
                        return false;
                    }
                }),
            );
            // Set itself (pw.js) as controller of the "client" = running PWA instance.
            // This way, clients loaded in same scope do not need reload (todo probably not needed)
            await clients.claim();
        })(),
    );
});

// Add listener to service worker for service worker receiving the 'fetch' event.
// The FetchEvent is emitted by the browser to this service worker
// when it intercepts all fetches, and gives this service worker a chance
// to handle each fetch request in this listener.
//
// This listener registers a callback named 'fetchCacheFirst' with the event
// by calling event.respondWith(fetchCacheFirst).
// The callback returns a response for the request wrapped in event.request
// looking first in cache, then to the network.

self.addEventListener('fetch', (event) => {
    
    console.log('[ServiceWorker:fetch:start] url=' + event.request.url);

    // Only capture and cache http/https requests
    if (!event.request.url.match('^(http|https)://')) {
        console.log(`[ServiceWorker:fetch:match http] by design, refusing to cache URL with scheme ${event.request.url}.`);
        return;
    }

    /* 
    if (event.request.mode === 'navigate') {
        // Newspeak single page app, when navigating (fetching HTML page)
        // should return directly to the (cached) index.html page
        event.respondWith(caches.match('/'));
        return;
    }
    */

    // For all other requests, look for response to cache first,
    // then to network, and return the response.
    event.respondWith(
        fetchCacheFirst({
            request: event.request,
            cacheName: pwaCacheName,
            fetchErrorUrl: '/peekingeye1610.png',
        })
    );
});
