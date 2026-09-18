const name = getURIParam("sessionId");
// JSForCroquet>>sessionId keys the per-session storage off localStorage['name'];
// persist the session name there. (The psoup page never sets it - a latent gap
// that collapses every session's storage onto one key.)
if (name !== null) localStorage.setItem("name", name);
const apiKey = getURIParam("apiKey");// value ignored with reflector=, but must be present
const appId = getURIParam("appId");
const password = getURIParam("pwd");

// classes aren't stored in the global object, so assign them to
// variables so we can easily get them from Newspeak
var NSCroquetModel = NewspeakCroquetModel;
var NSCroquetView = NewspeakCroquetView;

/* The startup gate. Newspeak boot (HopscotchShell>>setupCroquetView) reads the
   JS global theView, but Session.join is asynchronous. The generated program
   (nsProgramSrc, defined by an inline script on the deploy page) boots
   synchronously at script-load time, so it is loaded from here, only once the
   session exists. The psoup build gates the same way with an Emscripten run
   dependency (meta/croquet-pre.js). */
/* autoSleep: false -- by default the Croquet client disconnects a tab some
   seconds after it is hidden ("going dormant"). With --storage=none the
   reflector DELETES an island ~10s after its last client disconnects, so all
   tabs hidden at once silently erased the whole session history (waking
   clients rejoin a FRESH session under the same id; later joiners get a
   mid-stream history that can never be reconstructed). A persistent session
   must hold its connection while the tab exists. */
Croquet.Session.join({ apiKey, appId, name, password, autoSleep: false, model: NewspeakCroquetModel, view: NewspeakCroquetView })
    .then(function (session) {
	var tag = document.createElement('script');
	tag.type = 'text/javascript';
	tag.src = nsProgramSrc;
	document.body.appendChild(tag);
    }, function (err) {
	console.error('Croquet Session.join failed; Newspeak was not started:', err);
    });
