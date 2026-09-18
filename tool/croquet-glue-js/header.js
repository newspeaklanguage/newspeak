/* Croquet integration for Newspeak deployed as Javascript (NS2JS).

   GENERATED - do not edit. This text is produced by tool/mirror-croquet-glue.py
   from primordialsoup/meta/croquet-post.js, which is canonical for both
   platforms, and spliced into DeploymentManager.ns
   (JSPackager>>croquetSupportScript). To change it, edit the canonical file, or
   the two JS-only pieces in tool/croquet-glue-js/, and run the script.

   Differences from the psoup copy, all of them marked there:
   - this header, and the declaration of croquetInitDone, which the psoup build
     gets from meta/croquet-pre.js;
   - no Emscripten run dependency: the startup gate is the Session.join promise
     at the bottom, which loads the generated program script (nsProgramSrc,
     defined inline by the deploy page) only once the session exists. The
     program's top-level boot then finds theView already set;
   - safeDownloadBlob / saveBlobWithSaveFilePicker are omitted: the generated
     program already defines the download helpers;
   - addSubscription (pre-detour vfuel compatibility) is omitted: no JS deploy
     predates the detour. */
var croquetInitDone = false;
