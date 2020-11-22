// Copyright (c) 2019, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if defined(OS_EMSCRIPTEN)

#include <emscripten.h>

#include "isolate.h"
#include "message_loop.h"
#include "os.h"
#include "port.h"
#include "primordial_soup.h"

EM_JS(void, _JS_initializeAliens, (), {
  var aliens = new Array();
  aliens.push(undefined);  // 0
  aliens.push(null);       // 1
  aliens.push(false);      // 2
  aliens.push(true);       // 3
  aliens.push(window);     // 4
  Module.aliens = aliens;
});

static psoup::Isolate* isolate;
extern "C" void load_snapshot(void* snapshot, size_t snapshot_length) {
  PrimordialSoup_Startup();
  _JS_initializeAliens();

  uint64_t seed = psoup::OS::CurrentMonotonicNanos();
  isolate = new psoup::Isolate(snapshot, snapshot_length, seed);
  int argc = 0;
  const char** argv = NULL;
  isolate->loop()->PostMessage(new psoup::IsolateMessage(ILLEGAL_PORT,
                                                         argc, argv));
}

extern "C" int handle_message() {
  return static_cast<psoup::EmscriptenMessageLoop*>(isolate->loop())
      ->HandleMessage();
}

extern "C" int handle_signal(int handle, int status, int signals, int count) {
  return static_cast<psoup::EmscriptenMessageLoop*>(isolate->loop())
      ->HandleSignal(handle, status, signals, count);
}

#endif  // defined(OS_EMSCRIPTEN)
