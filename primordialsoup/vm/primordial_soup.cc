// Copyright (c) 2017, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "primordial_soup.h"

#include "flags.h"
#include "globals.h"
#include "isolate.h"
#include "message_loop.h"
#include "os.h"
#include "port.h"
#include "primitives.h"
#include "snapshot.h"
#include "thread.h"

PSOUP_EXTERN_C void PrimordialSoup_Startup() {
  psoup::OS::Startup();
  psoup::Primitives::Startup();
  psoup::PortMap::Startup();
  psoup::Isolate::Startup();
}


PSOUP_EXTERN_C void PrimordialSoup_Shutdown() {
  psoup::Isolate::Shutdown();
  psoup::PortMap::Shutdown();
  psoup::Primitives::Shutdown();
  psoup::OS::Shutdown();
}


PSOUP_EXTERN_C intptr_t PrimordialSoup_RunIsolate(void* snapshot,
                                                  size_t snapshot_length,
                                                  int argc,
                                                  const char** argv) {
  uint64_t seed = psoup::OS::CurrentMonotonicNanos();
  psoup::Isolate* isolate = new psoup::Isolate(snapshot, snapshot_length, seed);
  isolate->loop()->PostMessage(new psoup::IsolateMessage(ILLEGAL_PORT,
                                                         argc, argv));
  intptr_t exit_code = isolate->loop()->Run();
  delete isolate;
  return exit_code;
}


PSOUP_EXTERN_C void PrimordialSoup_InterruptAll() {
  psoup::Isolate::InterruptAll();
}
