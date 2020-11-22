// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if !defined(OS_EMSCRIPTEN)

#include <signal.h>

#include "os.h"
#include "primordial_soup.h"
#include "virtual_memory.h"

static void SIGINT_handler(int sig) {
  PrimordialSoup_InterruptAll();
}

int main(int argc, const char** argv) {
  if (argc < 2) {
    psoup::OS::PrintErr("Usage: %s <program.vfuel>\n", argv[0]);
    return -1;
  }

  psoup::VirtualMemory snapshot = psoup::VirtualMemory::MapReadOnly(argv[1]);
  PrimordialSoup_Startup();
  void (*defaultSIGINT)(int) = signal(SIGINT, SIGINT_handler);

  intptr_t exit_code =
      PrimordialSoup_RunIsolate(reinterpret_cast<void*>(snapshot.base()),
                                snapshot.size(), argc - 2, &argv[2]);

  signal(SIGINT, defaultSIGINT);
  PrimordialSoup_Shutdown();

  // TODO(rmacnak): File and anonymous mappings are freed differently on
  // Windows.
#if !defined(OS_WINDOWS)
  snapshot.Free();
#endif

  return exit_code;
}

#endif  // !defined(OS_EMSCRIPTEN)
