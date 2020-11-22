// Copyright (c) 2019, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if defined(OS_EMSCRIPTEN)

#include "virtual_memory.h"

#include "assert.h"
#include "os.h"

namespace psoup {

VirtualMemory VirtualMemory::MapReadOnly(const char* filename) {
  UNREACHABLE();
  return VirtualMemory(NULL, 0);
}


VirtualMemory VirtualMemory::Allocate(size_t size,
                                      Protection protection,
                                      const char* name) {
  void* address = malloc(size);
  if (address == NULL) {
    FATAL1("Failed to malloc %" Pd " bytes\n", size);
  }
  return VirtualMemory(address, size);
}


void VirtualMemory::Free() {
  free(address_);
}


bool VirtualMemory::Protect(Protection protection) {
  return true;
}

}  // namespace psoup

#endif  // defined(OS_EMSCRIPTEN)
