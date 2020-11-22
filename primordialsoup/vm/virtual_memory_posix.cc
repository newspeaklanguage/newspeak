// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if defined(OS_ANDROID) || defined(OS_MACOS) || defined(OS_LINUX)

#include "virtual_memory.h"

#include <sys/mman.h>
#include <sys/stat.h>

#include "assert.h"
#include "os.h"

namespace psoup {

VirtualMemory VirtualMemory::MapReadOnly(const char* filename) {
  FILE* file = fopen(filename, "r");
  if (file == NULL) {
    FATAL1("Failed to open '%s'\n", filename);
  }
  struct stat st;
  if (fstat(fileno(file), &st) != 0) {
    FATAL1("Failed to stat '%s'\n", filename);
  }
  intptr_t size = st.st_size;
  void* address = mmap(0, size, PROT_READ,
                       MAP_FILE | MAP_PRIVATE,
                       fileno(file), 0);
  if (address == MAP_FAILED) {
    FATAL1("Failed to mmap '%s'\n", filename);
  }
  int result = fclose(file);
  ASSERT(result == 0);

  return VirtualMemory(address, size);
}


VirtualMemory VirtualMemory::Allocate(size_t size,
                                      Protection protection,
                                      const char* name) {
  int prot;
  switch (protection) {
    case kNoAccess: prot = PROT_NONE; break;
    case kReadOnly: prot = PROT_READ; break;
    case kReadWrite: prot = PROT_READ | PROT_WRITE; break;
    default:
     UNREACHABLE();
     prot = 0;
  }

  void* address = mmap(0, size, prot,
                       MAP_PRIVATE | MAP_ANON,
                       0, 0);
  if (address == MAP_FAILED) {
    FATAL1("Failed to mmap %" Pd " bytes\n", size);
  }

  return VirtualMemory(address, size);
}


void VirtualMemory::Free() {
  int result = munmap(address_, size_);
  if (result != 0) {
    FATAL1("Failed to munmap %" Pd " bytes\n", size_);
  }
}


bool VirtualMemory::Protect(Protection protection) {
#if defined(__aarch64__)
  // mprotect crashes my DragonBoard, so skip on ARM64.
  return true;
#else
  int prot;
  switch (protection) {
    case kNoAccess: prot = PROT_NONE; break;
    case kReadOnly: prot = PROT_READ; break;
    case kReadWrite: prot = PROT_READ | PROT_WRITE; break;
    default:
     UNREACHABLE();
     prot = 0;
  }

  int result = mprotect(address_, size_, prot);
  return result == 0;
#endif
}

}  // namespace psoup

#endif  // defined(OS_ANDROID) || defined(OS_MACOS) || defined(OS_LINUX)
