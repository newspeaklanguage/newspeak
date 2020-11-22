// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if defined(OS_FUCHSIA)

#include "virtual_memory.h"

#include <fcntl.h>
#include <lib/fdio/io.h>
#include <zircon/process.h>
#include <zircon/status.h>
#include <zircon/syscalls.h>

#include "assert.h"

namespace psoup {

VirtualMemory VirtualMemory::MapReadOnly(const char* filename) {
  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    FATAL1("Failed to open '%s'\n", filename);
  }
  zx_handle_t vmo = ZX_HANDLE_INVALID;
  zx_status_t status = fdio_get_vmo_clone(fd, &vmo);
  close(fd);
  if (status != ZX_OK) {
    FATAL1("fdio_get_vmo() failed: %s\n", zx_status_get_string(status));
  }
  size_t size;
  status = zx_vmo_get_size(vmo, &size);
  if (status != ZX_OK) {
    FATAL1("zx_vmo_get_size() failed: %s\n", zx_status_get_string(status));
  }
  zx_handle_t vmar = zx_vmar_root_self();
  uintptr_t addr;
  status = zx_vmar_map(vmar, ZX_VM_FLAG_PERM_READ, 0, vmo, 0, size, &addr);
  zx_handle_close(vmo);
  if (status != ZX_OK) {
    FATAL2("zx_vmar_map(%" Pd ") failed: %s\n", size,
           zx_status_get_string(status));
  }
  return VirtualMemory(reinterpret_cast<void*>(addr), size);
}


VirtualMemory VirtualMemory::Allocate(size_t size,
                                      Protection protection,
                                      const char* name) {
  uint32_t prot;
  switch (protection) {
    case kNoAccess:
      prot = 0;
      break;
    case kReadOnly:
      prot = ZX_VM_FLAG_PERM_READ;
      break;
    case kReadWrite:
      prot = ZX_VM_FLAG_PERM_READ | ZX_VM_FLAG_PERM_WRITE;
      break;
    default:
      UNREACHABLE();
      prot = 0;
  }

  zx_handle_t vmar = zx_vmar_root_self();
  zx_handle_t vmo = ZX_HANDLE_INVALID;
  zx_status_t status = zx_vmo_create(size, 0u, &vmo);
  if (status != ZX_OK) {
    FATAL2("zx_vmo_create(%" Pd ") failed: %s\n", size,
           zx_status_get_string(status));
  }

  ASSERT(name != NULL);
  zx_object_set_property(vmo, ZX_PROP_NAME, name, strlen(name));

  uintptr_t addr;
  status = zx_vmar_map(vmar, prot, 0, vmo, 0, size, &addr);
  zx_handle_close(vmo);
  if (status != ZX_OK) {
    FATAL2("zx_vmar_map(%" Pd ") failed: %s\n", size,
           zx_status_get_string(status));
  }

  return VirtualMemory(reinterpret_cast<void*>(addr), size);
}


void VirtualMemory::Free() {
  zx_handle_t vmar = zx_vmar_root_self();
  zx_status_t status = zx_vmar_unmap(vmar,
                                     reinterpret_cast<uintptr_t>(address_),
                                     size_);
  if (status != ZX_OK) {
    FATAL1("zx_vmar_unmap failed: %s\n", zx_status_get_string(status));
  }
}


bool VirtualMemory::Protect(Protection protection) {
  uint32_t prot;
  switch (protection) {
    case kNoAccess:
      prot = 0;
      break;
    case kReadOnly:
      prot = ZX_VM_FLAG_PERM_READ;
      break;
    case kReadWrite:
      prot = ZX_VM_FLAG_PERM_READ | ZX_VM_FLAG_PERM_WRITE;
      break;
    default:
      UNREACHABLE();
      prot = 0;
  }
  zx_handle_t vmar = zx_vmar_root_self();
  zx_status_t status = zx_vmar_protect(vmar, prot,
                                       reinterpret_cast<uintptr_t>(address_),
                                       size_);
  if (status != ZX_OK) {
    FATAL1("zx_vmar_protect failed: %s\n", zx_status_get_string(status));
  }
  return true;
}

}  // namespace psoup

#endif  // defined(OS_FUCHSIA)
