// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_VIRTUAL_MEMORY_H_
#define VM_VIRTUAL_MEMORY_H_

#include "globals.h"

namespace psoup {

class VirtualMemory {
 public:
  enum Protection {
    kNoAccess,
    kReadOnly,
    kReadWrite,
  };

  static VirtualMemory MapReadOnly(const char* filename);
  static VirtualMemory Allocate(size_t size,
                                Protection protection,
                                const char* name);
  void Free();
  bool Protect(Protection protection);

  uword base() const { return reinterpret_cast<uword>(address_); }
  uword limit() const { return base() + size(); }
  size_t size() const { return size_; }

  VirtualMemory() : address_(0), size_(0) { }

 private:
  VirtualMemory(void* address, size_t size)
      : address_(address), size_(size) { }

  void* address_;
  size_t size_;
};

}  // namespace psoup

#endif  // VM_VIRTUAL_MEMORY_H_
