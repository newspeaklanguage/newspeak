// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_UTILS_H_
#define VM_UTILS_H_

#include "globals.h"
#include "assert.h"

namespace psoup {

class Utils {
 public:
  template<typename T>
  static inline T RoundDown(T x, intptr_t n) {
    ASSERT(IsPowerOfTwo(n));
    return (x & -n);
  }

  template<typename T>
  static inline T RoundUp(T x, intptr_t n) {
    return RoundDown(x + n - 1, n);
  }

  static inline int HighestBit(int64_t v) {
    uint64_t x = static_cast<uint64_t>((v > 0) ? v : -v);
#if defined(__GNUC__)
    ASSERT(sizeof(long long) == sizeof(int64_t));  // NOLINT
    if (v == 0) return 0;
    return 63 - __builtin_clzll(x);
#else
    uint64_t t;
    int r = 0;
    if ((t = x >> 32) != 0) { x = t; r += 32; }
    if ((t = x >> 16) != 0) { x = t; r += 16; }
    if ((t = x >> 8) != 0) { x = t; r += 8; }
    if ((t = x >> 4) != 0) { x = t; r += 4; }
    if ((t = x >> 2) != 0) { x = t; r += 2; }
    if (x > 1) r += 1;
    return r;
#endif
  }

  static int BitLength(int64_t value) {
    // Flip bits if negative (-1 becomes 0).
    value ^= value >> (8 * sizeof(value) - 1);
    return (value == 0) ? 0 : (Utils::HighestBit(value) + 1);
  }

  template<typename T>
  static inline bool IsPowerOfTwo(T x) {
    return ((x & (x - 1)) == 0) && (x != 0);
  }

  template<typename T>
  static inline bool IsAligned(T x, intptr_t n) {
    ASSERT(IsPowerOfTwo(n));
    return (x & (n - 1)) == 0;
  }

  static char* StrError(int err, char* buffer, size_t bufsize);
};

}  // namespace psoup

#if defined(OS_ANDROID)
#include "utils_android.h"
#elif defined(OS_EMSCRIPTEN)
#include "utils_emscripten.h"
#elif defined(OS_FUCHSIA)
#include "utils_fuchsia.h"
#elif defined(OS_LINUX)
#include "utils_linux.h"
#elif defined(OS_MACOS)
#include "utils_macos.h"
#elif defined(OS_WINDOWS)
#include "utils_win.h"
#else
#error Unknown OS.
#endif

#endif  // VM_UTILS_H_
