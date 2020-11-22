// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_MATH_H_
#define VM_MATH_H_

#include "globals.h"
#include "assert.h"
#include "flags.h"

namespace psoup {

class Math {
 public:
  static inline bool AddHasOverflow64(int64_t left,
                                      int64_t right,
                                      int64_t* result) {
    if (TEST_SLOW_PATH) return true;

#if defined(__GNUC__)
#if __GNUC__ >= 5
#define HAS_BUILTIN_ADD_OVERFLOW
#endif
#endif

#if defined(__has_builtin)
#if __has_builtin(__builtin_add_overflow)
#define HAS_BUILTIN_ADD_OVERFLOW
#endif
#endif

#if defined(HAS_BUILTIN_ADD_OVERFLOW)
    return __builtin_add_overflow(left, right, result);
#else
    if (((right > 0) && (left > (INT64_MAX - right))) ||
        ((right < 0) && (left < (INT64_MIN - right)))) {
      return true;
    }
    *result = left + right;
    return false;
#endif
  }

  static inline bool SubtractHasOverflow64(int64_t left,
                                           int64_t right,
                                           int64_t* result) {
    if (TEST_SLOW_PATH) return true;

#if defined(__GNUC__)
#if __GNUC__ >= 5
#define HAS_BUILTIN_SUB_OVERFLOW
#endif
#endif

#if defined(__has_builtin)
#if __has_builtin(__builtin_sub_overflow)
#define HAS_BUILTIN_SUB_OVERFLOW
#endif
#endif

#if defined(HAS_BUILTIN_SUB_OVERFLOW)
    return __builtin_sub_overflow(left, right, result);
#else
    if (((right > 0) && (left < (INT64_MIN + right))) ||
        ((right < 0) && (left > (INT64_MAX + right)))) {
      return true;
    }
    *result = left - right;
    return false;
#endif
  }

  static inline bool MultiplyHasOverflow(intptr_t left,
                                         intptr_t right,
                                         intptr_t* result) {
    if (TEST_SLOW_PATH) return true;

#if defined(__GNUC__)
#if __GNUC__ >= 5
#define HAS_BUILTIN_MUL_OVERFLOW
#endif
#endif

#if defined(__has_builtin)
#if __has_builtin(__builtin_mul_overflow)
#define HAS_BUILTIN_MUL_OVERFLOW
#endif
#endif

#if defined(HAS_BUILTIN_MUL_OVERFLOW)
    return __builtin_mul_overflow(left, right, result);
#else
    const intptr_t kMaxBits = (sizeof(intptr_t) * 8) - 2;
    if ((Utils::HighestBit(left) + Utils::HighestBit(right)) < kMaxBits) {
      *result = left * right;
      return false;
    }
    return true;
#endif
  }

  static inline bool MultiplyHasOverflow64(int64_t left,
                                           int64_t right,
                                           int64_t* result) {
    if (TEST_SLOW_PATH) return true;

#if defined(__GNUC__)
#if __GNUC__ >= 5
#define HAS_BUILTIN_MUL_OVERFLOW
#endif
#endif

#if defined(__has_builtin)
#if __has_builtin(__builtin_mul_overflow)
#define HAS_BUILTIN_MUL_OVERFLOW
#endif
#endif

#if defined(HAS_BUILTIN_MUL_OVERFLOW)
    return __builtin_mul_overflow(left, right, result);
#else
    if ((Utils::HighestBit(left) + Utils::HighestBit(right)) < 62) {
      *result = left * right;
      return false;
    }
    return true;
#endif
  }

  // See DAAN LEIJEN. "Division and Modulus for Computer Scientists". 2001.

  static inline intptr_t TruncDiv(intptr_t dividend, intptr_t divisor) {
    ASSERT(divisor != 0);
    ASSERT((divisor != -1) || (dividend != INTPTR_MIN));
    return dividend / divisor;  // Undefined before C99.
  }

  static inline int64_t TruncDiv64(int64_t dividend, int64_t divisor) {
    ASSERT(divisor != 0);
    ASSERT((divisor != -1) || (dividend != INT64_MIN));
    return dividend / divisor;  // Undefined before C99.
  }

  static inline intptr_t TruncMod(intptr_t dividend, intptr_t divisor) {
    ASSERT(divisor != 0);
    ASSERT((divisor != -1) || (dividend != INTPTR_MIN));
    return dividend % divisor;  // Undefined before C99.
  }

  static inline int64_t TruncMod64(int64_t dividend, int64_t divisor) {
    ASSERT(divisor != 0);
    ASSERT((divisor != -1) || (dividend != INT64_MIN));
    return dividend % divisor;  // Undefined before C99.
  }

  static inline intptr_t FloorDiv(intptr_t dividend, intptr_t divisor) {
    ASSERT(divisor != 0);
    ASSERT(divisor != -1 || dividend != INTPTR_MIN);
    intptr_t truncating_quoitent = dividend / divisor;  // Undefined before C99.
    intptr_t truncating_remainder = dividend % divisor;
    if ((truncating_remainder != 0) &&
        ((dividend < 0) != (divisor < 0))) {
      return truncating_quoitent - 1;
    } else {
      return truncating_quoitent;
    }
  }

  static inline int64_t FloorDiv64(int64_t dividend, int64_t divisor) {
    ASSERT(divisor != 0);
    ASSERT(divisor != -1 || dividend != INT64_MIN);
    int64_t truncating_quoitent = dividend / divisor;  // Undefined before C99.
    int64_t truncating_remainder = dividend % divisor;
    if ((truncating_remainder != 0) &&
        ((dividend < 0) != (divisor < 0))) {
      return truncating_quoitent - 1;
    } else {
      return truncating_quoitent;
    }
  }

  static inline intptr_t FloorMod(intptr_t dividend, intptr_t divisor) {
    ASSERT(divisor != 0);
    ASSERT(divisor != -1 || dividend != INTPTR_MIN);
    intptr_t truncating_remainder = dividend % divisor;
    if ((truncating_remainder != 0) &&
        ((truncating_remainder < 0) != (divisor < 0))) {
      return truncating_remainder + divisor;
    } else {
      return truncating_remainder;
    }
  }

  static inline int64_t FloorMod64(int64_t dividend, int64_t divisor) {
    ASSERT(divisor != 0);
    if ((divisor == -1) && (dividend == INT64_MIN)) {
      return 0;
    }
    int64_t truncating_remainder = dividend % divisor;
    if ((truncating_remainder != 0) &&
        ((truncating_remainder < 0) != (divisor < 0))) {
      return truncating_remainder + divisor;
    } else {
      return truncating_remainder;
    }
  }

  static inline intptr_t ShiftLeft(intptr_t left, intptr_t right) {
    return static_cast<intptr_t>(static_cast<uintptr_t>(left) << right);
  }

  static inline int64_t ShiftLeft64(int64_t left, int64_t right) {
    return static_cast<int64_t>(static_cast<uint64_t>(left) << right);
  }

  //NO_SANITIZE_UNDEFINED("float-divide-by-zero")
  static inline double DivideF64(double dividend, double divisor) {
    return dividend / divisor;
  }
};

}  // namespace psoup

#endif  // VM_MATH_H_
