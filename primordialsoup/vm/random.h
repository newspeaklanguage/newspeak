// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_RANDOM_H_
#define VM_RANDOM_H_

namespace psoup {

// xorshift128+
// Sebastiano Vigna. "Further scramblings of Marsaglia’s xorshift generators."
class Random {
 public:
  explicit Random(uint64_t seed) {
    state0_ = seed;
    state1_ = 0;
  }

  uint64_t NextUInt64() {
    uint64_t s1 = state0_;
    const uint64_t s0 = state1_;
    const uint64_t result = s0 + s1;
    state0_ = s0;
    s1 ^= s1 << 23;
    state1_ = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return result;
  }

 private:
  uint64_t state0_;
  uint64_t state1_;
};

}  // namespace psoup

#endif  // VM_RANDOM_H_
