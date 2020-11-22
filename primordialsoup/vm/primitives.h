// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_PRIMITIVES_H_
#define VM_PRIMITIVES_H_

#include "assert.h"
#include "globals.h"

namespace psoup {

class Heap;
class Interpreter;

typedef bool (PrimitiveFunction)(intptr_t num_args,
                                 Heap* heap,
                                 Interpreter* interpreter);

class Primitives {
 public:
  static void Startup();
  static void Shutdown();

  static bool IsUnwindProtect(intptr_t prim) { return prim == 113; }
  static bool IsSimulationRoot(intptr_t prim) { return prim == 142; }

  static bool Invoke(intptr_t prim,
                     intptr_t num_args,
                     Heap* heap,
                     Interpreter* interpreter) {
    ASSERT(prim > 0);
    ASSERT(prim < kNumPrimitives);
    PrimitiveFunction* func = primitive_table_[prim];
    return func(num_args, heap, interpreter);
  }

 private:
  static const intptr_t kNumPrimitives = 256;

  static PrimitiveFunction** primitive_table_;
};

}  // namespace psoup

#endif  // VM_PRIMITIVES_H_
