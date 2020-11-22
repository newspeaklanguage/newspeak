// Copyright (c) 2013, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_ALLOCATION_H_
#define VM_ALLOCATION_H_

#include "assert.h"
#include "globals.h"

namespace psoup {

// Stack allocated objects subclass from this base class. Objects of this type
// cannot be allocated on either the C or object heaps. Destructors for objects
// of this type will not be run unless the stack is unwound through normal
// program control flow.
class ValueObject {
 public:
  ValueObject() { }
  ~ValueObject() { }

 private:
  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(ValueObject);
};


// Static allocated classes only contain static members and can never
// be instantiated in the heap or on the stack.
class AllStatic {
 private:
  DISALLOW_ALLOCATION();
  DISALLOW_IMPLICIT_CONSTRUCTORS(AllStatic);
};


}  // namespace psoup

#endif  // VM_ALLOCATION_H_
