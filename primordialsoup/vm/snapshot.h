// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_SNAPSHOT_H_
#define VM_SNAPSHOT_H_

#include "allocation.h"
#include "globals.h"
#include "object.h"

namespace psoup {

class Cluster;
class Heap;
class Object;

// Reads a variant of VictoryFuel.
class Deserializer : public ValueObject {
 public:
  Deserializer(Heap* heap, void* snapshot, size_t snapshot_length);
  ~Deserializer();

  intptr_t position() { return cursor_ - snapshot_; }
  uint8_t ReadUint8();
  uint16_t ReadUint16();
  uint32_t ReadUint32();
  int32_t ReadInt32();
  int64_t ReadInt64();
  intptr_t ReadUnsigned();

  void Deserialize();

  Cluster* ReadCluster();

  intptr_t next_ref() const { return next_ref_; }

  void RegisterRef(Object object) {
    refs_[next_ref_++] = object;
  }
  Object ReadRef() {
    return Ref(ReadUnsigned());
  }
  Object Ref(intptr_t i) {
    ASSERT(i > 0);
    ASSERT(i < next_ref_);
    return refs_[i];
  }

 private:
  const uint8_t* const snapshot_;
  const intptr_t snapshot_length_;
  const uint8_t* cursor_;

  Heap* const heap_;

  intptr_t num_clusters_;
  Cluster** clusters_;

  Object* refs_;
  intptr_t next_ref_;
};

}  // namespace psoup

#endif  // VM_SNAPSHOT_H_
