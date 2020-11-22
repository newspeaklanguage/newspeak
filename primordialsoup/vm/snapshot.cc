// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "snapshot.h"

#include "heap.h"
#include "interpreter.h"
#include "object.h"
#include "os.h"

namespace psoup {

class Cluster {
 public:
  Cluster() : ref_start_(0), ref_stop_(0) {}

  virtual ~Cluster() {}

  virtual void ReadNodes(Deserializer* d, Heap* h) = 0;
  virtual void ReadEdges(Deserializer* d, Heap* h) = 0;

 protected:
  intptr_t ref_start_;
  intptr_t ref_stop_;
};

class RegularObjectCluster : public Cluster {
 public:
  explicit RegularObjectCluster(intptr_t format) : format_(format), cid_(0) {}
  ~RegularObjectCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    cid_ = h->AllocateClassId();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      Object object = h->AllocateRegularObject(cid_, format_, Heap::kSnapshot);
      d->RegisterRef(object);
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {
    Object cls = d->ReadRef();
    h->RegisterClass(cid_, static_cast<Behavior>(cls));

    for (intptr_t i = ref_start_; i < ref_stop_; i++) {
      RegularObject object = static_cast<RegularObject>(d->Ref(i));
      for (intptr_t j = 0; j < format_; j++) {
        object->set_slot(j, d->ReadRef(), kNoBarrier);
      }
    }
  }

 private:
  intptr_t format_;
  intptr_t cid_;
};

class ByteArrayCluster : public Cluster {
 public:
  ByteArrayCluster() {}
  ~ByteArrayCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      intptr_t size = d->ReadUnsigned();
      ByteArray object = h->AllocateByteArray(size, Heap::kSnapshot);
      for (intptr_t j = 0; j < size; j++) {
        object->set_element(j, d->ReadUint8());
      }
      d->RegisterRef(object);
      ASSERT(object->IsByteArray());
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {}
};

class StringCluster : public Cluster {
 public:
  StringCluster() {}
  ~StringCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    ReadNodes(d, h, false);
    ReadNodes(d, h, true);
  }

  void ReadNodes(Deserializer* d, Heap* h, bool is_canonical) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      intptr_t size = d->ReadUnsigned();
      String object = h->AllocateString(size, Heap::kSnapshot);
      ASSERT(!object->is_canonical());
      object->set_is_canonical(is_canonical);
      for (intptr_t j = 0; j < size; j++) {
        object->set_element(j, d->ReadUint8());
      }
      d->RegisterRef(object);
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {}
};

class ArrayCluster : public Cluster {
 public:
  ArrayCluster() {}
  ~ArrayCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      intptr_t size = d->ReadUnsigned();
      Array object = h->AllocateArray(size, Heap::kSnapshot);
      d->RegisterRef(object);
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {
    for (intptr_t i = ref_start_; i < ref_stop_; i++) {
      Array object = Array::Cast(d->Ref(i));
      intptr_t size = object->Size();
      for (intptr_t j = 0; j < size; j++) {
        object->set_element(j, d->ReadRef(), kNoBarrier);
      }
    }
  }
};

class WeakArrayCluster : public Cluster {
 public:
  WeakArrayCluster() {}
  ~WeakArrayCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      intptr_t size = d->ReadUnsigned();
      WeakArray object = h->AllocateWeakArray(size, Heap::kSnapshot);
      d->RegisterRef(object);
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {
    for (intptr_t i = ref_start_; i < ref_stop_; i++) {
      WeakArray object = WeakArray::Cast(d->Ref(i));
      intptr_t size = object->Size();
      for (intptr_t j = 0; j < size; j++) {
        object->set_element(j, d->ReadRef(), kNoBarrier);
      }
    }
  }
};

class ClosureCluster : public Cluster {
 public:
  ClosureCluster() {}
  ~ClosureCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      intptr_t size = d->ReadUint16();
      Closure object = h->AllocateClosure(size, Heap::kSnapshot);
      d->RegisterRef(object);
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {
    for (intptr_t i = ref_start_; i < ref_stop_; i++) {
      Closure object = Closure::Cast(d->Ref(i));

      object->set_defining_activation(Activation::Cast(d->ReadRef()),
                                      kNoBarrier);
      object->set_initial_bci(static_cast<SmallInteger>(d->ReadRef()));
      object->set_num_args(static_cast<SmallInteger>(d->ReadRef()));

      intptr_t size = object->NumCopied();
      for (intptr_t j = 0; j < size; j++) {
        object->set_copied(j, d->ReadRef(), kNoBarrier);
      }
    }
  }
};


class ActivationCluster : public Cluster {
 public:
  ActivationCluster() {}
  ~ActivationCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      Activation object = h->AllocateActivation(Heap::kSnapshot);
      d->RegisterRef(object);
    }
    ASSERT(d->next_ref() == ref_stop_);
  }

  void ReadEdges(Deserializer* d, Heap* h) {
    for (intptr_t i = ref_start_; i < ref_stop_; i++) {
      Activation object = Activation::Cast(d->Ref(i));

      object->set_sender(Activation::Cast(d->ReadRef()), kNoBarrier);
      object->set_bci(static_cast<SmallInteger>(d->ReadRef()));
      object->set_method(Method::Cast(d->ReadRef()), kNoBarrier);
      object->set_closure(Closure::Cast(d->ReadRef()), kNoBarrier);
      object->set_receiver(d->ReadRef(), kNoBarrier);

      intptr_t size = d->ReadUint16();
      ASSERT(size < kMaxTemps);
      object->set_stack_depth(SmallInteger::New(size));

      for (intptr_t j = 0; j < size; j++) {
        object->set_temp(j, d->ReadRef(), kNoBarrier);
      }
      for (intptr_t j = size; j < kMaxTemps; j++) {
        object->set_temp(j, SmallInteger::New(0), kNoBarrier);
      }
    }
  }
};

class SmallIntegerCluster : public Cluster {
 public:
  SmallIntegerCluster() {}
  ~SmallIntegerCluster() {}

  void ReadNodes(Deserializer* d, Heap* h) {
    intptr_t num_objects = d->ReadUnsigned();
    ref_start_ = d->next_ref();
    ref_stop_ = ref_start_ + num_objects;
    for (intptr_t i = 0; i < num_objects; i++) {
      int64_t value = d->ReadInt64();
      if (SmallInteger::IsSmiValue(value)) {
        SmallInteger object = SmallInteger::New(value);
        ASSERT(object->IsSmallInteger());
        d->RegisterRef(object);
      } else {
        MediumInteger object = h->AllocateMediumInteger(Heap::kSnapshot);
        object->set_value(value);
        d->RegisterRef(object);
      }
    }
    ASSERT(d->next_ref() == ref_stop_);

    intptr_t num_large = d->ReadUnsigned();
    for (intptr_t i = 0; i < num_large; i++) {
      bool negative = d->ReadUint8();
      intptr_t bytes = d->ReadUint16();
      intptr_t digits = (bytes + (sizeof(digit_t) - 1)) / sizeof(digit_t);
      intptr_t full_digits = bytes / sizeof(digit_t);

      LargeInteger object = h->AllocateLargeInteger(digits, Heap::kSnapshot);
      object->set_negative(negative);
      object->set_size(digits);

      for (intptr_t j = 0; j < full_digits; j++) {
        digit_t digit = 0;
        for (intptr_t shift = 0;
             shift < static_cast<intptr_t>(kDigitBits);
             shift += 8) {
          digit = digit | (d->ReadUint8() << shift);
        }
        object->set_digit(j, digit);
      }

      if (full_digits != digits) {
        intptr_t leftover_bytes = bytes % sizeof(digit_t);
        ASSERT(leftover_bytes != 0);
        digit_t digit = 0;
        for (intptr_t shift = 0;
             shift < (leftover_bytes * 8);
             shift += 8) {
          digit = digit | (d->ReadUint8() << shift);
        }
        object->set_digit(digits - 1, digit);
      }

      d->RegisterRef(object);
    }
  }

  void ReadEdges(Deserializer* d, Heap* h) {}
};

Deserializer::Deserializer(Heap* heap, void* snapshot, size_t snapshot_length) :
  snapshot_(reinterpret_cast<const uint8_t*>(snapshot)),
  snapshot_length_(snapshot_length),
  cursor_(snapshot_),
  heap_(heap),
  clusters_(NULL),
  refs_(NULL),
  next_ref_(0) {
}


Deserializer::~Deserializer() {
  for (intptr_t i = 0; i < num_clusters_; i++) {
    delete clusters_[i];
  }

  delete[] clusters_;
  delete[] refs_;
}


void Deserializer::Deserialize() {
  int64_t start = OS::CurrentMonotonicNanos();

  // Skip interpreter directive, if any.
  if ((cursor_[0] == static_cast<uint8_t>('#')) &&
      (cursor_[1] == static_cast<uint8_t>('!'))) {
    cursor_ += 2;
    while (*cursor_++ != static_cast<uint8_t>('\n')) {}
  }

  uint16_t magic = ReadUint16();
  if (magic != 0x1984) {
    FATAL("Wrong magic value");
  }
  uint16_t version = ReadUint16();
  if (version != 0) {
    FATAL1("Wrong version (%d)", version);
  }

  num_clusters_ = ReadUint16();
  clusters_ = new Cluster*[num_clusters_];

  intptr_t num_nodes = ReadUint32();
  refs_ = new Object[num_nodes + 1];  // Refs are 1-origin.
  next_ref_ = 1;

  for (intptr_t i = 0; i < num_clusters_; i++) {
    Cluster* c = ReadCluster();
    clusters_[i] = c;
    c->ReadNodes(this, heap_);
  }
  ASSERT((next_ref_ - 1) == num_nodes);
  for (intptr_t i = 0; i < num_clusters_; i++) {
    clusters_[i]->ReadEdges(this, heap_);
  }

  ObjectStore os = static_cast<ObjectStore>(ReadRef());

  heap_->RegisterClass(kSmiCid, os->SmallInteger());
  heap_->RegisterClass(kMintCid, os->MediumInteger());
  heap_->RegisterClass(kBigintCid, os->LargeInteger());
  heap_->RegisterClass(kFloat64Cid, os->Float64());
  heap_->RegisterClass(kByteArrayCid, os->ByteArray());
  heap_->RegisterClass(kStringCid, os->String());
  heap_->RegisterClass(kArrayCid, os->Array());
  heap_->RegisterClass(kWeakArrayCid, os->WeakArray());
  heap_->RegisterClass(kEphemeronCid, os->Ephemeron());
  heap_->RegisterClass(kActivationCid, os->Activation());
  heap_->RegisterClass(kClosureCid, os->Closure());

  heap_->interpreter()->InitializeRoot(os);
  heap_->InitializeAfterSnapshot();

  int64_t stop = OS::CurrentMonotonicNanos();
  intptr_t time = stop - start;
  if (TRACE_GROWTH) {
    OS::PrintErr("Deserialized %" Pd "kB snapshot "
                 "into %" Pd "kB heap "
                 "with %" Pd " objects "
                 "in %" Pd " us\n",
                 snapshot_length_ / KB,
                 heap_->Size() / KB,
                 next_ref_ - 1,
                 time / kNanosecondsPerMicrosecond);
  }

#if defined(DEBUG)
  size_t before = heap_->Size();
  heap_->CollectAll(Heap::kSnapshotTest);
  size_t after = heap_->Size();
  ASSERT(before == after);  // Snapshots should not contain garbage.
#endif
}


uint8_t Deserializer::ReadUint8() {
  return *cursor_++;
}


uint16_t Deserializer::ReadUint16() {
  int16_t result = ReadUint8();
  result = (result << 8) | ReadUint8();
  return result;
}


uint32_t Deserializer::ReadUint32() {
  uint32_t result = ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  return result;
}


int32_t Deserializer::ReadInt32() {
  uint32_t result = ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  return static_cast<int32_t>(result);
}


int64_t Deserializer::ReadInt64() {
  uint64_t result = ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  result = (result << 8) | ReadUint8();
  return static_cast<int64_t>(result);
}

static const int8_t kDataBitsPerByte = 7;
static const int8_t kByteMask = (1 << kDataBitsPerByte) - 1;
static const int8_t kMaxUnsignedDataPerByte = kByteMask;
static const uint8_t kEndUnsignedByteMarker = (255 - kMaxUnsignedDataPerByte);

intptr_t Deserializer::ReadUnsigned() {
  const uint8_t* c = cursor_;
  // ASSERT(c < end_);
  uint8_t b = *c++;
  if (b > kMaxUnsignedDataPerByte) {
    cursor_ = c;
    return static_cast<uint32_t>(b) - kEndUnsignedByteMarker;
  }

  int32_t r = 0;
  r |= static_cast<uint32_t>(b);
  // ASSERT(c < end_);
  b = *c++;
  if (b > kMaxUnsignedDataPerByte) {
    cursor_ = c;
    return r | ((static_cast<uint32_t>(b) - kEndUnsignedByteMarker) << 7);
  }

  r |= static_cast<uint32_t>(b) << 7;
  // ASSERT(c < end_);
  b = *c++;
  if (b > kMaxUnsignedDataPerByte) {
    cursor_ = c;
    return r | ((static_cast<uint32_t>(b) - kEndUnsignedByteMarker) << 14);
  }

  r |= static_cast<uint32_t>(b) << 14;
  // ASSERT(c < end_);
  b = *c++;
  if (b > kMaxUnsignedDataPerByte) {
    cursor_ = c;
    return r | ((static_cast<uint32_t>(b) - kEndUnsignedByteMarker) << 21);
  }

  r |= static_cast<uint32_t>(b) << 21;
  // ASSERT(c < end_);
  b = *c++;
  ASSERT(b > kMaxUnsignedDataPerByte);
  cursor_ = c;
  return r | ((static_cast<uint32_t>(b) - kEndUnsignedByteMarker) << 28);
}


Cluster* Deserializer::ReadCluster() {
  intptr_t format = ReadInt32();

  if (format >= 0) {
    return new RegularObjectCluster(format);
  } else {
    switch (-format) {
      case kByteArrayCid: return new ByteArrayCluster();
      case kStringCid: return new StringCluster();
      case kArrayCid: return new ArrayCluster();
      case kWeakArrayCid: return new WeakArrayCluster();
      case kClosureCid: return new ClosureCluster();
      case kActivationCid: return new ActivationCluster();
      case kSmiCid: return new SmallIntegerCluster();
    }
    FATAL1("Unknown cluster format %" Pd "\n", format);
    return NULL;
  }
}

}  // namespace psoup
