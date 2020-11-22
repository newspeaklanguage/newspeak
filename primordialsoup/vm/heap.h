// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_HEAP_H_
#define VM_HEAP_H_

#include "assert.h"
#include "flags.h"
#include "globals.h"
#include "object.h"
#include "utils.h"
#include "virtual_memory.h"

namespace psoup {

class Interpreter;
class Region;

// Note these values are never valid Object.
#if defined(ARCH_IS_32_BIT)
static const uword kUnallocatedWord = 0xabababab;
static const uword kUninitializedWord = 0xcbcbcbcb;
#elif defined(ARCH_IS_64_BIT)
static const uword kUnallocatedWord = 0xabababababababab;
static const uword kUninitializedWord = 0xcbcbcbcbcbcbcbcb;
#endif
static const uint8_t kUnallocatedByte = 0xab;
static const uint8_t kUninitializedByte = 0xcb;

static intptr_t AllocationSize(intptr_t size) {
  return Utils::RoundUp(size, kObjectAlignment);
}

class Semispace {
 private:
  friend class Heap;

  void Allocate(size_t size) {
    memory_ = VirtualMemory::Allocate(size,
                                      VirtualMemory::kReadWrite,
                                      "primordialsoup-heap");
    ASSERT(Utils::IsAligned(memory_.base(), kObjectAlignment));
    ASSERT(memory_.size() == size);
#if defined(DEBUG)
    MarkUnallocated();
#endif
  }

  void Free() { memory_.Free(); }

  size_t size() const { return memory_.size(); }
  uword base() const { return memory_.base(); }
  uword limit() const { return memory_.limit(); }
  uword object_start() const {
    return memory_.base() + kNewObjectAlignmentOffset;
  }

  void MarkUnallocated() const {
    memset(reinterpret_cast<void*>(base()), kUnallocatedByte, size());
  }

  void ReadWrite() { memory_.Protect(VirtualMemory::kReadWrite); }
  void NoAccess() { memory_.Protect(VirtualMemory::kNoAccess); }

  Semispace() : memory_() { }

  VirtualMemory memory_;
};

class FreeList {
 private:
  friend class Heap;

  FreeList() { Reset(); }

  uword TryAllocate(intptr_t size);

  intptr_t IndexForSize(intptr_t size) {
    intptr_t index = size >> kObjectAlignmentLog2;
    if (index > kSizeClasses) {
      return kSizeClasses;
    }
    return index;
  }

  void SplitAndRequeue(FreeListElement element, intptr_t size);
  FreeListElement Dequeue(intptr_t index);
  void Enqueue(FreeListElement element);
  void EnqueueRange(uword address, intptr_t size);
  void Reset() {
    for (intptr_t i = 0; i <= kSizeClasses; i++) {
      free_lists_[i] = nullptr;
    }
  }

  static const intptr_t kSizeClasses = 7;
  FreeListElement free_lists_[kSizeClasses + 1];
};

// C. J. Cheney. "A nonrecursive list compacting algorithm." Communications of
// the ACM. 1970.
//
// Barry Hayes. "Ephemerons: a New Finalization Mechanism." Object-Oriented
// Languages, Programming, Systems, and Applications. 1997.
class Heap {
 private:
  static const intptr_t kLargeAllocation = 32 * KB;
  static const size_t kInitialSemispaceCapacity = sizeof(uword) * MB / 8;
  static const size_t kMaxSemispaceCapacity = 2 * sizeof(uword) * MB;
  static const size_t kRegionSize = 256 * KB;

 public:
  enum Allocator { kNormal, kSnapshot };

  enum GrowthPolicy { kControlGrowth, kForceGrowth };

  enum Reason {
    kNewSpace,
    kTenure,
    kOldSpace,
    kClassTable,
    kPrimitive,
    kSnapshotTest
  };

  static const char* ReasonToCString(Reason reason) {
    switch (reason) {
      case kNewSpace: return "new-space";
      case kTenure: return "tenure";
      case kOldSpace: return "old-space";
      case kClassTable: return "class-table";
      case kPrimitive: return "primitive";
      case kSnapshotTest: return "snapshot-test";
    }
    UNREACHABLE();
    return nullptr;
  }

  Heap();
  ~Heap();

  void AddToRememberedSet(HeapObject object) {
    ASSERT(object->IsOldObject());
    ASSERT(!object->is_remembered());
    if (remembered_set_size_ == remembered_set_capacity_) {
      GrowRememberedSet();
    }
    remembered_set_[remembered_set_size_++] = object;
    object->set_is_remembered(true);
  }

  RegularObject AllocateRegularObject(intptr_t cid, intptr_t num_slots,
                                      Allocator allocator = kNormal) {
    ASSERT(cid == kEphemeronCid || cid >= kFirstRegularObjectCid);
    const intptr_t heap_size =
        AllocationSize(num_slots * sizeof(Object) + sizeof(HeapObject::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, cid, heap_size);
    RegularObject result = static_cast<RegularObject>(obj);
    ASSERT(result->IsRegularObject() || result->IsEphemeron());
    ASSERT(result->HeapSize() == heap_size);

    const intptr_t header_slots = sizeof(HeapObject::Layout) / sizeof(uword);
    if (((header_slots + num_slots) & 1) == 1) {
      // The leftover slot will be visited by the GC. Make it a valid oop.
      result->set_slot(num_slots, SmallInteger::New(0), kNoBarrier);
    }

    return result;
  }

  ByteArray AllocateByteArray(intptr_t num_bytes,
                              Allocator allocator = kNormal) {
    const intptr_t heap_size =
        AllocationSize(num_bytes * sizeof(uint8_t) + sizeof(ByteArray::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kByteArrayCid, heap_size);
    ByteArray result = static_cast<ByteArray>(obj);
    result->set_size(SmallInteger::New(num_bytes));
    ASSERT(result->IsByteArray());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  String AllocateString(intptr_t num_bytes, Allocator allocator = kNormal) {
    const intptr_t heap_size =
        AllocationSize(num_bytes * sizeof(uint8_t) + sizeof(String::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kStringCid, heap_size);
    String result = static_cast<String>(obj);
    result->set_size(SmallInteger::New(num_bytes));
    ASSERT(result->IsString());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  Array AllocateArray(intptr_t num_slots, Allocator allocator = kNormal) {
    const intptr_t heap_size =
        AllocationSize(num_slots * sizeof(Object) + sizeof(Array::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kArrayCid, heap_size);
    Array result = static_cast<Array>(obj);
    result->set_size(SmallInteger::New(num_slots));
    ASSERT(result->IsArray());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  WeakArray AllocateWeakArray(intptr_t num_slots,
                              Allocator allocator = kNormal) {
    const intptr_t heap_size =
        AllocationSize(num_slots * sizeof(Object) + sizeof(WeakArray::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kWeakArrayCid, heap_size);
    WeakArray result = static_cast<WeakArray>(obj);
    result->set_size(SmallInteger::New(num_slots));
    ASSERT(result->IsWeakArray());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  Closure AllocateClosure(intptr_t num_copied, Allocator allocator = kNormal) {
    const intptr_t heap_size =
        AllocationSize(num_copied * sizeof(Object) + sizeof(Closure::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kClosureCid, heap_size);
    Closure result = static_cast<Closure>(obj);
    result->set_num_copied(SmallInteger::New(num_copied));
    ASSERT(result->IsClosure());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  Activation AllocateActivation(Allocator allocator = kNormal) {
    const intptr_t heap_size = AllocationSize(sizeof(Activation::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kActivationCid, heap_size);
    Activation result = static_cast<Activation>(obj);
    ASSERT(result->IsActivation());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  MediumInteger AllocateMediumInteger(Allocator allocator = kNormal) {
    const intptr_t heap_size = AllocationSize(sizeof(MediumInteger::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kMintCid, heap_size);
    MediumInteger result = static_cast<MediumInteger>(obj);
    ASSERT(result->IsMediumInteger());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  LargeInteger AllocateLargeInteger(intptr_t capacity,
                                    Allocator allocator = kNormal) {
    const intptr_t heap_size = AllocationSize(capacity * sizeof(digit_t) +
                                              sizeof(LargeInteger::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kBigintCid, heap_size);
    LargeInteger result = static_cast<LargeInteger>(obj);
    result->set_capacity(capacity);
    ASSERT(result->IsLargeInteger());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  Float64 AllocateFloat64(Allocator allocator = kNormal) {
    const intptr_t heap_size = AllocationSize(sizeof(Float64::Layout));
    uword addr = Allocate(heap_size, allocator);
    HeapObject obj = HeapObject::Initialize(addr, kFloat64Cid, heap_size);
    Float64 result = static_cast<Float64>(obj);
    ASSERT(result->IsFloat64());
    ASSERT(result->HeapSize() == heap_size);
    return result;
  }

  Message AllocateMessage();

  size_t Size() const {
    size_t new_size = top_ - to_.object_start();
    return new_size + old_size_;
  }

  void CollectAll(Reason reason) { MarkSweep(reason); }

  intptr_t CountInstances(intptr_t cid);
  intptr_t CollectInstances(intptr_t cid, Array array);

  bool BecomeForward(Array old, Array neu);

  intptr_t AllocateClassId();
  void RegisterClass(intptr_t cid, Behavior cls) {
    ASSERT(class_table_[cid] == static_cast<Object>(kUninitializedWord));
    class_table_[cid] = cls;
    cls->set_id(SmallInteger::New(cid));
    cls->AssertCouldBeBehavior();
    ASSERT(cls->cid() >= kFirstRegularObjectCid);
  }
  Behavior ClassAt(intptr_t cid) const {
    ASSERT(cid > kIllegalCid);
    ASSERT(cid < class_table_size_);
    return static_cast<Behavior>(class_table_[cid]);
  }

  void InitializeInterpreter(Interpreter* interpreter) {
    ASSERT(interpreter_ == nullptr);
    interpreter_ = interpreter;
  }
  void InitializeAfterSnapshot();

  Interpreter* interpreter() const { return interpreter_; }

  intptr_t handles() const { return handles_size_; }
  void set_handles(intptr_t value) { handles_size_ = value; }

 private:
  void GrowRememberedSet();
  void ShrinkRememberedSet();

  // Scavenging.
  void Scavenge(Reason reason);
  void FlipSpaces();
  void ScavengeRoots();
  uword ScavengeToSpace(uword scan);
  void PushTenureStack(uword addr);
  uword PopTenureStack();
  bool IsTenureStackEmpty();
  void ProcessTenureStack();
  void ScavengePointer(Object* ptr);
  void ScavengeOldObject(HeapObject obj);
  void ScavengeClass(intptr_t cid);

  // Mark-sweep.
  void MarkSweep(Reason reason);
  void MarkRoots();
  void MarkObject(Object obj);
  void ProcessMarkStack();
  void Sweep();
  bool SweepRegion(Region* region);
  void SetOldAllocationLimit();

  // Ephemerons.
  void AddToEphemeronList(Ephemeron ephemeron_corpse);
  void ScavengeEphemeronList();
  void MarkEphemeronList();
  void MournEphemeronList();

  // WeakArrays.
  void AddToWeakList(WeakArray survivor);
  void MournWeakListScavenge();
  void MournWeakListMarkSweep();
  void MournWeakPointerScavenge(Object* ptr);
  void MournWeakPointerMarkSweep(Object* ptr);

  // Weak class table.
  void MournClassTableScavenge();
  void MournClassTableMarkSweep();
  void MournClassTableForwarded();

  // Become.
  void ForwardClassIds();
  void ForwardRoots();
  void ForwardHeap();

  uword TryAllocateNew(intptr_t size) {
    uword result = top_;
    intptr_t remaining = end_ - top_;
    if (remaining < size) {
      return 0;
    }
    ASSERT((result & kObjectAlignmentMask) == kNewObjectAlignmentOffset);
    top_ += size;
    return result;
  }

  uword Allocate(intptr_t size, Allocator allocator) {
    ASSERT(Utils::IsAligned(size, kObjectAlignment));
    if (allocator == kSnapshot) {
      if (size >= kLargeAllocation) {
        return AllocateSnapshotLarge(size);
      }
      return AllocateSnapshotSmall(size);
    }
    if (size >= kLargeAllocation) {
      return AllocateOldLarge(size, kControlGrowth);
    }
    return AllocateNew(size);
  }

  uword AllocateNew(intptr_t size);
  uword AllocateTenure(intptr_t size);
  uword AllocateOldSmall(intptr_t size, GrowthPolicy growth);
  uword AllocateOldLarge(intptr_t size, GrowthPolicy growth);
  uword AllocateSnapshotSmall(intptr_t size);
  uword AllocateSnapshotLarge(intptr_t size);

  Region* AllocateRegion(intptr_t region_size, GrowthPolicy growth);

#if defined(DEBUG)
  bool InFromSpace(HeapObject obj) {
    return (obj->Addr() >= from_.base()) && (obj->Addr() < from_.limit());
  }
  bool InToSpace(HeapObject obj) {
    return (obj->Addr() >= to_.base()) && (obj->Addr() < to_.limit());
  }
#endif

  // New space.
  uword top_;
  uword end_;
  uword survivor_end_;
  Semispace to_;
  Semispace from_;
  size_t next_semispace_capacity_;

  // Old space.
  Region* regions_;
  FreeList freelist_;
  size_t old_size_;
  size_t old_capacity_;
  size_t old_limit_;

  // Remembered set.
  HeapObject* remembered_set_;
  intptr_t remembered_set_size_;
  intptr_t remembered_set_capacity_;

  // Class table.
  Object* class_table_;
  intptr_t class_table_size_;
  intptr_t class_table_capacity_;
  intptr_t class_table_free_;

  // Roots.
  Interpreter* interpreter_;
  static const intptr_t kHandlesCapacity = 8;
  Object* handles_[kHandlesCapacity];
  intptr_t handles_size_;
  friend class HandleScope;

  Ephemeron ephemeron_list_;
  WeakArray weak_list_;

  DISALLOW_COPY_AND_ASSIGN(Heap);
};


class HandleScope {
 public:
  HandleScope(Heap* heap, Object* ptr) : heap_(heap) {
    ASSERT(heap_->handles_size_ < Heap::kHandlesCapacity);
    heap_->handles_[heap_->handles_size_++] = ptr;
  }

  ~HandleScope() {
    heap_->handles_size_--;
  }

 private:
  Heap* heap_;
};

}  // namespace psoup

#endif  // VM_HEAP_H_
