// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_OBJECT_H_
#define VM_OBJECT_H_

#include "assert.h"
#include "globals.h"
#include "bitfield.h"
#include "utils.h"

namespace psoup {

enum PointerBits {
  kSmiTag = 0,
  kHeapObjectTag = 1,
  kSmiTagSize = 1,
  kSmiTagMask = 1,
  kSmiTagShift = 1,
};

enum ObjectAlignment {
  // Alignment offsets are used to determine object age.
  kNewObjectAlignmentOffset = kWordSize,
  kOldObjectAlignmentOffset = 0,
  // Object sizes are aligned to kObjectAlignment.
  kObjectAlignment = 2 * kWordSize,
  kObjectAlignmentLog2 = kWordSizeLog2 + 1,
  kObjectAlignmentMask = kObjectAlignment - 1,

  kNewObjectBits = kNewObjectAlignmentOffset | kHeapObjectTag,
  kOldObjectBits = kOldObjectAlignmentOffset | kHeapObjectTag,
};

enum HeaderBits {
  // New object: Already copied to to-space (is forwarding pointer).
  // Old object: Already seen by the marker (is gray or black).
  kMarkBit = 0,

  // In remembered set.
  kRememberedBit = 1,

  // For symbols.
  kCanonicalBit = 2,

#if defined(ARCH_IS_32_BIT)
  kSizeFieldOffset = 8,
  kSizeFieldSize = 8,
  kClassIdFieldOffset = 16,
  kClassIdFieldSize = 16,
#elif defined(ARCH_IS_64_BIT)
  kSizeFieldOffset = 16,
  kSizeFieldSize = 16,
  kClassIdFieldOffset = 32,
  kClassIdFieldSize = 32,
#endif
};

enum ClassIds {
  kIllegalCid = 0,
  kForwardingCorpseCid = 1,
  kFreeListElementCid = 2,

  kFirstLegalCid = 3,

  kSmiCid = 3,
  kMintCid = 4,
  kBigintCid = 5,
  kFloat64Cid = 6,
  kByteArrayCid = 7,
  kStringCid = 8,
  kArrayCid = 9,
  kWeakArrayCid = 10,
  kEphemeronCid = 11,
  kActivationCid = 12,
  kClosureCid = 13,

  kFirstRegularObjectCid = 14,
};

enum Barrier {
  kNoBarrier,
  kBarrier
};

class Heap;
class Isolate;

class AbstractMixin;
class Activation;
class Array;
class Behavior;
class ByteArray;
class Closure;
class Ephemeron;
class Method;
class Object;
class SmallInteger;
class String;
class WeakArray;

#define HEAP_OBJECT_IMPLEMENTATION(klass, base)                                \
 public:                                                                       \
  class Layout;                                                                \
  explicit constexpr klass() : base() {}                                       \
  explicit constexpr klass(uword tagged) : base(tagged) {}                     \
  explicit constexpr klass(const Object& obj) : base(obj) {}                   \
  constexpr klass(nullptr_t) : base(nullptr) {}                                \
  klass* operator ->() { return this; }                                        \
  const klass* operator ->() const { return this; }                            \
  static klass Cast(const Object& object) {                                    \
    return static_cast<klass>(object);                                         \
  }                                                                            \
 private:                                                                      \
  const Layout* ptr() const {                                                  \
    ASSERT(IsHeapObject());                                                    \
    return reinterpret_cast<const Layout*>(Addr());                            \
  }                                                                            \
  Layout* ptr() {                                                              \
    ASSERT(IsHeapObject());                                                    \
    return reinterpret_cast<Layout*>(Addr());                                  \
  }                                                                            \

class Object {
 public:
  bool IsForwardingCorpse() const { return ClassId() == kForwardingCorpseCid; }
  bool IsFreeListElement() const { return ClassId() == kFreeListElementCid; }
  bool IsArray() const { return ClassId() == kArrayCid; }
  bool IsByteArray() const { return ClassId() == kByteArrayCid; }
  bool IsString() const { return ClassId() == kStringCid; }
  bool IsActivation() const { return ClassId() == kActivationCid; }
  bool IsMediumInteger() const { return ClassId() == kMintCid; }
  bool IsLargeInteger() const { return ClassId() == kBigintCid; }
  bool IsFloat64() const { return ClassId() == kFloat64Cid; }
  bool IsWeakArray() const { return ClassId() == kWeakArrayCid; }
  bool IsEphemeron() const { return ClassId() == kEphemeronCid; }
  bool IsClosure() const { return ClassId() == kClosureCid; }
  bool IsRegularObject() const { return ClassId() >= kFirstRegularObjectCid; }
  bool IsBytes() const {
    return (ClassId() == kByteArrayCid) || (ClassId() == kStringCid);
  }

  bool IsHeapObject() const {
    return (tagged_pointer_ & kSmiTagMask) == kHeapObjectTag;
  }
  bool IsImmediateObject() const { return IsSmallInteger(); }
  bool IsSmallInteger() const {
    return (tagged_pointer_ & kSmiTagMask) == kSmiTag;
  }
  bool IsOldObject() const {
    return (tagged_pointer_ & kObjectAlignmentMask) == kOldObjectBits;
  }
  bool IsNewObject() const {
    return (tagged_pointer_ & kObjectAlignmentMask) == kNewObjectBits;
  }
  // Like !IsHeapObject() || IsOldObject(), but compiles to a single branch.
  bool IsImmediateOrOldObject() const {
    return (tagged_pointer_ & kObjectAlignmentMask) != kNewObjectBits;
  }
  bool IsImmediateOrNewObject() const {
    return (tagged_pointer_ & kObjectAlignmentMask) != kOldObjectBits;
  }

  inline intptr_t ClassId() const;
  Behavior Klass(Heap* heap) const;

  char* ToCString(Heap* heap) const;
  void Print(Heap* heap) const;

 public:
  constexpr Object() : tagged_pointer_(0) {}
  explicit constexpr Object(uword tagged) : tagged_pointer_(tagged) {}
  constexpr Object(nullptr_t) : tagged_pointer_(0) {}  // NOLINT

  Object* operator->() { return this; }

  constexpr bool operator ==(const Object& other) const {
    return tagged_pointer_ == other.tagged_pointer_;
  }
  constexpr bool operator !=(const Object& other) const {
    return tagged_pointer_ != other.tagged_pointer_;
  }
  constexpr bool operator ==(nullptr_t other) const {
    return tagged_pointer_ == 0;
  }
  constexpr bool operator !=(nullptr_t other) const {
    return tagged_pointer_ != 0;
  }

  operator bool() const = delete;
  explicit operator uword() const {
    return tagged_pointer_;
  }
  explicit operator intptr_t() const {
    return static_cast<intptr_t>(tagged_pointer_);
  }

 protected:
  uword tagged_pointer_;
};

class HeapObject : public Object {
  HEAP_OBJECT_IMPLEMENTATION(HeapObject, Object);

 public:
  void AssertCouldBeBehavior() const {
    ASSERT(IsHeapObject());
    ASSERT(IsRegularObject());
    // 8 slots for a class, 7 slots for a metaclass, plus 1 header.
    intptr_t heap_slots = heap_size() / sizeof(uword);
    ASSERT((heap_slots == 8) || (heap_slots == 10));
  }

  inline bool is_marked() const;
  inline void set_is_marked(bool value);
  inline bool is_remembered() const;
  inline void set_is_remembered(bool value);
  inline bool is_canonical() const;
  inline void set_is_canonical(bool value);
  inline intptr_t heap_size() const;
  inline intptr_t cid() const;
  inline void set_cid(intptr_t value);
  inline intptr_t header_hash() const;
  inline void set_header_hash(intptr_t value);

  uword Addr() const {
    return tagged_pointer_ - kHeapObjectTag;
  }
  static HeapObject FromAddr(uword addr) {
    return HeapObject(addr + kHeapObjectTag);
  }

  inline static HeapObject Initialize(uword addr,
                                      intptr_t cid,
                                      intptr_t heap_size);

  intptr_t HeapSize() const {
    ASSERT(IsHeapObject());
    intptr_t heap_size_from_tag = heap_size();
    if (heap_size_from_tag != 0) {
      return heap_size_from_tag;
    }
    return HeapSizeFromClass();
  }
  intptr_t HeapSizeFromClass() const;
  void Pointers(Object** from, Object** to);

 protected:
  template<typename type>
  type Load(type* addr, Barrier barrier = kBarrier) const {
    return *addr;
  }

  template<typename type>
  void Store(type* addr, type value, Barrier barrier) {
    *addr = value;
    if (barrier == kNoBarrier) {
      ASSERT(value->IsImmediateOrOldObject());
    } else {
      // Generational write barrier:
      if (IsOldObject() && value->IsNewObject() && !is_remembered()) {
        AddToRememberedSet();
      }
    }
  }

 private:
  void AddToRememberedSet() const;

  class MarkBit : public BitField<bool, kMarkBit, 1> {};
  class RememberedBit : public BitField<bool, kRememberedBit, 1> {};
  class CanonicalBit : public BitField<bool, kCanonicalBit, 1> {};
  class SizeField :
      public BitField<intptr_t, kSizeFieldOffset, kSizeFieldSize> {};
  class ClassIdField :
      public BitField<intptr_t, kClassIdFieldOffset, kClassIdFieldSize> {};
};

intptr_t Object::ClassId() const {
  if (IsSmallInteger()) {
    return kSmiCid;
  } else {
    return static_cast<const HeapObject*>(this)->cid();
  }
}

class ForwardingCorpse : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(ForwardingCorpse, HeapObject);

 public:
  inline Object target() const;
  inline void set_target(Object value);
  inline intptr_t overflow_size() const;
  inline void set_overflow_size(intptr_t value);
};

class FreeListElement : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(FreeListElement, HeapObject);

 public:
  inline FreeListElement next() const;
  inline void set_next(FreeListElement value);
  inline intptr_t overflow_size() const;
  inline void set_overflow_size(intptr_t value);
};

class SmallInteger : public Object {
 public:
  static const intptr_t kBits = kBitsPerWord - 2;
  static const intptr_t kMaxValue = (static_cast<intptr_t>(1) << kBits) - 1;
  static const intptr_t kMinValue = -(static_cast<intptr_t>(1) << kBits);

  explicit constexpr SmallInteger(const Object& obj) : Object(obj) {}
  explicit constexpr SmallInteger(uword tagged) : Object(tagged) {}
  const SmallInteger* operator->() const { return this; }

  static SmallInteger New(intptr_t value) {
    return static_cast<SmallInteger>(
        static_cast<uintptr_t>(value) << kSmiTagShift);
  }

  intptr_t value() const {
    ASSERT(IsSmallInteger());
    return static_cast<intptr_t>(tagged_pointer_) >> kSmiTagShift;
  }

#if defined(ARCH_IS_32_BIT)
  static bool IsSmiValue(int64_t value) {
    return (value >= static_cast<int64_t>(kMinValue)) &&
           (value <= static_cast<int64_t>(kMaxValue));
  }
#endif

  static bool IsSmiValue(intptr_t value) {
    intptr_t tagged = static_cast<uintptr_t>(value) << kSmiTagShift;
    intptr_t untagged = tagged >> kSmiTagShift;
    return untagged == value;
  }
};

class MediumInteger : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(MediumInteger, HeapObject);

 public:
  static const int64_t kMinValue = kMinInt64;
  static const int64_t kMaxValue = kMaxInt64;

  inline int64_t value() const;
  inline void set_value(int64_t value);
};

#if defined(ARCH_IS_32_BIT)
typedef uint16_t digit_t;
typedef uint32_t ddigit_t;
typedef int32_t sddigit_t;
#elif defined(ARCH_IS_64_BIT)
typedef uint32_t digit_t;
typedef uint64_t ddigit_t;
typedef int64_t sddigit_t;
#endif
const ddigit_t kDigitBits = sizeof(digit_t) * kBitsPerByte;
const ddigit_t kDigitShift = sizeof(digit_t) * kBitsPerByte;
const ddigit_t kDigitBase = static_cast<ddigit_t>(1) << kDigitBits;
const ddigit_t kDigitMask = kDigitBase - static_cast<ddigit_t>(1);

class LargeInteger : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(LargeInteger, HeapObject);

 public:
  enum DivOperationType {
    kTruncated,
    kFloored,
    kExact,
  };

  enum DivResultType {
    kQuoitent,
    kRemainder
  };

  static LargeInteger Expand(Object integer, Heap* H);
  static Object Reduce(LargeInteger integer, Heap* H);

  static intptr_t Compare(LargeInteger left, LargeInteger right);

  static LargeInteger Add(LargeInteger left,
                          LargeInteger right, Heap* H);
  static LargeInteger Subtract(LargeInteger left,
                               LargeInteger right, Heap* H);
  static LargeInteger Multiply(LargeInteger left,
                               LargeInteger right, Heap* H);
  static LargeInteger Divide(DivOperationType op_type,
                             DivResultType result_type,
                             LargeInteger left,
                             LargeInteger right,
                             Heap* H);

  static LargeInteger And(LargeInteger left,
                          LargeInteger right, Heap* H);
  static LargeInteger Or(LargeInteger left,
                         LargeInteger right, Heap* H);
  static LargeInteger Xor(LargeInteger left,
                          LargeInteger right, Heap* H);
  static LargeInteger ShiftRight(LargeInteger left,
                                 intptr_t raw_right, Heap* H);
  static LargeInteger ShiftLeft(LargeInteger left,
                                intptr_t raw_right, Heap* H);

  static String PrintString(LargeInteger large, Heap* H);

  static double AsDouble(LargeInteger integer);
  static bool FromDouble(double raw_value, Object* result, Heap* H);

  inline bool negative() const;
  inline void set_negative(bool v);
  inline intptr_t size() const;
  inline void set_size(intptr_t value);
  inline intptr_t capacity() const;
  inline void set_capacity(intptr_t value);
  inline digit_t digit(intptr_t index) const;
  inline void set_digit(intptr_t index, digit_t value);
};

class RegularObject : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(RegularObject, HeapObject);

 public:
  inline Object slot(intptr_t index) const;
  inline void set_slot(intptr_t index, Object value,
                       Barrier barrier = kBarrier);

  inline Object* from();
  inline Object* to();
};

class Array : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Array, HeapObject);

 public:
  inline SmallInteger size() const;
  inline void set_size(SmallInteger s);
  intptr_t Size() const { return size()->value(); }

  inline Object element(intptr_t index) const;
  inline void set_element(intptr_t index, Object value,
                          Barrier barrier = kBarrier);

  inline Object* from();
  inline Object* to();
};

class WeakArray : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(WeakArray, HeapObject);

 public:
  inline SmallInteger size() const;
  inline void set_size(SmallInteger s);
  intptr_t Size() const { return size()->value(); }

  // Only accessed by the GC. Bypasses barrier, including assertions.
  inline WeakArray next() const;
  inline void set_next(WeakArray value);

  inline Object element(intptr_t index) const;
  inline void set_element(intptr_t index, Object value,
                          Barrier barrier = kBarrier);

  inline Object* from();
  inline Object* to();
};

class Ephemeron : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Ephemeron, HeapObject);

 public:
  inline Object key() const;
  inline Object* key_ptr();
  inline void set_key(Object key, Barrier barrier = kBarrier);

  inline Object value() const;
  inline Object* value_ptr();
  inline void set_value(Object value, Barrier barrier = kBarrier);

  inline Object finalizer() const;
  inline Object* finalizer_ptr();
  inline void set_finalizer(Object finalizer, Barrier barrier = kBarrier);

  // Only accessed by the GC. Bypasses barrier, including assertions.
  inline Ephemeron next() const;
  inline void set_next(Ephemeron value);

  inline Object* from();
  inline Object* to();
};

class Bytes : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Bytes, HeapObject);

 public:
  inline SmallInteger size() const;
  inline void set_size(SmallInteger s);
  intptr_t Size() const { return size()->value(); }

  inline uint8_t element(intptr_t index) const;
  inline void set_element(intptr_t index, uint8_t value);
  inline uint8_t* element_addr(intptr_t index);
  inline const uint8_t* element_addr(intptr_t index) const;
};

class String : public Bytes {
  HEAP_OBJECT_IMPLEMENTATION(String, Bytes);

 public:
  SmallInteger EnsureHash(Isolate* isolate);
};

class ByteArray : public Bytes {
  HEAP_OBJECT_IMPLEMENTATION(ByteArray, Bytes);
};

static const intptr_t kMaxTemps = 35;

class Activation : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Activation, HeapObject);

 public:
  inline Activation sender() const;
  inline void set_sender(Activation s, Barrier barrier = kBarrier);
  Object* sender_fp() const {
    return reinterpret_cast<Object*>(static_cast<uword>(sender()));
  }
  void set_sender_fp(Object* fp) {
    Activation sender = static_cast<Activation>(reinterpret_cast<uword>(fp));
    ASSERT(sender->IsSmallInteger());
    set_sender(sender, kNoBarrier);
  }

  inline SmallInteger bci() const;
  inline void set_bci(SmallInteger i);

  inline Method method() const;
  inline void set_method(Method m, Barrier barrier = kBarrier);

  inline Closure closure() const;
  inline void set_closure(Closure m, Barrier barrier = kBarrier);

  inline Object receiver() const;
  inline void set_receiver(Object o, Barrier barrier = kBarrier);

  inline SmallInteger stack_depth() const;
  inline void set_stack_depth(SmallInteger d);
  intptr_t StackDepth() const { return stack_depth()->value(); }

  inline Object temp(intptr_t index) const;
  inline void set_temp(intptr_t index, Object o, Barrier barrier = kBarrier);

  void PopNAndPush(intptr_t drop_count, Object value) {
    ASSERT(drop_count >= 0);
    ASSERT(drop_count <= StackDepth());
    set_stack_depth(SmallInteger::New(StackDepth() - drop_count + 1));
    set_temp(StackDepth() - 1, value);
  }
  void Push(Object value) {
    PopNAndPush(0, value);
  }

  void PrintStack(Heap* heap);

  inline Object* from();
  inline Object* to();
};

class Method : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Method, HeapObject);

 public:
  inline SmallInteger header() const;
  inline Array literals() const;
  inline ByteArray bytecode() const;
  inline AbstractMixin mixin() const;
  inline String selector() const;
  inline Object source() const;

  bool IsPublic() const {
    uword am = header()->value() >> 28;
    ASSERT((am == 0) || (am == 1) || (am == 2));
    return am == 0;
  }
  bool IsProtected() const {
    uword am = header()->value() >> 28;
    ASSERT((am == 0) || (am == 1) || (am == 2));
    return am == 1;
  }
  bool IsPrivate() const {
    uword am = header()->value() >> 28;
    ASSERT((am == 0) || (am == 1) || (am == 2));
    return am == 2;
  }
  intptr_t Primitive() const {
    return (header()->value() >> 16) & 1023;
  }
  intptr_t NumArgs() const {
    return (header()->value() >> 0) & 255;
  }
  intptr_t NumTemps() const {
    return (header()->value() >> 8) & 255;
  }

  const uint8_t* IP(const SmallInteger bci) {
    return bytecode()->element_addr(bci->value() - 1);
  }
  SmallInteger BCI(const uint8_t* ip) {
    return SmallInteger::New((ip - bytecode()->element_addr(0)) + 1);
  }
};

class Float64 : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Float64, HeapObject);

 public:
  inline double value() const;
  inline void set_value(double v);
};

class Closure : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Closure, HeapObject);

 public:
  inline SmallInteger num_copied() const;
  inline void set_num_copied(SmallInteger v);
  intptr_t NumCopied() const { return num_copied()->value(); }

  inline Activation defining_activation() const;
  inline void set_defining_activation(Activation a, Barrier barrier = kBarrier);

  inline SmallInteger initial_bci() const;
  inline void set_initial_bci(SmallInteger bci);

  inline SmallInteger num_args() const;
  inline void set_num_args(SmallInteger num);

  inline Object copied(intptr_t index) const;
  inline void set_copied(intptr_t index, Object o, Barrier barrier = kBarrier);

  inline Object* from();
  inline Object* to();
};

class Behavior : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Behavior, HeapObject);

 public:
  inline Behavior superclass() const;
  inline Array methods() const;
  inline AbstractMixin mixin() const;
  inline Object enclosing_object() const;
  inline SmallInteger id() const;
  inline void set_id(SmallInteger id);
  inline SmallInteger format() const;
};

class Class : public Behavior {
  HEAP_OBJECT_IMPLEMENTATION(Class, Behavior);

 public:
  inline String name() const;
  inline WeakArray subclasses() const;
};

class Metaclass : public Behavior {
  HEAP_OBJECT_IMPLEMENTATION(Metaclass, Behavior);

 public:
  inline Class this_class() const;
};

class AbstractMixin : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(AbstractMixin, HeapObject);

 public:
  inline String name() const;
  inline Array methods() const;
  inline AbstractMixin enclosing_mixin() const;
};

class Message : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(Message, HeapObject);

 public:
  inline void set_selector(String selector, Barrier barrier = kBarrier);
  inline void set_arguments(Array arguments, Barrier barrier = kBarrier);
};

class ObjectStore : public HeapObject {
  HEAP_OBJECT_IMPLEMENTATION(ObjectStore, HeapObject);

 public:
  inline class SmallInteger size() const;
  inline Object nil_obj() const;
  inline Object false_obj() const;
  inline Object true_obj() const;
  inline Object message_loop() const;
  inline class Array common_selectors() const;
  inline class String does_not_understand() const;
  inline class String non_boolean_receiver() const;
  inline class String cannot_return() const;
  inline class String about_to_return_through() const;
  inline class String unused_bytecode() const;
  inline class String dispatch_message() const;
  inline class String dispatch_signal() const;
  inline Behavior Array() const;
  inline Behavior ByteArray() const;
  inline Behavior String() const;
  inline Behavior Closure() const;
  inline Behavior Ephemeron() const;
  inline Behavior Float64() const;
  inline Behavior LargeInteger() const;
  inline Behavior MediumInteger() const;
  inline Behavior Message() const;
  inline Behavior SmallInteger() const;
  inline Behavior WeakArray() const;
  inline Behavior Activation() const;
  inline Behavior Method() const;
};

class HeapObject::Layout {
 public:
  uword header_;
  uword header_hash_;
};

class ForwardingCorpse::Layout : public HeapObject::Layout {
 public:
  intptr_t overflow_size_;
};

class FreeListElement::Layout : public HeapObject::Layout {
 public:
  intptr_t overflow_size_;
};

class MediumInteger::Layout : public HeapObject::Layout {
 public:
  int64_t value_;
};

class LargeInteger::Layout : public HeapObject::Layout {
 public:
  intptr_t capacity_;
  intptr_t negative_;  // TODO(rmacnak): Use a header bit?
  intptr_t size_;
  digit_t digits_[];
};

class RegularObject::Layout : public HeapObject::Layout {
 public:
  Object slots_[];
};

class Array::Layout : public HeapObject::Layout {
 public:
  SmallInteger size_;
  Object elements_[];
};

class WeakArray::Layout : public HeapObject::Layout {
 public:
  SmallInteger size_;  // Not visited.
  WeakArray next_;  // Not visited.
  Object elements_[];
};

class Ephemeron::Layout : public HeapObject::Layout {
 public:
  Object key_;
  Object value_;
  Object finalizer_;
  Ephemeron next_;  // Not visited.
};

class Bytes::Layout : public HeapObject::Layout {
 public:
  SmallInteger size_;
};

class String::Layout : public Bytes::Layout {};

class ByteArray::Layout : public Bytes::Layout {};

class Method::Layout : public HeapObject::Layout {
 public:
  SmallInteger header_;
  Array literals_;
  ByteArray bytecode_;
  AbstractMixin mixin_;
  String selector_;
  Object source_;
};

class Activation::Layout : public HeapObject::Layout {
 public:
  Activation sender_;
  SmallInteger bci_;
  Method method_;
  Closure closure_;
  Object receiver_;
  SmallInteger stack_depth_;
  Object temps_[kMaxTemps];
};

class Float64::Layout : public HeapObject::Layout {
 public:
  double value_;
};

class Closure::Layout : public HeapObject::Layout {
 public:
  SmallInteger num_copied_;
  Activation defining_activation_;
  SmallInteger initial_bci_;
  SmallInteger num_args_;
  Object copied_[];
};

class Behavior::Layout : public HeapObject::Layout {
 public:
  Behavior superclass_;
  Array methods_;
  Object enclosing_object_;
  AbstractMixin mixin_;
  SmallInteger classid_;
  SmallInteger format_;
};

class Class::Layout : public Behavior::Layout {
 public:
  String name_;
  WeakArray subclasses_;
};

class Metaclass::Layout : public Behavior::Layout {
 public:
  Class this_class_;
};

class AbstractMixin::Layout : public HeapObject::Layout {
 public:
  String name_;
  Array methods_;
  AbstractMixin enclosing_mixin_;
};

class Message::Layout : public HeapObject::Layout {
 public:
  String selector_;
  Array arguments_;
};

class ObjectStore::Layout : public HeapObject::Layout {
 public:
  class SmallInteger array_size_;
  Object nil_;
  Object false_;
  Object true_;
  Object message_loop_;
  class Array common_selectors_;
  class String does_not_understand_;
  class String non_boolean_receiver_;
  class String cannot_return_;
  class String about_to_return_through_;
  class String unused_bytecode_;
  class String dispatch_message_;
  class String dispatch_signal_;
  Behavior Array_;
  Behavior ByteArray_;
  Behavior String_;
  Behavior Closure_;
  Behavior Ephemeron_;
  Behavior Float64_;
  Behavior LargeInteger_;
  Behavior MediumInteger_;
  Behavior Message_;
  Behavior SmallInteger_;
  Behavior WeakArray_;
  Behavior Activation_;
  Behavior Method_;
};

bool HeapObject::is_marked() const {
  return MarkBit::decode(ptr()->header_);
}
void HeapObject::set_is_marked(bool value) {
  ptr()->header_ = MarkBit::update(value, ptr()->header_);
}
bool HeapObject::is_remembered() const {
  return RememberedBit::decode(ptr()->header_);
}
void HeapObject::set_is_remembered(bool value) {
  ptr()->header_ = RememberedBit::update(value, ptr()->header_);
}
bool HeapObject::is_canonical() const {
  return CanonicalBit::decode(ptr()->header_);
}
void HeapObject::set_is_canonical(bool value) {
  ptr()->header_ = CanonicalBit::update(value, ptr()->header_);
}
intptr_t HeapObject::heap_size() const {
  return SizeField::decode(ptr()->header_) << kObjectAlignmentLog2;
}
intptr_t HeapObject::cid() const {
  return ClassIdField::decode(ptr()->header_);
}
void HeapObject::set_cid(intptr_t value) {
  ptr()->header_ = ClassIdField::update(value, ptr()->header_);
}
intptr_t HeapObject::header_hash() const {
  return ptr()->header_hash_;
}
void HeapObject::set_header_hash(intptr_t value) {
  ptr()->header_hash_ = value;
}

HeapObject HeapObject::Initialize(uword addr,
                                intptr_t cid,
                                intptr_t heap_size) {
  ASSERT(cid != kIllegalCid);
  ASSERT((heap_size & kObjectAlignmentMask) == 0);
  ASSERT(heap_size > 0);
  intptr_t size_tag = heap_size >> kObjectAlignmentLog2;
  if (!SizeField::is_valid(size_tag)) {
    size_tag = 0;
    ASSERT(cid < kFirstRegularObjectCid);
  }
  uword header = 0;
  header = SizeField::update(size_tag, header);
  header = ClassIdField::update(cid, header);
  HeapObject obj = FromAddr(addr);
  obj.ptr()->header_ = header;
  obj.ptr()->header_hash_ = 0;
  ASSERT(obj.cid() == cid);
  ASSERT(!obj.is_marked());
  return obj;
}

Object ForwardingCorpse::target() const {
  return static_cast<Object>(ptr()->header_hash_);
}
void ForwardingCorpse::set_target(Object value) {
  ptr()->header_hash_ = static_cast<uword>(value);
}
intptr_t ForwardingCorpse::overflow_size() const {
  return ptr()->overflow_size_;
}
void ForwardingCorpse::set_overflow_size(intptr_t value) {
  ptr()->overflow_size_ = value;
}

FreeListElement FreeListElement::next() const {
  return static_cast<FreeListElement>(ptr()->header_hash_);
}
void FreeListElement::set_next(FreeListElement value) {
  ASSERT((value == nullptr) || value->IsHeapObject());  // Tagged.
  ptr()->header_hash_ = static_cast<uword>(value);
}
intptr_t FreeListElement::overflow_size() const {
  return ptr()->overflow_size_;
}
void FreeListElement::set_overflow_size(intptr_t value) {
  ptr()->overflow_size_ = value;
}

int64_t MediumInteger::value() const { return ptr()->value_; }
void MediumInteger::set_value(int64_t value) { ptr()->value_ = value; }

bool LargeInteger::negative() const {
  return ptr()->negative_;
}
void LargeInteger::set_negative(bool v) {
  ptr()->negative_ = v;
}
intptr_t LargeInteger::size() const {
  return ptr()->size_;
}
void LargeInteger::set_size(intptr_t value) {
  ptr()->size_ = value;
}
intptr_t LargeInteger::capacity() const {
  return ptr()->capacity_;
}
void LargeInteger::set_capacity(intptr_t value) {
  ptr()->capacity_ = value;
}
digit_t LargeInteger::digit(intptr_t index) const {
  return ptr()->digits_[index];
}
void LargeInteger::set_digit(intptr_t index, digit_t value) {
  ptr()->digits_[index] = value;
}

Object RegularObject::slot(intptr_t index) const {
  return Load(&ptr()->slots_[index]);
}
void RegularObject::set_slot(intptr_t index, Object value,
                             Barrier barrier) {
  Store(&ptr()->slots_[index], value, barrier);
}
Object* RegularObject::from() {
  return &ptr()->slots_[0];
}
Object* RegularObject::to() {
  intptr_t num_slots =
      (heap_size() - sizeof(HeapObject::Layout)) >> kWordSizeLog2;
  return &ptr()->slots_[num_slots - 1];
}

SmallInteger Array::size() const { return Load(&ptr()->size_, kNoBarrier); }
void Array::set_size(SmallInteger s) { Store(&ptr()->size_, s, kNoBarrier); }
Object Array::element(intptr_t index) const {
  return Load(&ptr()->elements_[index]);
}
void Array::set_element(intptr_t index, Object value, Barrier barrier) {
  Store(&ptr()->elements_[index], value, barrier);
}
Object* Array::from() {
  return &ptr()->elements_[0];
}
Object* Array::to() {
  return &ptr()->elements_[Size() - 1];
}

SmallInteger WeakArray::size() const { return Load(&ptr()->size_, kNoBarrier); }
void WeakArray::set_size(SmallInteger s) {
  Store(&ptr()->size_, s, kNoBarrier);
}
WeakArray WeakArray::next() const { return ptr()->next_; }
void WeakArray::set_next(WeakArray value) { ptr()->next_ = value; }
Object WeakArray::element(intptr_t index) const {
  return Load(&ptr()->elements_[index]);
}
void WeakArray::set_element(intptr_t index, Object value, Barrier barrier) {
  Store(&ptr()->elements_[index], value, barrier);
}
Object* WeakArray::from() {
  return &ptr()->elements_[0];
}
Object* WeakArray::to() {
  return &ptr()->elements_[Size() - 1];
}

Object Ephemeron::key() const { return ptr()->key_; }
Object* Ephemeron::key_ptr() { return &ptr()->key_; }
void Ephemeron::set_key(Object key, Barrier barrier) {
  Store(&ptr()->key_, key, barrier);
}
Object Ephemeron::value() const { return Load(&ptr()->value_); }
Object* Ephemeron::value_ptr() { return &ptr()->value_; }
void Ephemeron::set_value(Object value, Barrier barrier) {
  Store(&ptr()->value_, value, barrier);
}
Object Ephemeron::finalizer() const { return Load(&ptr()->finalizer_); }
Object* Ephemeron::finalizer_ptr() { return &ptr()->finalizer_; }
void Ephemeron::set_finalizer(Object finalizer, Barrier barrier) {
  Store(&ptr()->finalizer_, finalizer, barrier);
}
Ephemeron Ephemeron::next() const { return ptr()->next_; }
void Ephemeron::set_next(Ephemeron value) { ptr()->next_ = value; }
Object* Ephemeron::from() { return &ptr()->key_; }
Object* Ephemeron::to() { return &ptr()->finalizer_; }

SmallInteger Bytes::size() const { return Load(&ptr()->size_, kNoBarrier); }
void Bytes::set_size(SmallInteger s) { Store(&ptr()->size_, s, kNoBarrier); }
uint8_t Bytes::element(intptr_t index) const {
  return *element_addr(index);
}
void Bytes::set_element(intptr_t index, uint8_t value) {
  *element_addr(index) = value;
}
uint8_t* Bytes::element_addr(intptr_t index) {
  uint8_t* elements = reinterpret_cast<uint8_t*>(
      reinterpret_cast<uword>(ptr()) + sizeof(Bytes::Layout));
  return &elements[index];
}
const uint8_t* Bytes::element_addr(intptr_t index) const {
  const uint8_t* elements = reinterpret_cast<const uint8_t*>(
      reinterpret_cast<uword>(ptr()) + sizeof(Bytes::Layout));
  return &elements[index];
}

SmallInteger Method::header() const { return Load(&ptr()->header_); }
Array Method::literals() const { return Load(&ptr()->literals_); }
ByteArray Method::bytecode() const { return Load(&ptr()->bytecode_); }
AbstractMixin Method::mixin() const { return Load(&ptr()->mixin_); }
String Method::selector() const { return Load(&ptr()->selector_); }
Object Method::source() const { return Load(&ptr()->source_); }

Activation Activation::sender() const { return Load(&ptr()->sender_); }
void Activation::set_sender(Activation s, Barrier barrier) {
  Store(&ptr()->sender_, s, barrier);
}
SmallInteger Activation::bci() const { return Load(&ptr()->bci_, kNoBarrier); }
void Activation::set_bci(SmallInteger i) { Store(&ptr()->bci_, i, kNoBarrier); }
Method Activation::method() const { return Load(&ptr()->method_); }
void Activation::set_method(Method m, Barrier barrier) {
  Store(&ptr()->method_, m, barrier);
}
Closure Activation::closure() const { return Load(&ptr()->closure_); }
void Activation::set_closure(Closure m, Barrier barrier) {
  Store(&ptr()->closure_, m, barrier);
}
Object Activation::receiver() const { return Load(&ptr()->receiver_); }
void Activation::set_receiver(Object o, Barrier barrier) {
  Store(&ptr()->receiver_, o, barrier);
}
SmallInteger Activation::stack_depth() const {
  return Load(&ptr()->stack_depth_, kNoBarrier);
}
void Activation::set_stack_depth(SmallInteger d) {
  Store(&ptr()->stack_depth_, d, kNoBarrier);
}
Object Activation::temp(intptr_t index) const {
  return Load(&ptr()->temps_[index]);
}
void Activation::set_temp(intptr_t index, Object o, Barrier barrier) {
  Store(&ptr()->temps_[index], o, barrier);
}
Object* Activation::from() {
  return reinterpret_cast<Object*>(&ptr()->sender_);
}
Object* Activation::to() {
  return reinterpret_cast<Object*>(&ptr()->stack_depth_) + StackDepth();
}

double Float64::value() const { return ptr()->value_; }
void Float64::set_value(double v) { ptr()->value_ = v; }

SmallInteger Closure::num_copied() const {
  return Load(&ptr()->num_copied_, kNoBarrier);
}
void Closure::set_num_copied(SmallInteger v) {
  Store(&ptr()->num_copied_, v, kNoBarrier);
}
Activation Closure::defining_activation() const {
  return Load(&ptr()->defining_activation_);
}
void Closure::set_defining_activation(Activation a, Barrier barrier) {
  Store(&ptr()->defining_activation_, a, barrier);
}
SmallInteger Closure::initial_bci() const {
  return Load(&ptr()->initial_bci_, kNoBarrier);
}
void Closure::set_initial_bci(SmallInteger bci) {
  Store(&ptr()->initial_bci_, bci, kNoBarrier);
}
SmallInteger Closure::num_args() const {
  return Load(&ptr()->num_args_, kNoBarrier);
}
void Closure::set_num_args(SmallInteger num) {
  Store(&ptr()->num_args_, num, kNoBarrier);
}
Object Closure::copied(intptr_t index) const {
  return Load(&ptr()->copied_[index]);
}
void Closure::set_copied(intptr_t index, Object o, Barrier barrier ) {
  Store(&ptr()->copied_[index], o, barrier);
}
Object* Closure::from() {
  return reinterpret_cast<Object*>(&ptr()->num_copied_);
}
Object* Closure::to() {
  return reinterpret_cast<Object*>(&ptr()->copied_[NumCopied() - 1]);
}

Behavior Behavior::superclass() const { return Load(&ptr()->superclass_); }
Array Behavior::methods() const { return Load(&ptr()->methods_); }
AbstractMixin Behavior::mixin() const { return Load(&ptr()->mixin_); }
Object Behavior::enclosing_object() const {
  return Load(&ptr()->enclosing_object_);
}
SmallInteger Behavior::id() const { return Load(&ptr()->classid_, kNoBarrier); }
void Behavior::set_id(SmallInteger id) {
  Store(&ptr()->classid_, id, kNoBarrier);
}
SmallInteger Behavior::format() const {
  return Load(&ptr()->format_, kNoBarrier);
}

String Class::name() const { return Load(&ptr()->name_); }
WeakArray Class::subclasses() const { return Load(&ptr()->subclasses_); }

Class Metaclass::this_class() const { return Load(&ptr()->this_class_); }

String AbstractMixin::name() const { return Load(&ptr()->name_); }
Array AbstractMixin::methods() const { return Load(&ptr()->methods_); }
AbstractMixin AbstractMixin::enclosing_mixin() const {
  return Load(&ptr()->enclosing_mixin_);
}

void Message::set_selector(String selector, Barrier barrier) {
  Store(&ptr()->selector_, selector, barrier);
}
void Message::set_arguments(Array arguments, Barrier barrier) {
  Store(&ptr()->arguments_, arguments, barrier);
}

class SmallInteger ObjectStore::size() const { return ptr()->array_size_; }
Object ObjectStore::nil_obj() const { return ptr()->nil_; }
Object ObjectStore::false_obj() const { return ptr()->false_; }
Object ObjectStore::true_obj() const { return ptr()->true_; }
Object ObjectStore::message_loop() const { return ptr()->message_loop_; }
class Array ObjectStore::common_selectors() const {
  return ptr()->common_selectors_;
}
class String ObjectStore::does_not_understand() const {
  return ptr()->does_not_understand_;
}
class String ObjectStore::non_boolean_receiver() const {
  return ptr()->non_boolean_receiver_;
}
class String ObjectStore::cannot_return() const {
  return ptr()->cannot_return_;
}
class String ObjectStore::about_to_return_through() const {
  return ptr()->about_to_return_through_;
}
class String ObjectStore::unused_bytecode() const {
  return ptr()->unused_bytecode_;
}
class String ObjectStore::dispatch_message() const {
  return ptr()->dispatch_message_;
}
class String ObjectStore::dispatch_signal() const {
  return ptr()->dispatch_signal_;
}
Behavior ObjectStore::Array() const { return ptr()->Array_; }
Behavior ObjectStore::ByteArray() const { return ptr()->ByteArray_; }
Behavior ObjectStore::String() const { return ptr()->String_; }
Behavior ObjectStore::Closure() const { return ptr()->Closure_; }
Behavior ObjectStore::Ephemeron() const { return ptr()->Ephemeron_; }
Behavior ObjectStore::Float64() const { return ptr()->Float64_; }
Behavior ObjectStore::LargeInteger() const { return ptr()->LargeInteger_; }
Behavior ObjectStore::MediumInteger() const { return ptr()->MediumInteger_; }
Behavior ObjectStore::Message() const { return ptr()->Message_; }
Behavior ObjectStore::SmallInteger() const { return ptr()->SmallInteger_; }
Behavior ObjectStore::WeakArray() const { return ptr()->WeakArray_; }
Behavior ObjectStore::Activation() const { return ptr()->Activation_; }
Behavior ObjectStore::Method() const { return ptr()->Method_; }

}  // namespace psoup

#endif  // VM_OBJECT_H_
