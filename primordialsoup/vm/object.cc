// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "object.h"

#include "heap.h"
#include "interpreter.h"
#include "isolate.h"
#include "os.h"

namespace psoup {

Behavior Object::Klass(Heap* heap) const {
  return heap->ClassAt(ClassId());
}


intptr_t HeapObject::HeapSizeFromClass() const {
  ASSERT(IsHeapObject());

  switch (cid()) {
  case kIllegalCid:
    UNREACHABLE();
  case kForwardingCorpseCid:
    return static_cast<const ForwardingCorpse>(*this)->overflow_size();
  case kFreeListElementCid:
    return static_cast<const FreeListElement>(*this)->overflow_size();
  case kSmiCid:
    UNREACHABLE();
  case kMintCid:
    return AllocationSize(sizeof(MediumInteger::Layout));
  case kFloat64Cid:
    return AllocationSize(sizeof(Float64::Layout));
  case kBigintCid:
    return AllocationSize(sizeof(LargeInteger::Layout) +
        sizeof(digit_t) * LargeInteger::Cast(*this)->capacity());
  case kByteArrayCid:
    return AllocationSize(sizeof(ByteArray::Layout) +
                          sizeof(uint8_t) * ByteArray::Cast(*this)->Size());
  case kStringCid:
    return AllocationSize(sizeof(String::Layout) +
                          sizeof(uint8_t) * String::Cast(*this)->Size());
  case kArrayCid:
    return AllocationSize(sizeof(Array::Layout) +
                          sizeof(Object) * Array::Cast(*this)->Size());
  case kWeakArrayCid:
    return AllocationSize(sizeof(WeakArray::Layout) +
                          sizeof(Object) * WeakArray::Cast(*this)->Size());
  case kEphemeronCid:
    return AllocationSize(sizeof(Ephemeron::Layout));
  case kActivationCid:
    return AllocationSize(sizeof(Activation::Layout));
  case kClosureCid:
    return AllocationSize(sizeof(Closure::Layout) +
                          sizeof(Object) * Closure::Cast(*this)->NumCopied());
  default:
    UNREACHABLE();
    // Need to get num slots from class.
    return -1;
  }
}


void HeapObject::Pointers(Object** from, Object** to) {
  ASSERT(IsHeapObject());

  switch (cid()) {
  case kIllegalCid:
  case kForwardingCorpseCid:
  case kFreeListElementCid:
  case kSmiCid:
    UNREACHABLE();
  case kMintCid:
  case kBigintCid:
  case kFloat64Cid:
  case kByteArrayCid:
  case kStringCid:
    // No pointers (or only smis for size/hash)
    *from = reinterpret_cast<Object*>(1);
    *to = reinterpret_cast<Object*>(0);
    return;
  case kArrayCid:
    *from = Array::Cast(*this)->from();
    *to = Array::Cast(*this)->to();
    return;
  case kWeakArrayCid:
    *from = WeakArray::Cast(*this)->from();
    *to = WeakArray::Cast(*this)->to();
    return;
  case kEphemeronCid:
    *from = RegularObject::Cast(*this)->from();
    *to = RegularObject::Cast(*this)->to();
    return;
  case kActivationCid:
    *from = Activation::Cast(*this)->from();
    *to = Activation::Cast(*this)->to();
    return;
  case kClosureCid:
    *from = Closure::Cast(*this)->from();
    *to = Closure::Cast(*this)->to();
    return;
  default:
    *from = RegularObject::Cast(*this)->from();
    *to = RegularObject::Cast(*this)->to();
    return;
  }
}


void HeapObject::AddToRememberedSet() const {
  Isolate* isolate = Isolate::Current();
  ASSERT(isolate != NULL);
  isolate->heap()->AddToRememberedSet(*this);
}


char* Object::ToCString(Heap* heap) const {
  switch (ClassId()) {
  case kIllegalCid:
  case kForwardingCorpseCid:
  case kFreeListElementCid:
    UNREACHABLE();
  case kSmiCid:
    return OS::PrintStr("a SmallInteger(%" Pd ")",
                        static_cast<const SmallInteger>(*this)->value());
  case kMintCid:
    return OS::PrintStr("a MediumInteger(%" Pd64 ")",
                        MediumInteger::Cast(*this)->value());
  case kBigintCid:
    return OS::PrintStr("a LargeInteger(%" Pd " digits)",
                        LargeInteger::Cast(*this)->size());
  case kFloat64Cid:
    return OS::PrintStr("a Float(%lf)", Float64::Cast(*this)->value());
  case kByteArrayCid:
    return OS::PrintStr("a ByteArray(%" Pd ")", ByteArray::Cast(*this)->Size());
  case kStringCid:
    return OS::PrintStr("a String %.*s",
                        static_cast<int>(String::Cast(*this)->Size()),
                        String::Cast(*this)->element_addr(0));
  case kArrayCid:
    return OS::PrintStr("an Array(%" Pd ")", Array::Cast(*this)->Size());
  case kWeakArrayCid:
    return OS::PrintStr("a WeakArray(%" Pd ")", WeakArray::Cast(*this)->Size());
  case kEphemeronCid:
    return strdup("an Ephemeron");
  case kActivationCid:
    return strdup("an Activation");
  case kClosureCid:
    return strdup("a Closure");
  default:
    Behavior cls = Klass(heap);
    Behavior theMetaclass = heap->ClassAt(kSmiCid)->Klass(heap)->Klass(heap);
    if (cls->Klass(heap) == theMetaclass) {
      ASSERT(cls->HeapSize() >= AllocationSize(sizeof(Metaclass::Layout)));
      // A Metaclass.
      String name = static_cast<Metaclass>(cls)->this_class()->name();
      if (!name->IsString()) {
        return strdup("instance of uninitialized metaclass?");
      }
      return OS::PrintStr("instance of %.*s class",
                          static_cast<int>(name->Size()),
                          reinterpret_cast<const char*>(name->element_addr(0)));
    } else {
      ASSERT(cls->HeapSize() >= AllocationSize(sizeof(Class::Layout)));
      // A Class.
      String name = static_cast<Class>(cls)->name();
      if (!name->IsString()) {
        return strdup("instance of uninitialized class?");
      }
      return OS::PrintStr("instance of %.*s",
                          static_cast<int>(name->Size()),
                          reinterpret_cast<const char*>(name->element_addr(0)));
    }
    UNREACHABLE();
    return strdup("a RegularObject");
  }
}


void Object::Print(Heap* heap) const {
  char* cstr = ToCString(heap);
  OS::Print("%s\n", cstr);
  free(cstr);
}


static void PrintStringError(String string) {
  const char* cstr = reinterpret_cast<const char*>(string->element_addr(0));
  OS::PrintErr("%.*s", static_cast<int>(string->Size()), cstr);
}


void Activation::PrintStack(Heap* heap) {
  Activation act = *this;
  while (act != heap->interpreter()->nil_obj()) {
    OS::PrintErr("  ");

    Activation home = act;
    while (home->closure() != heap->interpreter()->nil_obj()) {
      ASSERT(home->closure()->IsClosure());
      OS::PrintErr("[] in ");
      home = home->closure()->defining_activation();
    }

    AbstractMixin receiver_mixin = home->receiver()->Klass(heap)->mixin();
    String receiver_mixin_name = receiver_mixin->name();
    if (receiver_mixin_name->IsString()) {
      PrintStringError(receiver_mixin_name);
    } else {
      receiver_mixin_name =
          static_cast<AbstractMixin>(receiver_mixin_name)->name();
      ASSERT(receiver_mixin_name->IsString());
      PrintStringError(receiver_mixin_name);
      OS::PrintErr(" class");
    }

    AbstractMixin method_mixin = home->method()->mixin();
    if (receiver_mixin != method_mixin) {
      String method_mixin_name = method_mixin->name();
      OS::PrintErr("(");
      if (method_mixin_name->IsString()) {
        PrintStringError(method_mixin_name);
      } else {
        method_mixin_name =
            static_cast<AbstractMixin>(method_mixin_name)->name();
        ASSERT(method_mixin_name->IsString());
        PrintStringError(method_mixin_name);
        OS::PrintErr(" class");
      }
      OS::PrintErr(")");
    }

    String method_name = home->method()->selector();
    OS::PrintErr(" ");
    PrintStringError(method_name);
    OS::PrintErr("\n");

    act = act->sender();
  }
}


#if defined(ARCH_IS_32_BIT)
static uintptr_t kFNVPrime = 16777619;
#elif defined(ARCH_IS_64_BIT)
static uintptr_t kFNVPrime = 1099511628211;
#endif


SmallInteger String::EnsureHash(Isolate* isolate) {
  if (header_hash() == 0) {
    // FNV-1a hash
    intptr_t length = Size();
    uintptr_t h = length + 1;
    for (intptr_t i = 0; i < length; i++) {
      h = h ^ element(i);
      h = h * kFNVPrime;
    }
    h = h ^ isolate->salt();
    h = h & SmallInteger::kMaxValue;
    if (h == 0) {
      h = 1;
    }
    set_header_hash(h);
  }
  return SmallInteger::New(header_hash());
}

}  // namespace psoup
