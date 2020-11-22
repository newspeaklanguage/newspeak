// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "interpreter.h"

#include "heap.h"
#include "isolate.h"
#include "math-vm.h"
#include "os.h"
#include "primitives.h"


#define H heap_
#define nil nil_

namespace psoup {

// Frame layout:
//
// | ...                       | (high addresses / stack base)
// | message receiver          |
// | argument 1                |
// | ...                       |
// | argument N                |
// | ------------------------- |
// | saved IP / base sender    |
// | saved FP / 0              |  <= fp
// | flags                     |
// | method                    |
// | activation / 0            |
// | method receiver           |
// | temporary 1               |
// | ...                       |
// | temporary N               |  <= sp
// | ...                       | (low addresses / stack limit)
//
// Note the message receiver is different from the method receiver in the case
// of closure activations. The message receiver is the closure, and the method
// receiver is the receiver of the closure's home activation (i.e., the binding
// of `self`).
//
// With saved FPs and frame flags being SmallIntegers, the only GC-unsafe values
// on the stack are the saved IPs. Before GC, we swap the saved IPs with BCIs,
// and after GC we swap back. This allows the GC to simply visit the whole
// stack, and also accounts for bytecode arrays moving during GC.

static intptr_t FlagsNumArgs(SmallInteger flags) {
  return flags->value() >> 1;
}
static bool FlagsIsClosure(SmallInteger flags) {
  return (flags->value() & 1) != 0;
}
static SmallInteger MakeFlags(intptr_t num_args, bool is_closure) {
  return SmallInteger::New((num_args << 1) | (is_closure ? 1 : 0));
}

static const uint8_t* FrameSavedIP(Object* fp) {
  return reinterpret_cast<const uint8_t*>(static_cast<uword>(fp[1]));
}
static const uint8_t** FrameSavedIPSlot(Object* fp) {
  return reinterpret_cast<const uint8_t**>((uword)&fp[1]);
}

static Object* FrameSavedFP(Object* fp) {
  return reinterpret_cast<Object*>(static_cast<uword>(fp[0]));
}

static SmallInteger FrameFlags(Object* fp) {
  return static_cast<SmallInteger>(fp[-1]);
}

static Method FrameMethod(Object* fp) { return static_cast<Method>(fp[-2]); }

static Activation FrameActivation(Object* fp) {
  return static_cast<Activation>(fp[-3]);
}
static void FrameActivationPut(Object* fp, Activation activation) {
  fp[-3] = activation;
}

static Object FrameReceiver(Object* fp) { return fp[-4]; }

static Object FrameParameter(Object* fp, intptr_t index) {
  ASSERT(index <= FlagsNumArgs(FrameFlags(fp)));
  return fp[1 + index];
}
static Object FrameLocal(Object* fp, intptr_t index) {
  return fp[-5 - index];
}
static void FrameLocalPut(Object* fp, intptr_t index, Object value) {
  fp[-5 - index] = value;
}

static Object FrameTemp(Object* fp, intptr_t index) {
  intptr_t num_args = FlagsNumArgs(FrameFlags(fp));
  if (index < num_args) {
    return fp[1 + num_args - index];
  } else {
    return fp[-5 - (index - num_args)];
  }
}
static void FrameTempPut(Object* fp, intptr_t index, Object value) {
  intptr_t num_args = FlagsNumArgs(FrameFlags(fp));
  if (index < num_args) {
    FATAL("Assignment to parameter");
  } else {
    fp[-5 - (index - num_args)] = value;
  }
}

static Object* FrameSavedSP(Object* fp) {
  intptr_t num_args = FlagsNumArgs(FrameFlags(fp));
  return fp + 3 + num_args;
}

static intptr_t FrameNumLocals(Object* fp, Object* sp) {
  return &fp[-4] - sp;
}

static Activation FrameBaseSender(Object* fp) {
  ASSERT(FrameSavedFP(fp) == 0);
  return static_cast<Activation>(fp[1]);
}

Interpreter::Interpreter(Heap* heap, Isolate* isolate) :
    ip_(nullptr),
    sp_(nullptr),
    fp_(nullptr),
    stack_base_(nullptr),
    stack_limit_(nullptr),
    nil_(nullptr),
    false_(nullptr),
    true_(nullptr),
    object_store_(nullptr),
    heap_(heap),
    isolate_(isolate),
    environment_(nullptr) {
  heap->InitializeInterpreter(this);

  stack_limit_ = reinterpret_cast<Object*>(malloc(kStackSize));
  stack_base_ = stack_limit_ + kStackSlots;
  sp_ = stack_base_;
  checked_stack_limit_ =
      stack_limit_ + (sizeof(Activation::Layout) / sizeof(Object));

#if defined(DEBUG)
  for (intptr_t i = 0; i < kStackSlots; i++) {
    stack_limit_[i] = static_cast<Object>(kUninitializedWord);
  }
#endif
}

Interpreter::~Interpreter() {
  free(stack_limit_);
}

void Interpreter::PushIndirectLocal(intptr_t vector_offset, intptr_t offset) {
  Object vector = FrameLocal(fp_, vector_offset);
  ASSERT(vector->IsArray());
  Object temp = static_cast<Array>(vector)->element(offset);
  Push(temp);
}

void Interpreter::PopIntoIndirectLocal(intptr_t vector_offset,
                                       intptr_t offset) {
  Object top = Pop();
  Object vector = FrameLocal(fp_, vector_offset);
  ASSERT(vector->IsArray());
  static_cast<Array>(vector)->set_element(offset, top);
}

void Interpreter::StoreIntoIndirectLocal(intptr_t vector_offset,
                                         intptr_t offset) {
  Object top = Stack(0);
  Object vector = FrameLocal(fp_, vector_offset);
  ASSERT(vector->IsArray());
  static_cast<Array>(vector)->set_element(offset, top);
}

void Interpreter::PushLiteral(intptr_t offset) {
  Array literals = FrameMethod(fp_)->literals();;
  ASSERT((offset >= 0) && (offset < literals->Size()));
  Push(literals->element(offset));
}

void Interpreter::PushEnclosingObject(intptr_t depth) {
  ASSERT(depth > 0);  // Compiler should have used push receiver.

  Object enclosing_object = FrameReceiver(fp_);
  AbstractMixin target_mixin = FrameMethod(fp_)->mixin();
  intptr_t count = 0;
  while (count < depth) {
    count++;
    Behavior mixin_app = FindApplicationOf(target_mixin,
                                            enclosing_object->Klass(H));
    enclosing_object = mixin_app->enclosing_object();
    target_mixin = target_mixin->enclosing_mixin();
  }
  Push(enclosing_object);
}

void Interpreter::PushNewArrayWithElements(intptr_t size) {
  Array result = H->AllocateArray(size);  // SAFEPOINT
  for (intptr_t i = 0; i < size; i++) {
    Object e = Stack(size - i - 1);
    result->set_element(i, e);
  }
  PopNAndPush(size, result);
}

void Interpreter::PushNewArray(intptr_t size) {
  Array result = H->AllocateArray(size);  // SAFEPOINT
  for (intptr_t i = 0; i < size; i++) {
    result->set_element(i, nil, kNoBarrier);
  }
  Push(result);
}

void Interpreter::PushClosure(intptr_t num_copied,
                              intptr_t num_args,
                              intptr_t block_size) {
  EnsureActivation(fp_);  // SAFEPOINT

  Closure result = H->AllocateClosure(num_copied);  // SAFEPOINT
  result->set_defining_activation(FrameActivation(fp_));
  result->set_initial_bci(FrameMethod(fp_)->BCI(ip_));
  result->set_num_args(SmallInteger::New(num_args));
  for (intptr_t i = 0; i < num_copied; i++) {
    Object e = Stack(num_copied - i - 1);
    result->set_copied(i, e);
  }

  ip_ += block_size;
  PopNAndPush(num_copied, result);
}

void Interpreter::Perform(String selector, intptr_t num_args) {
  OrdinarySend(selector, num_args);  // SAFEPOINT
}

void Interpreter::CommonSend(intptr_t offset) {
  Array common_selectors = object_store()->common_selectors();
  String selector =
      static_cast<String>(common_selectors->element(offset * 2));
  ASSERT(selector->IsString());
  ASSERT(selector->is_canonical());
  SmallInteger arity =
      static_cast<SmallInteger>(common_selectors->element(offset * 2 + 1));
  ASSERT(arity->IsSmallInteger());
  OrdinarySend(selector, arity->value());  // SAFEPOINT
}

Method Interpreter::MethodAt(Behavior cls, String selector) {
  ASSERT(selector->IsString());
  ASSERT(selector->is_canonical());
  Array methods = cls->methods();
  ASSERT(methods->IsArray());
  intptr_t length = methods->Size();
  for (intptr_t i = 0; i < length; i++) {
    Method method = static_cast<Method>(methods->element(i));
    ASSERT(method->selector()->IsString());
    ASSERT(method->selector()->is_canonical());
    if (method->selector() == selector) {
      return method;
    }
  }
  return static_cast<Method>(nil);
}

bool Interpreter::HasMethod(Behavior cls, String selector) {
  return MethodAt(cls, selector) != nil;
}

void Interpreter::OrdinarySend(intptr_t selector_index,
                               intptr_t num_args) {
  String selector = SelectorAt(selector_index);
  OrdinarySend(selector, num_args);  // SAFEPOINT
}

void Interpreter::OrdinarySend(String selector,
                               intptr_t num_args) {
#if LOOKUP_CACHE
  Object receiver = Stack(num_args);
  Method target;
  if (lookup_cache_.LookupOrdinary(receiver->ClassId(), selector, &target)) {
    Activate(target, num_args);  // SAFEPOINT
    return;
  }
#endif

  OrdinarySendMiss(selector, num_args);  // SAFEPOINT
}

void Interpreter::OrdinarySendMiss(String selector,
                                   intptr_t num_args) {
  Object receiver = Stack(num_args);
  Behavior receiver_class = receiver->Klass(H);
  Behavior lookup_class = receiver_class;
  while (lookup_class != nil) {
    Method method = MethodAt(lookup_class, selector);
    if (method != nil) {
      if (method->IsPublic()) {
#if LOOKUP_CACHE
        lookup_cache_.InsertOrdinary(receiver->ClassId(), selector, method);
#endif
        Activate(method, num_args);  // SAFEPOINT
        return;
      } else if (method->IsProtected()) {
        bool present_receiver = true;
        DNUSend(selector, num_args, receiver,
                receiver_class, present_receiver);  // SAFEPOINT
        return;
      }
    }
    lookup_class = lookup_class->superclass();
  }
  bool present_receiver = true;
  DNUSend(selector, num_args, receiver,
          receiver_class, present_receiver);  // SAFEPOINT
}

Behavior Interpreter::FindApplicationOf(AbstractMixin mixin,
                                        Behavior klass) {
  while (klass->mixin() != mixin) {
    klass = klass->superclass();
    if (klass == nil) {
      FATAL("Cannot find mixin application");
    }
  }
  return klass;
}

void Interpreter::SuperSend(intptr_t selector_index,
                            intptr_t num_args) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             kSuper,
                             &absent_receiver,
                             &target)) {
    ASSERT(absent_receiver == nullptr);
    absent_receiver = receiver;
    ActivateAbsent(target, receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  SuperSendMiss(selector, num_args);  // SAFEPOINT
}

void Interpreter::SuperSendMiss(String selector,
                                intptr_t num_args) {
  Object receiver = FrameReceiver(fp_);
  AbstractMixin method_mixin = FrameMethod(fp_)->mixin();
  Behavior receiver_class = receiver->Klass(H);
  Behavior method_mixin_app = FindApplicationOf(method_mixin,
                                                 receiver_class);
  ProtectedSend(selector,
                num_args,
                receiver,
                method_mixin_app->superclass(),
                kSuper);  // SAFEPOINT
}

void Interpreter::ImplicitReceiverSend(intptr_t selector_index,
                                       intptr_t num_args) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object method_receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(method_receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             kImplicitReceiver,
                             &absent_receiver,
                             &target)) {
    if (absent_receiver == nullptr) {
      absent_receiver = method_receiver;
    }
    ActivateAbsent(target, absent_receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  return ImplicitReceiverSendMiss(selector, num_args);  // SAFEPOINT
}

void Interpreter::ImplicitReceiverSendMiss(String selector,
                                           intptr_t num_args) {
  Object method_receiver = FrameReceiver(fp_);

  Object candidate_receiver = method_receiver;
  AbstractMixin candidate_mixin = FrameMethod(fp_)->mixin();

  for (;;) {
    Behavior candidateMixinApplication =
        FindApplicationOf(candidate_mixin,
                          candidate_receiver->Klass(H));
    if (HasMethod(candidateMixinApplication, selector)) {
      LexicalSend(selector,
                  num_args,
                  candidate_receiver,
                  candidate_mixin,
                  kImplicitReceiver);  // SAFEPOINT
      return;
    }
    candidate_mixin = candidate_mixin->enclosing_mixin();
    if (candidate_mixin == nil) break;
    candidate_receiver = candidateMixinApplication->enclosing_object();
  }
  ProtectedSend(selector,
                num_args,
                method_receiver,
                method_receiver->Klass(H),
                kImplicitReceiver);  // SAFEPOINT
}

void Interpreter::OuterSend(intptr_t selector_index,
                            intptr_t num_args,
                            intptr_t depth) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             depth,
                             &absent_receiver,
                             &target)) {
    ASSERT(absent_receiver != nullptr);
    ActivateAbsent(target, absent_receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  OuterSendMiss(selector, num_args, depth);  // SAFEPOINT
}

void Interpreter::OuterSendMiss(String selector,
                                intptr_t num_args,
                                intptr_t depth) {
  Object receiver = FrameReceiver(fp_);
  AbstractMixin target_mixin = FrameMethod(fp_)->mixin();
  intptr_t count = 0;
  while (count < depth) {
    count++;
    Behavior mixin_app = FindApplicationOf(target_mixin,
                                            receiver->Klass(H));
    receiver = mixin_app->enclosing_object();
    target_mixin = target_mixin->enclosing_mixin();
  }
  LexicalSend(selector, num_args, receiver, target_mixin, depth);  // SAFEPOINT
}

void Interpreter::SelfSend(intptr_t selector_index,
                           intptr_t num_args) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             kSelf,
                             &absent_receiver,
                             &target)) {
    ASSERT(absent_receiver == nullptr);
    ActivateAbsent(target, receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  SelfSendMiss(selector, num_args);  // SAFEPOINT
}

void Interpreter::SelfSendMiss(String selector,
                               intptr_t num_args) {
  Object receiver = FrameReceiver(fp_);
  AbstractMixin method_mixin = FrameMethod(fp_)->mixin();
  LexicalSend(selector, num_args, receiver, method_mixin, kSelf);  // SAFEPOINT
}

void Interpreter::LexicalSend(String selector,
                              intptr_t num_args,
                              Object receiver,
                              AbstractMixin mixin,
                              intptr_t rule) {
  Behavior receiver_class = receiver->Klass(H);
  Behavior mixin_application = FindApplicationOf(mixin, receiver_class);
  Method method = MethodAt(mixin_application, selector);
  if (method != nil && method->IsPrivate()) {
#if LOOKUP_CACHE
    Object method_receiver = FrameReceiver(fp_);
    lookup_cache_.InsertNS(method_receiver->ClassId(),
                           selector,
                           FrameMethod(fp_),
                           rule,
                           receiver == method_receiver ? Object() : receiver,
                           method);
#endif
    ActivateAbsent(method, receiver, num_args);  // SAFEPOINT
    return;
  }
  ProtectedSend(selector, num_args, receiver,
                receiver_class, rule);  // SAFEPOINT
}

void Interpreter::ProtectedSend(String selector,
                                intptr_t num_args,
                                Object receiver,
                                Behavior mixin_application,
                                intptr_t rule) {
  Behavior lookup_class = mixin_application;
  while (lookup_class != nil) {
    Method method = MethodAt(lookup_class, selector);
    if (method != nil && !method->IsPrivate()) {
#if LOOKUP_CACHE
      Object method_receiver = FrameReceiver(fp_);
      lookup_cache_.InsertNS(method_receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             rule,
                             receiver == method_receiver ? Object() : receiver,
                             method);
#endif
      ActivateAbsent(method, receiver, num_args);  // SAFEPOINT
      return;
    }
    lookup_class = lookup_class->superclass();
  }
  bool present_receiver = false;
  DNUSend(selector, num_args, receiver, mixin_application,
          present_receiver);  // SAFEPOINT
}

void Interpreter::DNUSend(String selector,
                          intptr_t num_args,
                          Object receiver,
                          Behavior lookup_class,
                          bool present_receiver) {
  if (TRACE_DNU) {
    char* c1 = receiver->ToCString(H);
    char* c2 = selector->ToCString(H);
    char* c3 = FrameMethod(fp_)->selector()->ToCString(H);
    OS::PrintErr("DNU %s %s from %s\n", c1, c2, c3);
    free(c1);
    free(c2);
    free(c3);
  }

  Behavior cls = lookup_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->does_not_understand());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Recursive #doesNotUnderstand:");
  }

  Array arguments;
  {
    HandleScope h1(H, reinterpret_cast<Object*>(&selector));
    HandleScope h2(H, &receiver);
    HandleScope h3(H, reinterpret_cast<Object*>(&method));
    arguments = H->AllocateArray(num_args);  // SAFEPOINT
  }
  for (intptr_t i = 0; i < num_args; i++) {
    Object e = Stack(num_args - i - 1);
    arguments->set_element(i, e);
  }
  Message message;
  {
    HandleScope h1(H, reinterpret_cast<Object*>(&selector));
    HandleScope h2(H, &receiver);
    HandleScope h3(H, reinterpret_cast<Object*>(&method));
    HandleScope h4(H, reinterpret_cast<Object*>(&arguments));
    message = H->AllocateMessage();  // SAFEPOINT
  }

  message->set_selector(selector);
  message->set_arguments(arguments);

  Drop(num_args);
  if (!present_receiver) {
    Push(receiver);
  }
  Push(message);
  Activate(method, 1);  // SAFEPOINT
}

void Interpreter::SendCannotReturn(Object result) {
  if (TRACE_SPECIAL_CONTROL) {
    OS::PrintErr("#cannotReturn:\n");
  }

  Activation top;
  {
    HandleScope h1(H, &result);
    top = EnsureActivation(fp_);  // SAFEPOINT
  }

  Behavior receiver_class = top->Klass(H);
  Behavior cls = receiver_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->cannot_return());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Missing #cannotReturn:");
  }

  Push(top);
  Push(result);
  Activate(method, 1);  // SAFEPOINT
}

void Interpreter::SendAboutToReturnThrough(Object result,
                                           Activation unwind) {
  if (TRACE_SPECIAL_CONTROL) {
    OS::PrintErr("#aboutToReturn:through:\n");
  }

  Activation top;
  {
    HandleScope h1(H, &result);
    HandleScope h2(H, reinterpret_cast<Object*>(&unwind));
    top = EnsureActivation(fp_);  // SAFEPOINT
  }

  Behavior receiver_class = top->Klass(H);
  Behavior cls = receiver_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->about_to_return_through());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Missing #aboutToReturn:through:");
  }

  Push(top);
  Push(result);
  Push(unwind);
  Activate(method, 2);  // SAFEPOINT
}

void Interpreter::SendNonBooleanReceiver(Object non_boolean) {
  // Note that Squeak instead sends #mustBeBoolean to the non-boolean.
  if (TRACE_SPECIAL_CONTROL) {
    OS::PrintErr("#nonBooleanReceiver:\n");
  }

  Activation top;
  {
    HandleScope h1(H, &non_boolean);
    top = EnsureActivation(fp_);  // SAFEPOINT
  }

  Behavior receiver_class = top->Klass(H);
  Behavior cls = receiver_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->non_boolean_receiver());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Missing #nonBooleanReceiver:");
  }

  Push(top);
  Push(non_boolean);
  Activate(method, 1);  // SAFEPOINT
}

void Interpreter::InsertAbsentReceiver(Object receiver, intptr_t num_args) {
  ASSERT(num_args >= 0);
  ASSERT(num_args < 255);

  ASSERT(StackDepth() >= num_args);
  Grow(1);
  for (intptr_t i = 0; i < num_args; i++) {
    StackPut(i, Stack(i + 1));
  }
  StackPut(num_args, receiver);
}

void Interpreter::ActivateAbsent(Method method,
                                 Object receiver,
                                 intptr_t num_args) {
  InsertAbsentReceiver(receiver, num_args);
  Activate(method, num_args);  // SAFEPOINT
}

void Interpreter::Activate(Method method, intptr_t num_args) {
  ASSERT(num_args == method->NumArgs());

  intptr_t prim = method->Primitive();
  if (prim != 0) {
    if (TRACE_PRIMITIVES) {
      OS::PrintErr("Primitive %" Pd "\n", prim);
    }
    if ((prim & 256) != 0) {
      // Getter
      intptr_t offset = prim & 255;
      ASSERT(num_args == 0);
      Object receiver = Stack(0);
      ASSERT(receiver->IsRegularObject() || receiver->IsEphemeron());
      Object value = static_cast<RegularObject>(receiver)->slot(offset);
      PopNAndPush(1, value);
      return;
    } else if ((prim & 512) != 0) {
      // Setter
      intptr_t offset = prim & 255;
      ASSERT(num_args == 1);
      Object receiver = Stack(1);
      Object value = Stack(0);
      ASSERT(receiver->IsRegularObject() || receiver->IsEphemeron());
      static_cast<RegularObject>(receiver)->set_slot(offset, value);
      PopNAndPush(2, receiver);
      return;
    } else {
      HandleScope h1(H, reinterpret_cast<Object*>(&method));
      if (Primitives::Invoke(prim, num_args, H, this)) {  // SAFEPOINT
        ASSERT(StackDepth() >= 0);
        return;
      }
    }
  }

  // Create frame.
  Object receiver = Stack(num_args);
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(ip_)));
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(fp_)));
  fp_ = sp_;
  Push(MakeFlags(num_args, false));
  Push(method);
  Push(Object(static_cast<uword>(0)));  // Activation.
  Push(receiver);

  ip_ = method->IP(SmallInteger::New(1));
  intptr_t num_temps = method->NumTemps();
  for (intptr_t i = num_args; i < num_temps; i++) {
    Push(nil);
  }

  if (sp_ < checked_stack_limit_) {
    StackOverflow();
  }
}

void Interpreter::ActivateClosure(intptr_t num_args) {
  Closure closure = static_cast<Closure>(Stack(num_args));
  ASSERT(closure->IsClosure());
  ASSERT(closure->num_args() == SmallInteger::New(num_args));

  Activation home = closure->defining_activation();

  // Create frame.
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(ip_)));
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(fp_)));
  fp_ = sp_;
  Push(MakeFlags(num_args, true));
  Push(home->method());
  Push(Object(static_cast<uword>(0)));  // Activation.
  Push(home->receiver());

  ip_ = home->method()->IP(closure->initial_bci());

  intptr_t num_copied = closure->NumCopied();
  for (intptr_t i = 0; i < num_copied; i++) {
    Push(closure->copied(i));
  }

  // Temps allocated by bytecodes

  if (sp_ < checked_stack_limit_) {
    StackOverflow();
  }
}

void Interpreter::CreateBaseFrame(Activation activation) {
  ASSERT(activation->IsActivation());
  ASSERT(activation->bci()->IsSmallInteger());

  ASSERT(ip_ == 0);
  ASSERT(sp_ == stack_base_);
  ASSERT(fp_ == 0);

  bool is_closure;
  intptr_t num_args;
  if (activation->closure() == nil) {
    is_closure = false;
    num_args = activation->method()->NumArgs();
    Push(activation->receiver());  // Message receiver.
  } else {
    Closure closure = activation->closure();
    ASSERT(closure->IsClosure());
    is_closure = true;
    num_args = closure->num_args()->value();
    Push(closure);                // Message receiver.
  }
  for (intptr_t i = 0; i < num_args; i++) {
    Push(activation->temp(i));
  }

  ASSERT(!activation->sender()->IsSmallInteger());

  // Create frame.
  Push(activation->sender());           // Base sender.
  Push(Object(static_cast<uword>(0)));  // Saved FP.
  fp_ = sp_;
  Push(MakeFlags(num_args, is_closure));
  Push(activation->method());
  Push(activation);
  Push(activation->receiver());

  intptr_t num_temps = activation->StackDepth();
  for (intptr_t i = num_args; i < num_temps; i++) {
    Push(activation->temp(i));
  }
  // Drop temps. We don't update the activation as we store into the frame, so
  // the stale references in the activation may create leaks.
  activation->set_stack_depth(SmallInteger::New(num_args));

  ip_ = activation->method()->IP(activation->bci());

  ASSERT(FrameBaseSender(fp_) == activation->sender());
  activation->set_sender_fp(fp_);
  ASSERT(FrameSavedFP(fp_) == 0);
  ASSERT(FrameMethod(fp_) == activation->method());
  ASSERT(FrameActivation(fp_) == activation);
  ASSERT(FrameReceiver(fp_) == activation->receiver());
}

void Interpreter::StackOverflow() {
  if (checked_stack_limit_ == reinterpret_cast<Object*>(-1)) {
    // Interrupt.
    isolate_->PrintStack();
    Exit();
  }

  // True overflow: reclaim stack space by moving all frames except the top
  // frame to the heap.
  CreateBaseFrame(FlushAllFrames());  // SAFEPOINT
}

String Interpreter::SelectorAt(intptr_t index) {
  Array literals = FrameMethod(fp_)->literals();
  ASSERT((index >= 0) && (index < literals->Size()));
  Object selector = literals->element(index);
  ASSERT(selector->IsString());
  ASSERT(static_cast<String>(selector)->is_canonical());
  return static_cast<String>(selector);
}

void Interpreter::LocalReturn(Object result) {
  Object* saved_fp = FrameSavedFP(fp_);
  if (saved_fp == 0) {
    LocalBaseReturn(result);  // SAFEPOINT
    return;
  }

  ip_ = FrameSavedIP(fp_);
  sp_ = FrameSavedSP(fp_);
  fp_ = saved_fp;
  Push(result);
}

void Interpreter::LocalBaseReturn(Object result) {
  // Returning from the base frame.
  Activation top;
  {
    HandleScope h(H, reinterpret_cast<Object*>(&result));
    top = FlushAllFrames();  // SAFEPOINT
  }

  Activation sender = top->sender();
  if (!sender->IsActivation() ||
      !sender->bci()->IsSmallInteger()) {
    CreateBaseFrame(top);
    SendCannotReturn(result);  // SAFEPOINT
    return;
  }

  top->set_sender(static_cast<Activation>(nil), kNoBarrier);
  top->set_bci(static_cast<SmallInteger>(nil));

  CreateBaseFrame(sender);
  Push(result);
}

void Interpreter::NonLocalReturn(Object result) {
  // Search the static chain for the enclosing method activation.
  ASSERT(FlagsIsClosure(FrameFlags(fp_)));
  Closure c = static_cast<Closure>(FrameTemp(fp_, -1));
  ASSERT(c->IsClosure());
  Activation home = c->defining_activation();
  ASSERT(home->IsActivation());
  c = home->closure();
  while (c != nil) {
    home = c->defining_activation();
    ASSERT(home->IsActivation());
    c = home->closure();
  }

  for (Object* fp = FrameSavedFP(fp_); fp != 0; fp = FrameSavedFP(fp)) {
    if (FrameActivation(fp) == home) {
      if (FrameSavedFP(fp) == 0) {
        break;  // Return crosses base frame.
      }

      // Note this implicitly zaps every activation on the dynamic chain.
      ip_ = FrameSavedIP(fp);
      sp_ = FrameSavedSP(fp);
      fp_ = FrameSavedFP(fp);
      Push(result);
      return;
    }

    intptr_t prim = FrameMethod(fp)->Primitive();
    if (Primitives::IsUnwindProtect(prim)) {
      break;
    }
    if (Primitives::IsSimulationRoot(prim)) {
      break;
    }
  }

  // A more complicated case: crossing the base frame, #cannotReturn:, or
  // #aboutToReturn:to:. These cares are very rare, so we simply flush to
  // activations instead of dealing with a mixture of frames and activations.

  Activation top;
  {
    HandleScope h1(H, reinterpret_cast<Object*>(&home));
    HandleScope h2(H, reinterpret_cast<Object*>(&result));
    top = FlushAllFrames();  // SAFEPOINT
  }

  // Search the dynamic chain for a dead activation or an unwind-protect
  // activation that would block the return.
  for (Activation unwind = top->sender();
       unwind != home;
       unwind = unwind->sender()) {
    if (!unwind->IsActivation()) {
      ASSERT(unwind == nil);
      CreateBaseFrame(top);
      SendCannotReturn(result);  // SAFEPOINT
      return;
    }

    intptr_t prim = unwind->method()->Primitive();
    if (Primitives::IsUnwindProtect(prim)) {
      CreateBaseFrame(top);
      SendAboutToReturnThrough(result, unwind);  // SAFEPOINT
      return;
    }
    if (Primitives::IsSimulationRoot(prim)) {
      CreateBaseFrame(top);
      SendCannotReturn(result);  // SAFEPOINT
      return;
    }
  }

  Activation sender = home->sender();
  if (!sender->IsActivation() ||
      !sender->bci()->IsSmallInteger()) {
    CreateBaseFrame(top);
    SendCannotReturn(result);  // SAFEPOINT
    return;
  }

  // Mark activations on the dynamic chain up to the return target as dead.
  // Note this follows the behavior of Squeak instead of the blue book, which
  // only zaps A.
  Activation zap = top;
  do {
    Activation next = zap->sender();
    zap->set_sender(static_cast<Activation>(nil), kNoBarrier);
    zap->set_bci(static_cast<SmallInteger>(nil));
    zap = next;
  } while (zap != sender);

  CreateBaseFrame(sender);
  Push(result);
}

void Interpreter::Enter() {
  intptr_t saved_handles = H->handles();
  jmp_buf* saved_environment = environment_;

  jmp_buf environment;
  environment_ = &environment;

  if (setjmp(environment) == 0) {
    Interpret();
    UNREACHABLE();
  }

  environment_ = saved_environment;
  H->set_handles(saved_handles);
}

void Interpreter::Exit() {
  ASSERT(environment_ != NULL);
  longjmp(*environment_, 1);
}

void Interpreter::ActivateDispatch(Method method, intptr_t num_args) {
  ASSERT(method->Primitive() == 0);
  Interpreter::Activate(method, num_args);
}

void Interpreter::ReturnFromDispatch() {
  Object* saved_fp = FrameSavedFP(fp_);
  if (saved_fp == 0) {
    // Base frame.
    Activation sender = FrameBaseSender(fp_);
    if (sender != nil) {
      ip_ = 0;
      sp_ = FrameSavedSP(fp_);
      fp_ = saved_fp;
      CreateBaseFrame(sender);
      return;
    }
  }

  ip_ = FrameSavedIP(fp_);
  sp_ = FrameSavedSP(fp_);
  fp_ = saved_fp;
}

void Interpreter::PrintStack() {
  Activation top = FlushAllFrames();  // SAFEPOINT
  top->PrintStack(H);
  CreateBaseFrame(top);
}

void Interpreter::Interpret() {
  for (;;) {
    ASSERT(ip_ != 0);
    ASSERT(sp_ != 0);
    ASSERT(fp_ != 0);

    uint8_t byte1 = *ip_++;
    switch (byte1) {
    case 0: case 1: case 2: case 3: case 4: case 5: case 6: case 7:
    case 8: case 9: case 10: case 11: case 12: case 13: case 14: case 15:
      ip_ -= (byte1 & 15);
      break;
    case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 23:
    case 24: case 25: case 26: case 27: case 28: case 29: case 30: case 31:
      ip_ += (byte1 & 15);
      break;
    case 32: case 33: case 34: case 35: case 36: case 37: case 38: case 39:
    case 40: case 41: case 42: case 43: case 44: case 45: case 46: case 47: {
      Object top = Pop();
      if (top == true_) {
        ip_ += (byte1 & 15);
      } else if (top != false_) {
        SendNonBooleanReceiver(top);
      }
      break;
    }
    case 48: case 49: case 50: case 51: case 52: case 53: case 54: case 55:
    case 56: case 57: case 58: case 59: case 60: case 61: case 62: case 63: {
      Object top = Pop();
      if (top == false_) {
        ip_ += (byte1 & 15);
      } else if (top != true_) {
        SendNonBooleanReceiver(top);
      }
      break;
    }
    case 64: case 65: case 66: case 67:
    case 68: case 69: case 70: case 71:
    case 72: case 73: case 74: case 75:
    case 76: case 77: case 78: case 79:
      OrdinarySend(byte1 & 7, (byte1 >> 3) & 1);
      break;
    case 80: case 81: case 82: case 83:
    case 84: case 85: case 86: case 87:
    case 88: case 89: case 90: case 91:
    case 92: case 93: case 94: case 95:
      SelfSend(byte1 & 7, (byte1 >> 3) & 1);
      break;
    case 96: case 97: case 98: case 99:
    case 100: case 101: case 102: case 103:
    case 104: case 105: case 106: case 107:
    case 108: case 109: case 110: case 111:
      ImplicitReceiverSend(byte1 & 7, (byte1 >> 3) & 1);
      break;
    case 112: case 113: case 114: case 115:
    case 116: case 117: case 118: case 119:
      Push(FrameParameter(fp_, byte1 & 7));
      break;
    case 120: case 121: case 122: case 123:
    case 124: case 125: case 126: case 127:
      Push(FrameLocal(fp_, byte1 & 7));
      break;
    case 128: case 129: case 130: case 131:
    case 132: case 133: case 134: case 135:
      FrameLocalPut(fp_, byte1 & 7, Pop());
      break;
    case 136: case 137: case 138: case 139:
    case 140: case 141: case 142: case 143:
      FrameLocalPut(fp_, byte1 & 7, Stack(0));
      break;
    case 144: case 145: case 146: case 147:
    case 148: case 149: case 150: case 151:
      PushLiteral(byte1 & 7);
      break;
    case 152: Push(nil_); break;
    case 153: Push(false_); break;
    case 154: Push(true_); break;
    case 155: Push(FrameReceiver(fp_)); break;
    case 156: Push(FrameMethod(fp_)->mixin()); break;
    case 157: Push(object_store()->message_loop()); break;
    case 158: Pop(); break;
    case 159: Push(Stack(0)); break;
    case 160: Push(SmallInteger::New(-1)); break;
    case 161: Push(SmallInteger::New(0)); break;
    case 162: Push(SmallInteger::New(1)); break;
    case 163: Push(SmallInteger::New(2)); break;
    case 166: LocalReturn(nil_); break;
    case 167: LocalReturn(false_); break;
    case 168: LocalReturn(true_); break;
    case 169: LocalReturn(FrameReceiver(fp_)); break;
    case 170: LocalReturn(Pop()); break;
    case 171: NonLocalReturn(nil_); break;
    case 172: NonLocalReturn(false_); break;
    case 173: NonLocalReturn(true_); break;
    case 174: NonLocalReturn(FrameReceiver(fp_)); break;
    case 175: NonLocalReturn(Pop()); break;
#if STATIC_PREDICTION_BYTECODES
    case 176: {
      // +
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        intptr_t raw_left = static_cast<SmallInteger>(left)->value();
        intptr_t raw_right = static_cast<SmallInteger>(right)->value();
        intptr_t raw_result = raw_left + raw_right;
        if (SmallInteger::IsSmiValue(raw_result)) {
          PopNAndPush(2, SmallInteger::New(raw_result));
          break;
        }
      }
      goto CommonSendDispatch;
    }
    case 177: {
      // -
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        intptr_t raw_left = static_cast<SmallInteger>(left)->value();
        intptr_t raw_right = static_cast<SmallInteger>(right)->value();
        intptr_t raw_result = raw_left - raw_right;
        if (SmallInteger::IsSmiValue(raw_result)) {
          PopNAndPush(2, SmallInteger::New(raw_result));
          break;
        }
      }
      goto CommonSendDispatch;
    }
    case 178: {
      // *
      goto CommonSendDispatch;
    }
    case 179: {
      // //
      goto CommonSendDispatch;
    }
    case 180: {
      /* \\ */
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        intptr_t raw_left = static_cast<SmallInteger>(left)->value();
        intptr_t raw_right = static_cast<SmallInteger>(right)->value();
        if (raw_right != 0) {
          intptr_t raw_result = Math::FloorMod(raw_left, raw_right);
          ASSERT(SmallInteger::IsSmiValue(raw_result));
          PopNAndPush(2, SmallInteger::New(raw_result));
          break;
        }
      }
      goto CommonSendDispatch;
    }
    case 181: {
      // <<
      goto CommonSendDispatch;
    }
    case 182: {
      // >>
      goto CommonSendDispatch;
    }
    case 183: {
      // &
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        PopNAndPush(2, static_cast<SmallInteger>(
            static_cast<intptr_t>(left) & static_cast<intptr_t>(right)));
        break;
      }
      goto CommonSendDispatch;
    }
    case 184: {
      // |
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        PopNAndPush(2, static_cast<SmallInteger>(
            static_cast<intptr_t>(left) | static_cast<intptr_t>(right)));
        break;
      }
      goto CommonSendDispatch;
    }
    case 185: {
      // <
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        if (static_cast<intptr_t>(left) < static_cast<intptr_t>(right)) {
          PopNAndPush(2, true_);
        } else {
          PopNAndPush(2, false_);
        }
        break;
      }
      goto CommonSendDispatch;
    }
    case 186: {
      // >
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        if (static_cast<intptr_t>(left) > static_cast<intptr_t>(right)) {
          PopNAndPush(2, true_);
        } else {
          PopNAndPush(2, false_);
        }
        break;
      }
      goto CommonSendDispatch;
    }
    case 187: {
      // <=
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        if (static_cast<intptr_t>(left) <= static_cast<intptr_t>(right)) {
          PopNAndPush(2, true_);
        } else {
          PopNAndPush(2, false_);
        }
        break;
      }
      goto CommonSendDispatch;
    }
    case 188: {
      // >=
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        if (static_cast<intptr_t>(left) >= static_cast<intptr_t>(right)) {
          PopNAndPush(2, true_);
        } else {
          PopNAndPush(2, false_);
        }
        break;
      }
      goto CommonSendDispatch;
    }
    case 189: {
      // =
      Object left = Stack(1);
      Object right = Stack(0);
      if (left->IsSmallInteger() && right->IsSmallInteger()) {
        if (static_cast<intptr_t>(left) == static_cast<intptr_t>(right)) {
          PopNAndPush(2, true_);
        } else {
          PopNAndPush(2, false_);
        }
        break;
      }
      goto CommonSendDispatch;
    }
    case 190: {
      // new
      goto CommonSendDispatch;
    }
    case 191: {
      // new:
      goto CommonSendDispatch;
    }
    case 192: {
      // at:
      Object array = Stack(1);
      SmallInteger index = static_cast<SmallInteger>(Stack(0));
      if (index->IsSmallInteger()) {
        intptr_t raw_index = index->value() - 1;
        if (array->IsArray()) {
          if ((raw_index >= 0) &&
              (raw_index < static_cast<Array>(array)->Size())) {
            Object value = static_cast<Array>(array)->element(raw_index);
            PopNAndPush(2, value);
            break;
          }
        } else if (array->IsBytes()) {
          if ((raw_index >= 0) &&
              (raw_index < static_cast<Bytes>(array)->Size())) {
            uint8_t raw_value = static_cast<Bytes>(array)->element(raw_index);
            PopNAndPush(2, SmallInteger::New(raw_value));
            break;
          }
        }
      }
      goto CommonSendDispatch;
    }
    case 193: {
      // at:put:
      Object array = Stack(2);
      SmallInteger index = static_cast<SmallInteger>(Stack(1));
      if (index->IsSmallInteger()) {
        intptr_t raw_index = index->value() - 1;
        if (array->IsArray()) {
          if ((raw_index >= 0) &&
              (raw_index < static_cast<Array>(array)->Size())) {
            Object value = Stack(0);
            static_cast<Array>(array)->set_element(raw_index, value);
            PopNAndPush(3, value);
            break;
          }
        } else if (array->IsByteArray()) {
          SmallInteger value = static_cast<SmallInteger>(Stack(0));
          if ((raw_index >= 0) &&
              (raw_index < static_cast<ByteArray>(array)->Size()) &&
              static_cast<uword>(value) <= 255) {
            static_cast<ByteArray>(array)->set_element(raw_index,
                                                        value->value());
            PopNAndPush(3, value);
            break;
          }
        }
      }
      goto CommonSendDispatch;
    }
    case 194: {
      // size
      Object array = Stack(0);
      if (array->IsArray()) {
        PopNAndPush(1, static_cast<Array>(array)->size());
        break;
      } else if (array->IsBytes()) {
        PopNAndPush(1, static_cast<Bytes>(array)->size());
        break;
      }
      goto CommonSendDispatch;
    }
    case 195:
    case 196: case 197: case 198: case 199:
    case 200: case 201: case 202: case 203:
    case 204: case 205: case 206: case 207:
      CommonSendDispatch:
      CommonSend(byte1 - 176);
      break;
#else  // !STATIC_PREDICTION_BYTECODES
    case 176: case 177: case 178: case 179:
    case 180: case 181: case 182: case 183:
    case 184: case 185: case 186: case 187:
    case 188: case 189: case 190: case 191:
    case 192: case 193: case 194: case 195:
    case 196: case 197: case 198: case 199:
    case 200: case 201: case 202: case 203:
    case 204: case 205: case 206: case 207:
      CommonSend(byte1 - 176);
      break;
#endif  // STATIC_PREDICTION_BYTECODES
    case 222: {
      uint8_t byte2 = *ip_++;
      PushNewArray(byte2);
      break;
    }
    case 223: {
      uint8_t byte2 = *ip_++;
      PushNewArrayWithElements(byte2);
      break;
    }
    case 228: {
      uint8_t byte2 = *ip_++;
      Push(FrameParameter(fp_, byte2));
      break;
    }
    case 229: {
      uint8_t byte2 = *ip_++;
      ASSERT(byte2 < StackDepth());
      Push(FrameLocal(fp_, byte2));
      break;
    }
    case 230: {
      uint8_t byte2 = *ip_++;
      ASSERT(byte2 < StackDepth());
      FrameLocalPut(fp_, byte2, Pop());
      break;
    }
    case 231: {
      uint8_t byte2 = *ip_++;
      ASSERT(byte2 < StackDepth());
      FrameLocalPut(fp_, byte2, Stack(0));
      break;
    }
    case 233: {
      uint8_t byte2 = *ip_++;
      PushEnclosingObject(byte2);
      break;
    }
    case 240: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t delta = (byte3 << 8) | byte2;
      ip_ -= delta;
      break;
    }
    case 241: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t delta = (byte3 << 8) | byte2;
      ip_ += delta;
      break;
    }
    case 242: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t delta = (byte3 << 8) | byte2;
      Object top = Pop();
      if (top == true_) {
        ip_ += delta;
      } else if (top != false_) {
        SendNonBooleanReceiver(top);
      }
      break;
    }
    case 243: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t delta = (byte3 << 8) | byte2;
      Object top = Pop();
      if (top == false_) {
        ip_ += delta;
      } else if (top != true_) {
        SendNonBooleanReceiver(top);
      }
      break;
    }
    case 245: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      PushIndirectLocal(byte3, byte2);
      break;
    }
    case 246: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      PopIntoIndirectLocal(byte3, byte2);
      break;
    }
    case 247: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      StoreIntoIndirectLocal(byte3, byte2);
      break;
    }
    case 248: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      PushLiteral((byte3 << 8) | byte2);
      break;
    }
    case 249: {
      uint8_t byte2 = *ip_++;
      int8_t byte3 = *ip_++;
      Push(SmallInteger::New((byte3 << 8) | byte2));
      break;
    }
    case 250: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t num_args = byte3 >> 4;
      intptr_t selector_index = ((byte3 & 0xF) << 8) | byte2;
      OrdinarySend(selector_index, num_args);
      break;
    }
    case 251: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t num_args = byte3 >> 4;
      intptr_t selector_index = ((byte3 & 0xF) << 8) | byte2;
      SelfSend(selector_index, num_args);
      break;
    }
    case 252: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t num_args = byte3 >> 4;
      intptr_t selector_index = ((byte3 & 0xF) << 8) | byte2;
      SuperSend(selector_index, num_args);
      break;
    }
    case 253: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      intptr_t num_args = byte3 >> 4;
      intptr_t selector_index = ((byte3 & 0xF) << 8) | byte2;
      ImplicitReceiverSend(selector_index, num_args);
      break;
    }
    case 254: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      uint8_t byte4 = *ip_++;
      intptr_t num_args = byte3 >> 4;
      intptr_t selector_index = ((byte3 & 0xF) << 8) | byte2;
      intptr_t depth = byte4;
      OuterSend(selector_index, num_args, depth);
      break;
    }
    case 255: {
      uint8_t byte2 = *ip_++;
      uint8_t byte3 = *ip_++;
      uint8_t byte4 = *ip_++;
      intptr_t num_copied = byte2 >> 4;
      intptr_t num_args = byte2 & 7;
      intptr_t block_size = byte3 | (byte4 << 8);
      PushClosure(num_copied, num_args, block_size);
      break;
    }
    default:
      FATAL("Unused bytecode");
    }
  }
}

Activation Interpreter::EnsureActivation(Object* fp) {
  Activation activation = FrameActivation(fp);
  if (activation == nullptr) {
    activation = H->AllocateActivation();  // SAFEPOINT
    activation->set_sender_fp(fp);
    activation->set_bci(static_cast<SmallInteger>(nil));
    activation->set_method(FrameMethod(fp));
    if (FlagsIsClosure(FrameFlags(fp))) {
      Closure closure = static_cast<Closure>(FrameTemp(fp, -1));
      ASSERT(closure->IsClosure());
      activation->set_closure(closure);
    } else {
      activation->set_closure(static_cast<Closure>(nil), kNoBarrier);
    }
    activation->set_receiver(FrameReceiver(fp));
    // Note this differs from Cog, which also copies the parameters. It may help
    // some debugging cases if parameters remain available in returned-from
    // activations, but for now it is slightly simpler to treat all locals
    // uniformly.
    activation->set_stack_depth(SmallInteger::New(0));

    FrameActivationPut(fp, activation);
  }
  return activation;
}


Activation Interpreter::FlushAllFrames() {
  Activation top = EnsureActivation(fp_);  // SAFEPOINT
  HandleScope h1(H, reinterpret_cast<Object*>(&top));

  while (fp_ != 0) {
    EnsureActivation(fp_);  // SAFEPOINT

    Object* saved_fp = FrameSavedFP(fp_);
    Activation sender;
    if (saved_fp != 0) {
      sender = EnsureActivation(saved_fp);  // SAFEPOINT
    } else {
      sender = FrameBaseSender(fp_);
      ASSERT((sender == nil) || sender->IsActivation());
    }
    ASSERT((sender == nil) || sender->IsActivation());

    Activation activation = FrameActivation(fp_);
    activation->set_sender(sender);
    activation->set_bci(activation->method()->BCI(ip_));

    intptr_t num_args = FlagsNumArgs(FrameFlags(fp_));
    intptr_t num_temps = num_args + FrameNumLocals(fp_, sp_);
    for (intptr_t i = 0; i < num_temps; i++) {
      activation->set_temp(i, FrameTemp(fp_, i));
    }
    activation->set_stack_depth(SmallInteger::New(num_temps));

    ip_ = FrameSavedIP(fp_);
    sp_ = FrameSavedSP(fp_);
    fp_ = saved_fp;
  }

  ip_ = 0;  // Was base sender.
  ASSERT(sp_ == stack_base_);
  ASSERT(fp_ == 0);
#if defined(DEBUG)
  for (intptr_t i = 0; i < kStackSlots; i++) {
    stack_limit_[i] = static_cast<Object>(kUninitializedWord);
  }
#endif

  return top;
}

bool Interpreter::HasLivingFrame(Activation activation) {
  if (!activation->sender()->IsSmallInteger()) {
    return false;
  }

  Object* activation_fp = activation->sender_fp();
  Object* fp = fp_;
  while (fp != 0) {
    if (fp == activation_fp) {
      if (FrameActivation(fp) == activation) {
        return true;
      }
      break;
    }
    fp = FrameSavedFP(fp);
  }

  // Frame is gone.
  activation->set_sender(static_cast<Activation>(nil), kNoBarrier);
  activation->set_bci(static_cast<SmallInteger>(nil));
  return false;
}

Activation Interpreter::CurrentActivation() {
  return EnsureActivation(fp_);  // SAFEPOINT
}

void Interpreter::SetCurrentActivation(Activation new_activation) {
  ASSERT(new_activation->IsActivation());

  if (fp_ != 0) {
    HandleScope h1(H, reinterpret_cast<Object*>(&new_activation));
    FlushAllFrames();  // SAFEPOINT
  }

  CreateBaseFrame(new_activation);
}

Object Interpreter::ActivationSender(Activation activation) {
  if (HasLivingFrame(activation)) {
    Object* fp = activation->sender_fp();
    Object* sender_fp = FrameSavedFP(fp);
    if (sender_fp == 0) {
      return FrameBaseSender(fp);
    }
    return EnsureActivation(sender_fp);  // SAFEPOINT
  } else {
    return activation->sender();
  }
}

void Interpreter::ActivationSenderPut(Activation activation,
                                      Activation new_sender) {
  ASSERT(!new_sender->IsSmallInteger());
  ASSERT((new_sender == nil) || new_sender->IsActivation());
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_sender));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_sender(new_sender);
    CreateBaseFrame(top);
  } else {
    activation->set_sender(new_sender);
  }
}

Object Interpreter::ActivationBCI(Activation activation) {
  if (activation->sender()->IsSmallInteger()) {
    Object* activation_fp = activation->sender_fp();
    Object* fp = fp_;
    const uint8_t* ip = ip_;
    while (fp != 0) {
      if (fp == activation_fp) {
        if (FrameActivation(fp) == activation) {
          return FrameMethod(fp)->BCI(ip);
        }
        break;
      }
      ip = FrameSavedIP(fp);
      fp = FrameSavedFP(fp);
    }
    // Frame is gone.
    activation->set_sender(static_cast<Activation>(nil), kNoBarrier);
    activation->set_bci(static_cast<SmallInteger>(nil));
  }

  return activation->bci();
}

void Interpreter::ActivationBCIPut(Activation activation,
                                   SmallInteger new_bci) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_bci));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_bci(new_bci);
    CreateBaseFrame(top);
  } else {
    return activation->set_bci(new_bci);
  }
}

void Interpreter::ActivationMethodPut(Activation activation,
                                      Method new_method) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_method));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_method(new_method);
    CreateBaseFrame(top);
  } else {
    activation->set_method(new_method);
  }
}

void Interpreter::ActivationClosurePut(Activation activation,
                                       Closure new_closure) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_closure));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_closure(new_closure);
    CreateBaseFrame(top);
  } else {
    activation->set_closure(new_closure);
  }
}


void Interpreter::ActivationReceiverPut(Activation activation,
                                        Object new_receiver) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_receiver));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_receiver(new_receiver);
    CreateBaseFrame(top);
  } else {
    activation->set_receiver(new_receiver);
  }
}

Object Interpreter::ActivationTempAt(Activation activation, intptr_t index) {
  if (HasLivingFrame(activation)) {
    Object* fp = activation->sender_fp();
    return FrameTemp(fp, index);
  } else {
    return activation->temp(index);
  }
}

void Interpreter::ActivationTempAtPut(Activation activation,
                                      intptr_t index,
                                      Object value) {
  if (HasLivingFrame(activation)) {
    Object* fp = activation->sender_fp();
    return FrameTempPut(fp, index, value);
  } else {
    return activation->set_temp(index, value);
  }
}

intptr_t Interpreter::ActivationTempSize(Activation activation) {
  if (activation->sender()->IsSmallInteger()) {
    Object* activation_fp = activation->sender_fp();
    Object* sp = sp_;
    Object* fp = fp_;
    while (fp != 0) {
      if (fp == activation_fp) {
        if (FrameActivation(fp) == activation) {
          return FlagsNumArgs(FrameFlags(fp)) + FrameNumLocals(fp, sp);
        }
        break;
      }
      sp = FrameSavedSP(fp);
      fp = FrameSavedFP(fp);
    }

    // Frame is gone.
    activation->set_sender(static_cast<Activation>(nil), kNoBarrier);
    activation->set_bci(static_cast<SmallInteger>(nil));
  }

  return activation->stack_depth()->value();
}

void Interpreter::ActivationTempSizePut(Activation activation,
                                        intptr_t new_size) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_size));
      top = FlushAllFrames();  // SAFEPOINT
    }
    intptr_t old_size = activation->StackDepth();
    for (intptr_t i = old_size; i < new_size; i++) {
      activation->set_temp(i, nil, kNoBarrier);
    }
    activation->set_stack_depth(SmallInteger::New(new_size));
    CreateBaseFrame(top);
  } else {
    intptr_t old_size = activation->StackDepth();
    for (intptr_t i = old_size; i < new_size; i++) {
      activation->set_temp(i, nil, kNoBarrier);
    }
    activation->set_stack_depth(SmallInteger::New(new_size));
  }
}

void Interpreter::GCPrologue() {
  // Convert IPs to BCIs. The makes every slot on the stack a valid object
  // pointer. Frame flags and saved FPs are valid as SmallIntegers.

  Object* fp = fp_;
  const uint8_t** ip_slot = &ip_;

  while (fp != 0) {
    SmallInteger bci = FrameMethod(fp)->BCI(*ip_slot);
    *ip_slot = reinterpret_cast<const uint8_t*>(static_cast<uword>(bci));

    ip_slot = FrameSavedIPSlot(fp);
    fp = FrameSavedFP(fp);
  }
}

void Interpreter::GCEpilogue() {
  // Convert BCIs to IPs. Invalidate lookup caches.

  Object* fp = fp_;
  const uint8_t** ip_slot = &ip_;

  while (fp != 0) {
    const SmallInteger bci =
        static_cast<const SmallInteger>(reinterpret_cast<uword>(*ip_slot));
    *ip_slot = FrameMethod(fp)->IP(bci);

    ip_slot = FrameSavedIPSlot(fp);
    fp = FrameSavedFP(fp);
  }

#if LOOKUP_CACHE
  lookup_cache_.Clear();
#endif
}

}  // namespace psoup
