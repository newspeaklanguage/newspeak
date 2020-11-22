// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_INTERPRETER_H_
#define VM_INTERPRETER_H_

#include <setjmp.h>

#include "globals.h"
#include "assert.h"
#include "flags.h"
#include "lookup_cache.h"
#include "object.h"

namespace psoup {

class Heap;
class Isolate;
class Object;

class Interpreter {
 public:
  Interpreter(Heap* heap, Isolate* isolate);
  ~Interpreter();

  Isolate* isolate() const { return isolate_; }

  void Enter();
  void Exit();
  void ActivateDispatch(Method method, intptr_t num_args);
  void ReturnFromDispatch();

  void Perform(String selector, intptr_t num_args);
  Method MethodAt(Behavior cls, String selector);
  void ActivateClosure(intptr_t num_args);

  void Interrupt() { checked_stack_limit_ = reinterpret_cast<Object*>(-1); }
  void PrintStack();

  const uint8_t* IPForAssert() { return ip_; }

  Activation CurrentActivation();
  void SetCurrentActivation(Activation new_activation);
  Object ActivationSender(Activation activation);
  void ActivationSenderPut(Activation activation, Activation new_sender);
  Object ActivationBCI(Activation activation);
  void ActivationBCIPut(Activation activation, SmallInteger new_bci);
  void ActivationMethodPut(Activation activation, Method new_method);
  void ActivationClosurePut(Activation activation, Closure new_closure);
  void ActivationReceiverPut(Activation activation, Object value);
  Object ActivationTempAt(Activation activation, intptr_t index);
  void ActivationTempAtPut(Activation activation, intptr_t index,
                           Object value);
  intptr_t ActivationTempSize(Activation activation);
  void ActivationTempSizePut(Activation activation, intptr_t new_size);

  void GCPrologue();
  void RootPointers(Object** from, Object** to) {
    *from = &nil_;
    *to = reinterpret_cast<Object*>(&object_store_);
  }
  void StackPointers(Object** from, Object** to) {
    *from = sp_;
    *to = stack_base_ - 1;
  }
  void GCEpilogue();

  void Push(Object value) {
    ASSERT(sp_ <= stack_base_);
    ASSERT(sp_ > stack_limit_);
    *--sp_ = value;
  }
  Object Pop() {
    ASSERT(StackDepth() > 0);
    return *sp_++;
  }
  void PopNAndPush(intptr_t n, Object value) {
    ASSERT(StackDepth() >= n);
    sp_ += (n - 1);
    *sp_ = value;
  }
  Object Stack(intptr_t depth) {
    ASSERT((fp_ == 0) || (StackDepth() >= depth));
    return sp_[depth];
  }
  void StackPut(intptr_t depth, Object value) {
    ASSERT(StackDepth() >= depth);
    sp_[depth] = value;
  }
  void Grow(intptr_t elements) { sp_ -= elements; }
  void Drop(intptr_t elements) {
    ASSERT(StackDepth() >= elements);
    sp_ += elements;
  }
  intptr_t StackDepth() { return &fp_[-4] - sp_; }  // Magic!

  ObjectStore object_store() const { return object_store_; }
  Object nil_obj() const { return nil_; }
  Object false_obj() const { return false_; }
  Object true_obj() const { return true_; }
  void InitializeRoot(ObjectStore object_store) {
    ASSERT(object_store_ == nullptr);
    ASSERT(object_store->IsArray());
    nil_ = object_store->nil_obj();
    false_ = object_store->false_obj();
    true_ = object_store->true_obj();
    object_store_ = object_store;
    // Becomes the sender of the dispatch activation.
    ip_ = reinterpret_cast<const uint8_t*>(static_cast<uword>(nil_));
  }

 private:
  void Interpret();

  INLINE void PushIndirectLocal(intptr_t vector_offset, intptr_t offset);
  INLINE void PopIntoIndirectLocal(intptr_t vector_offset, intptr_t offset);
  INLINE void StoreIntoIndirectLocal(intptr_t vector_offset, intptr_t offset);

  INLINE void PushLiteral(intptr_t offset);
  INLINE void PushEnclosingObject(intptr_t depth);
  INLINE void PushNewArrayWithElements(intptr_t size);
  INLINE void PushNewArray(intptr_t size);
  void PushClosure(intptr_t num_copied, intptr_t num_args, intptr_t block_size);

  INLINE void CommonSend(intptr_t offset);
  INLINE void OrdinarySend(intptr_t selector_index, intptr_t num_args);
  INLINE void OrdinarySend(String selector, intptr_t num_args);
  NOINLINE void OrdinarySendMiss(String selector, intptr_t num_args);
  INLINE void SuperSend(intptr_t selector_index, intptr_t num_args);
  NOINLINE void SuperSendMiss(String selector, intptr_t num_args);
  INLINE void ImplicitReceiverSend(intptr_t selector_index, intptr_t num_args);
  NOINLINE void ImplicitReceiverSendMiss(String selector, intptr_t num_args);
  INLINE void OuterSend(intptr_t selector_index, intptr_t num_args,
                        intptr_t depth);
  NOINLINE void OuterSendMiss(String selector, intptr_t num_args,
                              intptr_t depth);
  INLINE void SelfSend(intptr_t selector_index, intptr_t num_args);
  NOINLINE void SelfSendMiss(String selector, intptr_t num_args);

  Behavior FindApplicationOf(AbstractMixin mixin, Behavior klass);
  bool HasMethod(Behavior, String selector);
  INLINE String SelectorAt(intptr_t index);

  void LexicalSend(String selector,
                   intptr_t num_args,
                   Object receiver,
                   AbstractMixin mixin,
                   intptr_t rule);
  void ProtectedSend(String selector,
                     intptr_t num_args,
                     Object receiver,
                     Behavior starting_at,
                     intptr_t rule);
  void DNUSend(String selector,
               intptr_t num_args,
               Object receiver,
               Behavior lookup_class,
               bool present_receiver);

  NOINLINE void SendCannotReturn(Object result);
  NOINLINE void SendAboutToReturnThrough(Object result, Activation unwind);
  NOINLINE void SendNonBooleanReceiver(Object non_boolean);

  INLINE void InsertAbsentReceiver(Object receiver, intptr_t num_args);
  INLINE void ActivateAbsent(Method method, Object receiver,
                             intptr_t num_args);
  NOINLINE void Activate(Method method, intptr_t num_args);
  NOINLINE void StackOverflow();

  INLINE void LocalReturn(Object result);
  NOINLINE void LocalBaseReturn(Object result);
  NOINLINE void NonLocalReturn(Object result);

  NOINLINE void CreateBaseFrame(Activation activation);
  NOINLINE Activation EnsureActivation(Object* fp);
  NOINLINE Activation FlushAllFrames();
  bool HasLivingFrame(Activation activation);

  static constexpr intptr_t kStackSlots = 1024;
  static constexpr intptr_t kStackSize = kStackSlots * sizeof(Object);

  const uint8_t* ip_;
  Object* sp_;
  Object* fp_;
  Object* stack_base_;
  Object* stack_limit_;
  Object* volatile checked_stack_limit_;

  Object nil_;
  Object false_;
  Object true_;
  ObjectStore object_store_;

  Heap* const heap_;
  Isolate* const isolate_;
  jmp_buf* environment_;
  LookupCache lookup_cache_;
};

}  // namespace psoup

#endif  // VM_INTERPRETER_H_
