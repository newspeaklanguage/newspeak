// Copyright (c) 2019, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_MESSAGE_LOOP_EMSCRIPTEN_H_
#define VM_MESSAGE_LOOP_EMSCRIPTEN_H_

#if !defined(VM_MESSAGE_LOOP_H_)
#error Do not include message_loop_emscripten.h directly; use message_loop.h \
  instead.
#endif

#include "message_loop.h"

namespace psoup {

#define PlatformMessageLoop EmscriptenMessageLoop

class EmscriptenMessageLoop : public MessageLoop {
 public:
  explicit EmscriptenMessageLoop(Isolate* isolate);
  ~EmscriptenMessageLoop();

  void PostMessage(IsolateMessage* message);
  intptr_t AwaitSignal(intptr_t handle, intptr_t signals);
  void CancelSignalWait(intptr_t wait_id);
  void MessageEpilogue(int64_t new_wakeup);
  void Exit(intptr_t exit_code);

  intptr_t Run();
  void Interrupt();

  int HandleMessage();
  int HandleSignal(int handle, int status, int signals, int count);

 private:
  int ComputeTimeout();

  IsolateMessage* WaitMessage();

  IsolateMessage* head_;
  IsolateMessage* tail_;
  int64_t wakeup_;

  DISALLOW_COPY_AND_ASSIGN(EmscriptenMessageLoop);
};

}  // namespace psoup

#endif  // VM_MESSAGE_LOOP_EMSCRIPTEN_H_
