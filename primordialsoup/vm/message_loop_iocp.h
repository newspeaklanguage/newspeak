// Copyright (c) 2018, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_MESSAGE_LOOP_IOCP_H_
#define VM_MESSAGE_LOOP_IOCP_H_

#if !defined(VM_MESSAGE_LOOP_H_)
#error Do not include message_loop_iocp.h directly; use message_loop.h instead.
#endif

#include "message_loop.h"
#include "thread.h"

namespace psoup {

#define PlatformMessageLoop IOCPMessageLoop

class IOCPMessageLoop : public MessageLoop {
 public:
  explicit IOCPMessageLoop(Isolate* isolate);
  ~IOCPMessageLoop();

  void PostMessage(IsolateMessage* message);
  intptr_t AwaitSignal(intptr_t handle, intptr_t signals);
  void CancelSignalWait(intptr_t wait_id);
  void MessageEpilogue(int64_t new_wakeup);
  void Exit(intptr_t exit_code);

  intptr_t Run();
  void Interrupt();

 private:
  IsolateMessage* TakeMessages();
  void Notify();

  Mutex mutex_;
  IsolateMessage* head_;
  IsolateMessage* tail_;
  int64_t wakeup_;
  HANDLE completion_port_;

  DISALLOW_COPY_AND_ASSIGN(IOCPMessageLoop);
};

}  // namespace psoup

#endif  // VM_MESSAGE_LOOP_IOCP_H_
