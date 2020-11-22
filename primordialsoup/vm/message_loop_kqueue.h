// Copyright (c) 2018, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_MESSAGE_LOOP_KQUEUE_H_
#define VM_MESSAGE_LOOP_KQUEUE_H_

#if !defined(VM_MESSAGE_LOOP_H_)
#error Do not include message_loop_kqueue.h directly; use message_loop.h \
  instead.
#endif

#include "message_loop.h"
#include "thread.h"

namespace psoup {

#define PlatformMessageLoop KQueueMessageLoop

class KQueueMessageLoop : public MessageLoop {
 public:
  explicit KQueueMessageLoop(Isolate* isolate);
  ~KQueueMessageLoop();

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
  int interrupt_fds_[2];
  int kqueue_fd_;

  DISALLOW_COPY_AND_ASSIGN(KQueueMessageLoop);
};

}  // namespace psoup

#endif  // VM_MESSAGE_LOOP_KQUEUE_H_
