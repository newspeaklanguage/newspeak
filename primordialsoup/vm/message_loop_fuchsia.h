// Copyright (c) 2017, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_MESSAGE_LOOP_FUCHSIA_H_
#define VM_MESSAGE_LOOP_FUCHSIA_H_

#if !defined(VM_MESSAGE_LOOP_H_)
#error Do not include message_loop_fuchsia.h directly; use message_loop.h \
  instead.
#endif

#include <lib/async-loop/cpp/loop.h>
#include <lib/async/cpp/wait.h>
#include <lib/zx/timer.h>

#include "port.h"

namespace psoup {

#define PlatformMessageLoop FuchsiaMessageLoop

class FuchsiaMessageLoop : public MessageLoop {
 public:
  explicit FuchsiaMessageLoop(Isolate* isolate);
  ~FuchsiaMessageLoop();

  void PostMessage(IsolateMessage* message);
  intptr_t AwaitSignal(intptr_t handle, intptr_t signals);
  void CancelSignalWait(intptr_t wait_id);
  void MessageEpilogue(int64_t new_wakeup);
  void Exit(intptr_t exit_code);

  intptr_t Run();
  void Interrupt();

 private:
  void OnHandleReady(async_dispatcher_t* async,
                     async::WaitBase* wait,
                     zx_status_t status,
                     const zx_packet_signal_t* packet);

  using Wait =
      async::WaitMethod<FuchsiaMessageLoop, &FuchsiaMessageLoop::OnHandleReady>;

  async_loop_t* loop_;
  zx::timer timer_;
  Wait timer_wait_;
  int64_t wakeup_;

  DISALLOW_COPY_AND_ASSIGN(FuchsiaMessageLoop);
};

}  // namespace psoup

#endif  // VM_MESSAGE_LOOP_FUCHSIA_H_
