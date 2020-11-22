// Copyright (c) 2017, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_FUCHSIA)

#include "message_loop.h"

#include <lib/async/cpp/task.h>
#include <zircon/status.h>
#include <zircon/syscalls.h>

#include "os.h"

namespace psoup {

FuchsiaMessageLoop::FuchsiaMessageLoop(Isolate* isolate)
    : MessageLoop(isolate),
      loop_(),
      timer_(ZX_HANDLE_INVALID),
      timer_wait_(this),
      wakeup_(0) {
  zx_status_t status =
      async_loop_create(&kAsyncLoopConfigNeverAttachToThread, &loop_);
  ASSERT(status == ZX_OK);

  status = zx::timer::create(ZX_TIMER_SLACK_LATE, ZX_CLOCK_MONOTONIC, &timer_);
  ASSERT(status == ZX_OK);
  timer_wait_.set_object(timer_.get());
  timer_wait_.set_trigger(ZX_TIMER_SIGNALED);
  status = timer_wait_.Begin(async_loop_get_dispatcher(loop_));
  ASSERT(status == ZX_OK);
}

FuchsiaMessageLoop::~FuchsiaMessageLoop() {
  zx_status_t status = timer_wait_.Cancel();
  ASSERT(status == ZX_OK);
  async_loop_destroy(loop_);
}

intptr_t FuchsiaMessageLoop::AwaitSignal(intptr_t handle, intptr_t signals) {
  open_waits_++;

  Wait* wait = new Wait(this, handle, signals);
  zx_status_t status = wait->Begin(async_loop_get_dispatcher(loop_));
  ASSERT(status == ZX_OK);
  ASSERT((reinterpret_cast<intptr_t>(wait) & 1) == 0);
  return reinterpret_cast<intptr_t>(wait) >> 1;
}

void FuchsiaMessageLoop::OnHandleReady(async_dispatcher_t* async,
                                       async::WaitBase* wait,
                                       zx_status_t status,
                                       const zx_packet_signal_t* packet) {
  wait->Begin(async_loop_get_dispatcher(loop_));

  if (wait == &timer_wait_) {
    DispatchWakeup();
  } else {
    zx_handle_t handle = wait->object();
    zx_signals_t pending = packet->observed;
    uint64_t count = packet->count;
    DispatchSignal(handle, status, pending, count);
  }
}

void FuchsiaMessageLoop::CancelSignalWait(intptr_t wait_id) {
  Wait* wait = reinterpret_cast<Wait*>(wait_id << 1);
  wait->Cancel();
  delete wait;

  open_waits_--;
}

void FuchsiaMessageLoop::MessageEpilogue(int64_t new_wakeup) {
  wakeup_ = new_wakeup;
  if (new_wakeup == 0) {
    zx_status_t result = timer_.cancel();
    ASSERT(result == ZX_OK);
  } else {
    zx_status_t result = timer_.set(zx::time(new_wakeup), zx::msec(1));
    ASSERT(result == ZX_OK);
  }

  if ((open_ports_ == 0) && (open_waits_ == 0) && (wakeup_ == 0)) {
    Exit(0);
  }
}

void FuchsiaMessageLoop::Exit(intptr_t exit_code) {
  exit_code_ = exit_code;
  isolate_ = NULL;
  async_loop_quit(loop_);
}

void FuchsiaMessageLoop::PostMessage(IsolateMessage* message) {
  async::PostTask(async_loop_get_dispatcher(loop_),
                  [this, message] { DispatchMessage(message); });
}

intptr_t FuchsiaMessageLoop::Run() {
  async_loop_run(loop_, ZX_TIME_INFINITE, false /* once */);

  if (open_ports_ > 0) {
    PortMap::CloseAllPorts(this);
  }

  return exit_code_;
}

void FuchsiaMessageLoop::Interrupt() {
  const intptr_t SIGINT = 2;
  Exit(SIGINT);
}

}  // namespace psoup

#endif  // defined(OS_FUCHSIA)
