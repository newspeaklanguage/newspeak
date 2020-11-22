// Copyright (c) 2019, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_EMSCRIPTEN)

#include "message_loop.h"

#include <emscripten.h>

#include "os.h"

namespace psoup {

EmscriptenMessageLoop::EmscriptenMessageLoop(Isolate* isolate)
    : MessageLoop(isolate),
      head_(NULL),
      tail_(NULL),
      wakeup_(0) {}

EmscriptenMessageLoop::~EmscriptenMessageLoop() {}

intptr_t EmscriptenMessageLoop::AwaitSignal(intptr_t handle,
                                            intptr_t signals) {
  UNIMPLEMENTED();
  return 0;
}

void EmscriptenMessageLoop::CancelSignalWait(intptr_t wait_id) {
  UNIMPLEMENTED();
}

void EmscriptenMessageLoop::MessageEpilogue(int64_t new_wakeup) {
  wakeup_ = new_wakeup;
}

void EmscriptenMessageLoop::Exit(intptr_t exit_code) {
  exit_code_ = exit_code;
  isolate_ = NULL;

  if (open_ports_ > 0) {
    PortMap::CloseAllPorts(this);
  }

  while (head_ != NULL) {
    IsolateMessage* message = head_;
    head_ = message->next_;
    delete message;
  }
}

void EmscriptenMessageLoop::PostMessage(IsolateMessage* message) {
  if (head_ == NULL) {
    head_ = tail_ = message;
  } else {
    tail_->next_ = message;
    tail_ = message;
  }
}

intptr_t EmscriptenMessageLoop::Run() {
  UNREACHABLE();
  return -1;
}

int EmscriptenMessageLoop::HandleMessage() {
  IsolateMessage* message = head_;
  if (head_ != NULL) {
    head_ = message->next_;
    if (head_ == NULL) {
      tail_ = NULL;
    }
  }

  if (message == NULL) {
    DispatchWakeup();
  } else {
    DispatchMessage(message);
  }

  return ComputeTimeout();
}

int EmscriptenMessageLoop::HandleSignal(int handle,
                                        int status,
                                        int signals,
                                        int count) {
  DispatchSignal(handle, status, signals, count);
  return ComputeTimeout();
}

int EmscriptenMessageLoop::ComputeTimeout() {
  if (head_ != NULL) return 0;

  if (wakeup_ == 0) return -1;

  int64_t now = OS::CurrentMonotonicNanos();
  if (wakeup_ <= now) {
    return 0;
  }

  return (wakeup_ - now) / kNanosecondsPerMillisecond;
}

void EmscriptenMessageLoop::Interrupt() {
  UNREACHABLE();
}

}  // namespace psoup

#endif  // defined(OS_EMSCRIPTEN)
