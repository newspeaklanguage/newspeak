// Copyright (c) 2018, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_WINDOWS)

#include "message_loop.h"

#include <signal.h>

#include "lockers.h"
#include "os.h"

namespace psoup {

IOCPMessageLoop::IOCPMessageLoop(Isolate* isolate)
    : MessageLoop(isolate),
      mutex_(),
      head_(NULL),
      tail_(NULL),
      wakeup_(0) {
  completion_port_ = CreateIoCompletionPort(INVALID_HANDLE_VALUE, NULL, NULL,
                                            1);
  if (completion_port_ == NULL) {
    FATAL("Failed to create IOCP");
  }
}

IOCPMessageLoop::~IOCPMessageLoop() {
  CloseHandle(completion_port_);
}

intptr_t IOCPMessageLoop::AwaitSignal(intptr_t fd, intptr_t signals) {
  UNIMPLEMENTED();
  return 0;
}

void IOCPMessageLoop::CancelSignalWait(intptr_t wait_id) {
  UNIMPLEMENTED();
}

void IOCPMessageLoop::MessageEpilogue(int64_t new_wakeup) {
  wakeup_ = new_wakeup;

  if ((open_ports_ == 0) && (wakeup_ == 0)) {
    Exit(0);
  }
}

void IOCPMessageLoop::Exit(intptr_t exit_code) {
  exit_code_ = exit_code;
  isolate_ = NULL;
}

void IOCPMessageLoop::PostMessage(IsolateMessage* message) {
  MutexLocker locker(&mutex_);
  if (head_ == NULL) {
    head_ = tail_ = message;
    Notify();
  } else {
    tail_->next_ = message;
    tail_ = message;
  }
}

void IOCPMessageLoop::Notify() {
  BOOL ok = PostQueuedCompletionStatus(completion_port_, 0, NULL,
                                       reinterpret_cast<OVERLAPPED*>(this));
  if (!ok) {
    FATAL("PostQueuedCompletionStatus failed");
  }
}

IsolateMessage* IOCPMessageLoop::TakeMessages() {
  MutexLocker locker(&mutex_);
  IsolateMessage* message = head_;
  head_ = tail_ = NULL;
  return message;
}

intptr_t IOCPMessageLoop::Run() {
  while (isolate_ != NULL) {
    DWORD timeout;
    if (wakeup_ == 0) {
      timeout = INFINITE;
    } else {
      int64_t timeout64 = (wakeup_ - OS::CurrentMonotonicNanos()) /
          kNanosecondsPerMillisecond;;
      if (timeout64 < 0) {
        timeout64 = 0;
      }
      if (timeout64 > kMaxInt32) {
        timeout64 = kMaxInt32;
      }
      COMPILE_ASSERT(sizeof(int32_t) == sizeof(DWORD));
      timeout = static_cast<DWORD>(timeout64);
    }

    DWORD bytes;
    ULONG_PTR key;
    OVERLAPPED* overlapped;
    BOOL ok = GetQueuedCompletionStatus(completion_port_, &bytes,
                                        &key, &overlapped, timeout);
    if (!ok && (overlapped == NULL)) {
      // Timeout.
      if ((wakeup_ != 0) && (OS::CurrentMonotonicNanos() >= wakeup_)) {
        DispatchWakeup();
      }
    } else if (key == NULL) {
      // Interrupt: will check messages below.
    } else {
      UNIMPLEMENTED();
    }

    IsolateMessage* message = TakeMessages();
    while (message != NULL) {
      IsolateMessage* next = message->next_;
      DispatchMessage(message);
      message = next;
    }
  }

  if (open_ports_ > 0) {
    PortMap::CloseAllPorts(this);
  }

  while (head_ != NULL) {
    IsolateMessage* message = head_;
    head_ = message->next_;
    delete message;
  }

  return exit_code_;
}

void IOCPMessageLoop::Interrupt() {
  Exit(SIGINT);
  Notify();
}

}  // namespace psoup

#endif  // defined(OS_WINDOWS)
