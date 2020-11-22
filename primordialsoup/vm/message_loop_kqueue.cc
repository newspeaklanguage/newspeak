// Copyright (c) 2018, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_MACOS)

#include "message_loop.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>
#include <unistd.h>

#include "lockers.h"
#include "os.h"

namespace psoup {

static bool SetBlockingHelper(intptr_t fd, bool blocking) {
  intptr_t status;
  status = fcntl(fd, F_GETFL);
  if (status < 0) {
    perror("fcntl(F_GETFL) failed");
    return false;
  }
  status = blocking ? (status & ~O_NONBLOCK) : (status | O_NONBLOCK);
  if (fcntl(fd, F_SETFL, status) < 0) {
    perror("fcntl(F_SETFL, O_NONBLOCK) failed");
    return false;
  }
  return true;
}

KQueueMessageLoop::KQueueMessageLoop(Isolate* isolate)
    : MessageLoop(isolate),
      mutex_(),
      head_(NULL),
      tail_(NULL),
      wakeup_(0) {
  int result = pipe(interrupt_fds_);
  if (result != 0) {
    FATAL("Failed to create pipe");
  }
  if (!SetBlockingHelper(interrupt_fds_[0], false)) {
    FATAL("Failed to set pipe fd non-blocking\n");
  }

  kqueue_fd_ = kqueue();
  if (kqueue_fd_ == -1) {
    FATAL("Failed to create kqueue");
  }

  struct kevent event;
  EV_SET(&event, interrupt_fds_[0], EVFILT_READ, EV_ADD, 0, 0, NULL);
  int status = kevent(kqueue_fd_, &event, 1, NULL, 0, NULL);
  if (status == -1) {
    FATAL("Failed to add pipe to kqueue");
  }
}

KQueueMessageLoop::~KQueueMessageLoop() {
  close(kqueue_fd_);
  close(interrupt_fds_[0]);
  close(interrupt_fds_[1]);
}

intptr_t KQueueMessageLoop::AwaitSignal(intptr_t fd, intptr_t signals) {
  static const intptr_t kMaxChanges = 2;
  struct kevent changes[kMaxChanges];
  intptr_t nchanges = 0;
  void* udata = reinterpret_cast<void*>(fd);
  if (signals & (1 << kReadEvent)) {
    EV_SET(changes + nchanges, fd, EVFILT_READ, EV_ADD, 0, 0, udata);
    nchanges++;
  }
  if (signals & (1 << kWriteEvent)) {
    EV_SET(changes + nchanges, fd, EVFILT_WRITE, EV_ADD, 0, 0, udata);
    nchanges++;
  }
  ASSERT(nchanges > 0);
  ASSERT(nchanges <= kMaxChanges);
  int status = kevent(kqueue_fd_, changes, nchanges, NULL, 0, NULL);
  if (status == -1) {
    FATAL("Failed to add to kqueue");
  }

  return fd;
}

void KQueueMessageLoop::CancelSignalWait(intptr_t wait_id) {
  UNIMPLEMENTED();
}

void KQueueMessageLoop::MessageEpilogue(int64_t new_wakeup) {
  wakeup_ = new_wakeup;

  if ((open_ports_ == 0) && (wakeup_ == 0)) {
    Exit(0);
  }
}

void KQueueMessageLoop::Exit(intptr_t exit_code) {
  exit_code_ = exit_code;
  isolate_ = NULL;
}

void KQueueMessageLoop::PostMessage(IsolateMessage* message) {
  MutexLocker locker(&mutex_);
  if (head_ == NULL) {
    head_ = tail_ = message;
    Notify();
  } else {
    tail_->next_ = message;
    tail_ = message;
  }
}

void KQueueMessageLoop::Notify() {
  uword message = 0;
  ssize_t written = write(interrupt_fds_[1], &message, sizeof(message));
  if (written != sizeof(message)) {
    FATAL("Failed to atomically write notify message");
  }
}

IsolateMessage* KQueueMessageLoop::TakeMessages() {
  MutexLocker locker(&mutex_);
  IsolateMessage* message = head_;
  head_ = tail_ = NULL;
  return message;
}

intptr_t KQueueMessageLoop::Run() {
  while (isolate_ != NULL) {
    struct timespec* timeout = NULL;
    struct timespec ts;
    if (wakeup_ == 0) {
      // NULL pointer timespec for infinite timeout.
    } else {
      int64_t nanos = wakeup_ - OS::CurrentMonotonicNanos();
      if (nanos < 0) {
        nanos = 0;
      }
      ts.tv_sec = nanos / kNanosecondsPerSecond;
      ts.tv_nsec = nanos % kNanosecondsPerSecond;
      timeout = &ts;
    }

    static const intptr_t kMaxEvents = 16;
    struct kevent events[kMaxEvents];
    int result = kevent(kqueue_fd_, NULL, 0, events, kMaxEvents, timeout);
    if ((result == -1) && (errno != EINTR)) {
      FATAL("kevent failed");
    }

    if ((wakeup_ != 0) && (OS::CurrentMonotonicNanos() >= wakeup_)) {
      DispatchWakeup();
    }

    for (int i = 0; i < result; i++) {
      if ((events[i].flags & EV_ERROR) != 0) {
        FATAL("kevent failed\n");
      }
      if (events[i].udata == NULL) {
        // Interrupt fd.
        uword message = 0;
        ssize_t red = read(interrupt_fds_[0], &message, sizeof(message));
        if (red != sizeof(message)) {
          FATAL("Failed to atomically write notify message");
        }
      } else {
        intptr_t fd = events[i].ident;
        intptr_t pending = 0;
        if (events[i].filter == EVFILT_READ) {
          pending |= 1 << kReadEvent;
          if ((events[i].flags & EV_EOF) != 0) {
            if (events[i].fflags != 0) {
              pending = (1 << kErrorEvent);
            } else {
              pending |= (1 << kCloseEvent);
            }
          }
        } else if (events[i].filter == EVFILT_WRITE) {
          pending |= (1 << kWriteEvent);
          if ((events[i].flags & EV_EOF) != 0) {
            if (events[i].fflags != 0) {
              pending = (1 << kErrorEvent);
            }
          }
        } else {
          UNREACHABLE();
        }
        DispatchSignal(fd, 0, pending, 0);
      }
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

void KQueueMessageLoop::Interrupt() {
  Exit(SIGINT);
  Notify();
}

}  // namespace psoup

#endif  // defined(OS_MACOS)
