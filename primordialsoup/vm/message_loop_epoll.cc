// Copyright (c) 2018, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_ANDROID) || defined(OS_LINUX)

#include "message_loop.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/epoll.h>
#include <sys/timerfd.h>
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

EPollMessageLoop::EPollMessageLoop(Isolate* isolate)
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

  timer_fd_ = timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC);
  if (timer_fd_ == -1) {
    FATAL("Failed to creater timer_fd");
  }

  epoll_fd_ = epoll_create(64);
  if (epoll_fd_ == -1) {
    FATAL("Failed to create epoll");
  }

  struct epoll_event event;
  event.events = EPOLLIN;
  event.data.fd = interrupt_fds_[0];
  int status = epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, interrupt_fds_[0], &event);
  if (status == -1) {
    FATAL("Failed to add pipe to epoll");
  }

  event.events = EPOLLIN;
  event.data.fd = timer_fd_;
  status = epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, timer_fd_, &event);
  if (status == -1) {
    FATAL("Failed to add timer_fd to epoll");
  }
}

EPollMessageLoop::~EPollMessageLoop() {
  close(epoll_fd_);
  close(timer_fd_);
  close(interrupt_fds_[0]);
  close(interrupt_fds_[1]);
}

intptr_t EPollMessageLoop::AwaitSignal(intptr_t fd, intptr_t signals) {
  struct epoll_event event;
  event.events = EPOLLRDHUP | EPOLLET;
  if (signals & (1 << kReadEvent)) {
    event.events |= EPOLLIN;
  }
  if (signals & (1 << kWriteEvent)) {
    event.events |= EPOLLOUT;
  }
  event.data.fd = fd;

  int status = epoll_ctl(epoll_fd_, EPOLL_CTL_ADD, fd, &event);
  if (status == -1) {
    FATAL("Failed to add to epoll");
  }
  return fd;
}

void EPollMessageLoop::CancelSignalWait(intptr_t wait_id) {
  UNIMPLEMENTED();
}

void EPollMessageLoop::MessageEpilogue(int64_t new_wakeup) {
  wakeup_ = new_wakeup;

  struct itimerspec it;
  memset(&it, 0, sizeof(it));
  if (new_wakeup != 0) {
    it.it_value.tv_sec = new_wakeup / kNanosecondsPerSecond;
    it.it_value.tv_nsec = new_wakeup % kNanosecondsPerSecond;
  }
  timerfd_settime(timer_fd_, TFD_TIMER_ABSTIME, &it, NULL);

  if ((open_ports_ == 0) && (wakeup_ == 0)) {
    Exit(0);
  }
}

void EPollMessageLoop::Exit(intptr_t exit_code) {
  exit_code_ = exit_code;
  isolate_ = NULL;
}

void EPollMessageLoop::PostMessage(IsolateMessage* message) {
  MutexLocker locker(&mutex_);
  if (head_ == NULL) {
    head_ = tail_ = message;
    Notify();
  } else {
    tail_->next_ = message;
    tail_ = message;
  }
}

void EPollMessageLoop::Notify() {
  uword message = 0;
  ssize_t written = write(interrupt_fds_[1], &message, sizeof(message));
  if (written != sizeof(message)) {
    FATAL("Failed to atomically write notify message");
  }
}

IsolateMessage* EPollMessageLoop::TakeMessages() {
  MutexLocker locker(&mutex_);
  IsolateMessage* message = head_;
  head_ = tail_ = NULL;
  return message;
}

intptr_t EPollMessageLoop::Run() {
  while (isolate_ != NULL) {
    static const intptr_t kMaxEvents = 16;
    struct epoll_event events[kMaxEvents];

    int result = epoll_wait(epoll_fd_, events, kMaxEvents, -1);
    if (result <= 0) {
      if ((errno != EWOULDBLOCK) && (errno != EINTR)) {
        FATAL("epoll_wait failed");
      }
    } else {
      for (int i = 0; i < result; i++) {
        if (events[i].data.fd == interrupt_fds_[0]) {
          // Interrupt fd.
          uword message = 0;
          ssize_t red = read(interrupt_fds_[0], &message, sizeof(message));
          if (red != sizeof(message)) {
            FATAL("Failed to atomically write notify message");
          }
        } else if (events[i].data.fd == timer_fd_) {
          int64_t value;
          ssize_t ignore = read(timer_fd_, &value, sizeof(value));
          (void)ignore;
          DispatchWakeup();
        } else {
          intptr_t fd = events[i].data.fd;
          intptr_t pending = 0;
          if (events[i].events & EPOLLERR) {
            pending |= 1 << kErrorEvent;
          }
          if (events[i].events & EPOLLIN) {
            pending |= 1 << kReadEvent;
          }
          if (events[i].events & EPOLLOUT) {
            pending |= 1 << kWriteEvent;
          }
          if (events[i].events & EPOLLHUP) {
            pending |= 1 << kCloseEvent;
          }
          if (events[i].events & EPOLLRDHUP) {
            pending |= 1 << kCloseEvent;
          }
          DispatchSignal(fd, 0, pending, 0);
        }
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

void EPollMessageLoop::Interrupt() {
  Exit(SIGINT);
  Notify();
}

}  // namespace psoup

#endif  // defined(OS_ANDROID) || defined(OS_LINUX)
