// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_THREAD_H_
#define VM_THREAD_H_

#include "allocation.h"
#include "globals.h"

// Declare the OS-specific types ahead of defining the generic classes.
#if defined(OS_ANDROID)
#include "thread_android.h"
#elif defined(OS_EMSCRIPTEN)
#include "thread_emscripten.h"
#elif defined(OS_FUCHSIA)
#include "thread_fuchsia.h"
#elif defined(OS_LINUX)
#include "thread_linux.h"
#elif defined(OS_MACOS)
#include "thread_macos.h"
#elif defined(OS_WINDOWS)
#include "thread_win.h"
#else
#error Unknown OS.
#endif

namespace psoup {

class Thread : public AllStatic {
 public:
  typedef void (*ThreadStartFunction)(uword parameter);

  // Start a thread running the specified function. Returns 0 if the
  // thread started successfuly and a system specific error code if
  // the thread failed to start.
  static int Start(const char* name,
                   ThreadStartFunction function,
                   uword parameter);

  static ThreadId GetCurrentThreadId();
  static void Join(ThreadJoinId id);
  static intptr_t ThreadIdToIntPtr(ThreadId id);
  static ThreadId ThreadIdFromIntPtr(intptr_t id);
  static bool Compare(ThreadId a, ThreadId b);

  // This function can be called only once per Thread, and should only be
  // called when the returned id will eventually be passed to Thread::Join().
  static ThreadJoinId GetCurrentThreadJoinId();

  static void DisableThreadCreation();
  static void EnableThreadCreation();

  static const ThreadId kInvalidThreadId;
  static const ThreadJoinId kInvalidThreadJoinId;

  static ThreadId GetCurrentThreadTraceId();
};

class Mutex {
 public:
  Mutex();
  ~Mutex();

#if defined(DEBUG)
  bool IsOwnedByCurrentThread() const {
    return owner_ == Thread::GetCurrentThreadId();
  }
#endif

 private:
  void Lock();
  bool TryLock();  // Returns false if lock is busy and locking failed.
  void Unlock();

  void CheckHeldAndUnmark() {
#if defined(DEBUG)
    ASSERT(owner_ == Thread::GetCurrentThreadId());
    owner_ = Thread::kInvalidThreadId;
#endif
  }
  void CheckUnheldAndMark() {
#if defined(DEBUG)
    ASSERT(owner_ == Thread::kInvalidThreadId);
    owner_ = Thread::GetCurrentThreadId();
#endif
  }

  MutexData data_;
#if defined(DEBUG)
  ThreadId owner_;
#endif  // defined(DEBUG)

  friend class MutexLocker;
  DISALLOW_COPY_AND_ASSIGN(Mutex);
};


class Monitor {
 public:
  enum WaitResult { kNotified, kTimedOut };

  Monitor();
  ~Monitor();

#if defined(DEBUG)
  bool IsOwnedByCurrentThread() const {
    return owner_ == Thread::GetCurrentThreadId();
  }
#endif

 private:
  bool TryEnter();  // Returns false if lock is busy and locking failed.
  void Enter();
  void Exit();

  // Wait for notification or deadline.
  void Wait();
  WaitResult WaitUntilNanos(int64_t deadline);

  // Notify waiting threads.
  void Notify();
  void NotifyAll();

  void CheckHeldAndUnmark() {
#if defined(DEBUG)
    ASSERT(owner_ == Thread::GetCurrentThreadId());
    owner_ = Thread::kInvalidThreadId;
#endif
  }
  void CheckUnheldAndMark() {
#if defined(DEBUG)
    ASSERT(owner_ == Thread::kInvalidThreadId);
    owner_ = Thread::GetCurrentThreadId();
#endif
  }

  MonitorData data_;  // OS-specific data.
#if defined(DEBUG)
  ThreadId owner_;
#endif  // defined(DEBUG)

  friend class MonitorLocker;
  DISALLOW_COPY_AND_ASSIGN(Monitor);
};


}  // namespace psoup


#endif  // VM_THREAD_H_
