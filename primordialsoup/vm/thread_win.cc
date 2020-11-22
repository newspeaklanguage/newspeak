// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_WINDOWS)

#include "assert.h"
#include "lockers.h"
#include "os.h"
#include "thread.h"

#include <process.h>  // NOLINT

namespace psoup {

class ThreadStartData {
 public:
  ThreadStartData(const char* name,
                  Thread::ThreadStartFunction function,
                  uword parameter)
      : name_(name), function_(function), parameter_(parameter) {}

  const char* name() const { return name_; }
  Thread::ThreadStartFunction function() const { return function_; }
  uword parameter() const { return parameter_; }

 private:
  const char* name_;
  Thread::ThreadStartFunction function_;
  uword parameter_;

  DISALLOW_COPY_AND_ASSIGN(ThreadStartData);
};


// Dispatch to the thread start function provided by the caller. This trampoline
// is used to ensure that the thread is properly destroyed if the thread just
// exits.
static unsigned int __stdcall ThreadEntry(void* data_ptr) {
  ThreadStartData* data = reinterpret_cast<ThreadStartData*>(data_ptr);

  const char* name = data->name();
  Thread::ThreadStartFunction function = data->function();
  uword parameter = data->parameter();
  delete data;

  // Call the supplied thread start function handing it its parameters.
  function(parameter);

  return 0;
}


int Thread::Start(const char* name,
                  ThreadStartFunction function,
                  uword parameter) {
  ThreadStartData* start_data = new ThreadStartData(name, function, parameter);
  uint32_t tid;
  uintptr_t thread = _beginthreadex(NULL, 0,
                                    ThreadEntry, start_data, 0, &tid);
  if (thread == -1L || thread == 0) {
#ifdef DEBUG
    fprintf(stderr, "_beginthreadex error: %d (%s)\n", errno, strerror(errno));
#endif
    return errno;
  }

  // Close the handle, so we don't leak the thread object.
  CloseHandle(reinterpret_cast<HANDLE>(thread));

  return 0;
}


const ThreadId Thread::kInvalidThreadId = 0;
const ThreadJoinId Thread::kInvalidThreadJoinId = NULL;


ThreadId Thread::GetCurrentThreadId() {
  return ::GetCurrentThreadId();
}


ThreadId Thread::GetCurrentThreadTraceId() {
  return ::GetCurrentThreadId();
}


ThreadJoinId Thread::GetCurrentThreadJoinId() {
  ThreadId id = GetCurrentThreadId();
  HANDLE handle = OpenThread(SYNCHRONIZE, false, id);
  ASSERT(handle != NULL);
  return handle;
}


void Thread::Join(ThreadJoinId id) {
  HANDLE handle = static_cast<HANDLE>(id);
  ASSERT(handle != NULL);
  DWORD res = WaitForSingleObject(handle, INFINITE);
  CloseHandle(handle);
  ASSERT(res == WAIT_OBJECT_0);
}


intptr_t Thread::ThreadIdToIntPtr(ThreadId id) {
  ASSERT(sizeof(id) <= sizeof(intptr_t));
  return static_cast<intptr_t>(id);
}


ThreadId Thread::ThreadIdFromIntPtr(intptr_t id) {
  return static_cast<ThreadId>(id);
}


bool Thread::Compare(ThreadId a, ThreadId b) {
  return a == b;
}


Mutex::Mutex() {
  InitializeSRWLock(&data_.lock_);
#if defined(DEBUG)
  // When running with assertions enabled we do track the owner.
  owner_ = Thread::kInvalidThreadId;
#endif  // defined(DEBUG)
}


Mutex::~Mutex() {
#if defined(DEBUG)
  // When running with assertions enabled we do track the owner.
  ASSERT(owner_ == Thread::kInvalidThreadId);
#endif  // defined(DEBUG)
}


void Mutex::Lock() {
  AcquireSRWLockExclusive(&data_.lock_);
  CheckUnheldAndMark();
}


bool Mutex::TryLock() {
  if (TryAcquireSRWLockExclusive(&data_.lock_)) {
    CheckUnheldAndMark();
    return true;
  }
  return false;
}


void Mutex::Unlock() {
  CheckHeldAndUnmark();
  ReleaseSRWLockExclusive(&data_.lock_);
}


Monitor::Monitor() {
  InitializeSRWLock(&data_.lock_);
  InitializeConditionVariable(&data_.cond_);

#if defined(DEBUG)
  // When running with assertions enabled we track the owner.
  owner_ = Thread::kInvalidThreadId;
#endif  // defined(DEBUG)
}


Monitor::~Monitor() {
#if defined(DEBUG)
  // When running with assertions enabled we track the owner.
  ASSERT(owner_ == Thread::kInvalidThreadId);
#endif  // defined(DEBUG)
}


bool Monitor::TryEnter() {
  if (TryAcquireSRWLockExclusive(&data_.lock_)) {
    CheckUnheldAndMark();
    return true;
  }
  return false;
}


void Monitor::Enter() {
  AcquireSRWLockExclusive(&data_.lock_);
  CheckUnheldAndMark();
}


void Monitor::Exit() {
  CheckHeldAndUnmark();
  ReleaseSRWLockExclusive(&data_.lock_);
}


void Monitor::Wait() {
  CheckHeldAndUnmark();
  SleepConditionVariableSRW(&data_.cond_, &data_.lock_, INFINITE, 0);
  CheckUnheldAndMark();
}


Monitor::WaitResult Monitor::WaitUntilNanos(int64_t deadline) {
  int64_t now = OS::CurrentMonotonicNanos();
  if (deadline <= now) {
    return kTimedOut;
  }

  int64_t millis = (deadline - now) / kNanosecondsPerMillisecond;

  CheckHeldAndUnmark();

  Monitor::WaitResult retval = kNotified;
  // Wait for the given period of time for a Notify or a NotifyAll
  // event.
  if (!SleepConditionVariableSRW(&data_.cond_, &data_.lock_, millis, 0)) {
    ASSERT(GetLastError() == ERROR_TIMEOUT);
    retval = kTimedOut;
  }

  CheckUnheldAndMark();
  return retval;
}


void Monitor::Notify() {
  // When running with assertions enabled we track the owner.
  DEBUG_ASSERT(IsOwnedByCurrentThread());
  WakeConditionVariable(&data_.cond_);
}


void Monitor::NotifyAll() {
  // When running with assertions enabled we track the owner.
  DEBUG_ASSERT(IsOwnedByCurrentThread());
  WakeAllConditionVariable(&data_.cond_);
}

}  // namespace psoup

#endif  // defined(OS_WINDOWS)
