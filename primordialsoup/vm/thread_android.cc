// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"  // NOLINT
#if defined(OS_ANDROID)

#include "thread.h"

#include <errno.h>     // NOLINT
#include <sys/time.h>  // NOLINT
#include <unistd.h>    // NOLINT

#include "assert.h"
#include "utils.h"

namespace psoup {

#define VALIDATE_PTHREAD_RESULT(result)                                        \
  if (result != 0) {                                                           \
    const int kBufferSize = 1024;                                              \
    char error_message[kBufferSize];                                           \
    Utils::StrError(result, error_message, kBufferSize);                       \
    FATAL2("pthread error: %d (%s)", result, error_message);                   \
  }


#if defined(DEBUG)
#define ASSERT_PTHREAD_SUCCESS(result) VALIDATE_PTHREAD_RESULT(result)
#else
// NOTE: This (currently) expands to a no-op.
#define ASSERT_PTHREAD_SUCCESS(result) ASSERT(result == 0)
#endif


#ifdef DEBUG
#define RETURN_ON_PTHREAD_FAILURE(result)                                      \
  if (result != 0) {                                                           \
    const int kBufferSize = 1024;                                              \
    char error_message[kBufferSize];                                           \
    Utils::StrError(result, error_message, kBufferSize);                       \
    fprintf(stderr, "%s:%d: pthread error: %d (%s)\n", __FILE__, __LINE__,     \
            result, error_message);                                            \
    return result;                                                             \
  }
#else
#define RETURN_ON_PTHREAD_FAILURE(result)                                      \
  if (result != 0) return result;
#endif


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
static void* ThreadStart(void* data_ptr) {
  ThreadStartData* data = reinterpret_cast<ThreadStartData*>(data_ptr);

  const char* name = data->name();
  Thread::ThreadStartFunction function = data->function();
  uword parameter = data->parameter();
  delete data;

  // Set the thread name.
  pthread_setname_np(pthread_self(), name);

  // Call the supplied thread start function handing it its parameters.
  function(parameter);

  return NULL;
}


int Thread::Start(const char* name,
                  ThreadStartFunction function,
                  uword parameter) {
  pthread_attr_t attr;
  int result = pthread_attr_init(&attr);
  RETURN_ON_PTHREAD_FAILURE(result);

  ThreadStartData* data = new ThreadStartData(name, function, parameter);

  pthread_t tid;
  result = pthread_create(&tid, &attr, ThreadStart, data);
  RETURN_ON_PTHREAD_FAILURE(result);

  result = pthread_attr_destroy(&attr);
  RETURN_ON_PTHREAD_FAILURE(result);

  return 0;
}


const ThreadId Thread::kInvalidThreadId = static_cast<ThreadId>(0);
const ThreadJoinId Thread::kInvalidThreadJoinId =
    static_cast<ThreadJoinId>(0);


ThreadId Thread::GetCurrentThreadId() {
  return gettid();
}


ThreadId Thread::GetCurrentThreadTraceId() {
  return GetCurrentThreadId();
}


ThreadJoinId Thread::GetCurrentThreadJoinId() {
  return pthread_self();
}


void Thread::Join(ThreadJoinId id) {
  int result = pthread_join(id, NULL);
  ASSERT(result == 0);
}


intptr_t Thread::ThreadIdToIntPtr(ThreadId id) {
  ASSERT(sizeof(id) == sizeof(intptr_t));
  return static_cast<intptr_t>(id);
}


ThreadId Thread::ThreadIdFromIntPtr(intptr_t id) {
  return static_cast<ThreadId>(id);
}


bool Thread::Compare(ThreadId a, ThreadId b) {
  return a == b;
}


Mutex::Mutex() {
  pthread_mutexattr_t attr;
  int result = pthread_mutexattr_init(&attr);
  VALIDATE_PTHREAD_RESULT(result);

#if defined(DEBUG)
  result = pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_ERRORCHECK);
  VALIDATE_PTHREAD_RESULT(result);
#endif  // defined(DEBUG)

  result = pthread_mutex_init(data_.mutex(), &attr);
  // Verify that creating a pthread_mutex succeeded.
  VALIDATE_PTHREAD_RESULT(result);

  result = pthread_mutexattr_destroy(&attr);
  VALIDATE_PTHREAD_RESULT(result);

#if defined(DEBUG)
  // When running with assertions enabled we do track the owner.
  owner_ = Thread::kInvalidThreadId;
#endif  // defined(DEBUG)
}


Mutex::~Mutex() {
  int result = pthread_mutex_destroy(data_.mutex());
  // Verify that the pthread_mutex was destroyed.
  VALIDATE_PTHREAD_RESULT(result);

#if defined(DEBUG)
  // When running with assertions enabled we do track the owner.
  ASSERT(owner_ == Thread::kInvalidThreadId);
#endif  // defined(DEBUG)
}


void Mutex::Lock() {
  int result = pthread_mutex_lock(data_.mutex());
  // Specifically check for dead lock to help debugging.
  ASSERT(result != EDEADLK);
  ASSERT_PTHREAD_SUCCESS(result);  // Verify no other errors.
  CheckUnheldAndMark();
}


bool Mutex::TryLock() {
  int result = pthread_mutex_trylock(data_.mutex());
  // Return false if the lock is busy and locking failed.
  if (result == EBUSY) {
    return false;
  }
  ASSERT_PTHREAD_SUCCESS(result);  // Verify no other errors.
  CheckUnheldAndMark();
  return true;
}


void Mutex::Unlock() {
  CheckHeldAndUnmark();
  int result = pthread_mutex_unlock(data_.mutex());
  // Specifically check for wrong thread unlocking to aid debugging.
  ASSERT(result != EPERM);
  ASSERT_PTHREAD_SUCCESS(result);  // Verify no other errors.
}


Monitor::Monitor() {
  pthread_mutexattr_t mutex_attr;
  int result = pthread_mutexattr_init(&mutex_attr);
  VALIDATE_PTHREAD_RESULT(result);

#if defined(DEBUG)
  result = pthread_mutexattr_settype(&mutex_attr, PTHREAD_MUTEX_ERRORCHECK);
  VALIDATE_PTHREAD_RESULT(result);
#endif  // defined(DEBUG)

  result = pthread_mutex_init(data_.mutex(), &mutex_attr);
  VALIDATE_PTHREAD_RESULT(result);

  result = pthread_mutexattr_destroy(&mutex_attr);
  VALIDATE_PTHREAD_RESULT(result);

  pthread_condattr_t cond_attr;
  result = pthread_condattr_init(&cond_attr);
  VALIDATE_PTHREAD_RESULT(result);

  // Since Android 5.0 (API level 21).
  result = pthread_condattr_setclock(&cond_attr, CLOCK_MONOTONIC);
  VALIDATE_PTHREAD_RESULT(result);

  result = pthread_cond_init(data_.cond(), &cond_attr);
  VALIDATE_PTHREAD_RESULT(result);

  result = pthread_condattr_destroy(&cond_attr);
  VALIDATE_PTHREAD_RESULT(result);

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

  int result = pthread_mutex_destroy(data_.mutex());
  VALIDATE_PTHREAD_RESULT(result);

  result = pthread_cond_destroy(data_.cond());
  VALIDATE_PTHREAD_RESULT(result);
}


bool Monitor::TryEnter() {
  int result = pthread_mutex_trylock(data_.mutex());
  // Return false if the lock is busy and locking failed.
  if (result == EBUSY) {
    return false;
  }
  ASSERT_PTHREAD_SUCCESS(result);  // Verify no other errors.
  CheckUnheldAndMark();
  return true;
}


void Monitor::Enter() {
  int result = pthread_mutex_lock(data_.mutex());
  VALIDATE_PTHREAD_RESULT(result);
  CheckUnheldAndMark();
}


void Monitor::Exit() {
  CheckHeldAndUnmark();
  int result = pthread_mutex_unlock(data_.mutex());
  VALIDATE_PTHREAD_RESULT(result);
}


void Monitor::Wait() {
  CheckHeldAndUnmark();
  int result = pthread_cond_wait(data_.cond(), data_.mutex());
  VALIDATE_PTHREAD_RESULT(result);
  CheckUnheldAndMark();
}


Monitor::WaitResult Monitor::WaitUntilNanos(int64_t deadline) {
  CheckHeldAndUnmark();

  Monitor::WaitResult retval = kNotified;
  struct timespec ts;
  int64_t secs = deadline / kNanosecondsPerSecond;
  int64_t nanos = deadline % kNanosecondsPerSecond;
  if (secs > kMaxInt32) {
    // Avoid truncation of overly large timeout values.
    secs = kMaxInt32;
  }
  ts.tv_sec = static_cast<int32_t>(secs);
  ts.tv_nsec = static_cast<long>(nanos);  // NOLINT (long used in timespec).
  int result = pthread_cond_timedwait(data_.cond(), data_.mutex(), &ts);
  ASSERT((result == 0) || (result == ETIMEDOUT));
  if (result == ETIMEDOUT) {
    retval = kTimedOut;
  }

  CheckUnheldAndMark();
  return retval;
}


void Monitor::Notify() {
  // When running with assertions enabled we track the owner.
  DEBUG_ASSERT(IsOwnedByCurrentThread());
  int result = pthread_cond_signal(data_.cond());
  VALIDATE_PTHREAD_RESULT(result);
}


void Monitor::NotifyAll() {
  // When running with assertions enabled we track the owner.
  DEBUG_ASSERT(IsOwnedByCurrentThread());
  int result = pthread_cond_broadcast(data_.cond());
  VALIDATE_PTHREAD_RESULT(result);
}

}  // namespace psoup

#endif  // defined(OS_ANDROID)
