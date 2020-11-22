// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_LOCKERS_H_
#define VM_LOCKERS_H_

#include "assert.h"
#include "allocation.h"
#include "globals.h"
#include "thread.h"

namespace psoup {

/*
 * Normal mutex locker :
 * This locker abstraction should only be used when the enclosing code can
 * not trigger a safepoint. In debug mode this class increments the
 * no_safepoint_scope_depth variable for the current thread when the lock is
 * taken and decrements it when the lock is released. NOTE: please do not use
 * the passed in mutex object independent of the locker class, For example the
 * code below will not assert correctly:
 *    {
 *      MutexLocker ml(m);
 *      ....
 *      m->Exit();
 *      ....
 *      m->Enter();
 *      ...
 *    }
 * Always use the locker object even when the lock needs to be released
 * temporarily, e.g:
 *    {
 *      MutexLocker ml(m);
 *      ....
 *      ml.Exit();
 *      ....
 *      ml.Enter();
 *      ...
 *    }
 */
class MutexLocker : public ValueObject {
 public:
  explicit MutexLocker(Mutex* mutex, bool no_safepoint_scope = true)
      : mutex_(mutex), no_safepoint_scope_(no_safepoint_scope) {
    ASSERT(mutex != NULL);
    mutex_->Lock();
  }

  virtual ~MutexLocker() {
    mutex_->Unlock();
  }

  void Lock() const {
    mutex_->Lock();
  }
  void Unlock() const {
    mutex_->Unlock();
  }

 private:
  Mutex* const mutex_;
  bool no_safepoint_scope_;

  DISALLOW_COPY_AND_ASSIGN(MutexLocker);
};

/*
 * Normal monitor locker :
 * This locker abstraction should only be used when the enclosing code can
 * not trigger a safepoint. In debug mode this class increments the
 * no_safepoint_scope_depth variable for the current thread when the lock is
 * taken and decrements it when the lock is released. NOTE: please do not use
 * the passed in mutex object independent of the locker class, For example the
 * code below will not assert correctly:
 *    {
 *      MonitorLocker ml(m);
 *      ....
 *      m->Exit();
 *      ....
 *      m->Enter();
 *      ...
 *    }
 * Always use the locker object even when the lock needs to be released
 * temporarily, e.g:
 *    {
 *      MonitorLocker ml(m);
 *      ....
 *      ml.Exit();
 *      ....
 *      ml.Enter();
 *      ...
 *    }
 */
class MonitorLocker : public ValueObject {
 public:
  explicit MonitorLocker(Monitor* monitor, bool no_safepoint_scope = true)
      : monitor_(monitor), no_safepoint_scope_(no_safepoint_scope) {
    ASSERT(monitor != NULL);
    monitor_->Enter();
  }

  virtual ~MonitorLocker() {
    monitor_->Exit();
  }

  void Enter() const {
    monitor_->Enter();
  }
  void Exit() const {
    monitor_->Exit();
  }

  void Wait() {
    monitor_->Wait();
  }

  Monitor::WaitResult WaitUntilNanos(int64_t deadline) {
    return monitor_->WaitUntilNanos(deadline);
  }

  void Notify() {
    monitor_->Notify();
  }

  void NotifyAll() {
    monitor_->NotifyAll();
  }

 private:
  Monitor* const monitor_;
  bool no_safepoint_scope_;

  DISALLOW_COPY_AND_ASSIGN(MonitorLocker);
};

}  // namespace psoup


#endif  // VM_LOCKERS_H_
