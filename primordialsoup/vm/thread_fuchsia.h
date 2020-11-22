// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_THREAD_FUCHSIA_H_
#define VM_THREAD_FUCHSIA_H_

#if !defined(VM_THREAD_H_)
#error Do not include thread_fuchsia.h directly; use thread.h instead.
#endif

#include <pthread.h>

#include "assert.h"
#include "globals.h"

namespace psoup {

typedef pthread_t ThreadId;
typedef pthread_t ThreadJoinId;

class MutexData {
 private:
  MutexData() {}
  ~MutexData() {}

  pthread_mutex_t* mutex() { return &mutex_; }

  pthread_mutex_t mutex_;

  friend class Mutex;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(MutexData);
};


class MonitorData {
 private:
  MonitorData() {}
  ~MonitorData() {}

  pthread_mutex_t* mutex() { return &mutex_; }
  pthread_cond_t* cond() { return &cond_; }

  pthread_mutex_t mutex_;
  pthread_cond_t cond_;

  friend class Monitor;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(MonitorData);
};

}  // namespace psoup

#endif  // VM_THREAD_FUCHSIA_H_
