// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_THREAD_WIN_H_
#define VM_THREAD_WIN_H_

#if !defined(VM_THREAD_H_)
#error Do not include thread_win.h directly; use thread.h instead.
#endif

#include "assert.h"
#include "globals.h"

namespace psoup {

typedef DWORD ThreadId;
typedef HANDLE ThreadJoinId;

class MutexData {
 private:
  MutexData() {}
  ~MutexData() {}

  SRWLOCK lock_;

  friend class Mutex;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(MutexData);
};


class MonitorData {
 private:
  MonitorData() {}
  ~MonitorData() {}

  SRWLOCK lock_;
  CONDITION_VARIABLE cond_;

  friend class Monitor;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(MonitorData);
};

}  // namespace psoup

#endif  // VM_THREAD_WIN_H_
