// Copyright (c) 2019, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_THREAD_EMSCRIPTEN_H_
#define VM_THREAD_EMSCRIPTEN_H_

#if !defined(VM_THREAD_H_)
#error Do not include thread_emscripten.h directly; use thread.h instead.
#endif

#include "assert.h"
#include "globals.h"

namespace psoup {

typedef intptr_t ThreadId;
typedef intptr_t ThreadJoinId;

class MutexData {
 private:
  MutexData() {}
  ~MutexData() {}

  friend class Mutex;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(MutexData);
};


class MonitorData {
 private:
  MonitorData() {}
  ~MonitorData() {}

  friend class Monitor;

  DISALLOW_ALLOCATION();
  DISALLOW_COPY_AND_ASSIGN(MonitorData);
};

}  // namespace psoup

#endif  // VM_THREAD_EMSCRIPTEN_H_
