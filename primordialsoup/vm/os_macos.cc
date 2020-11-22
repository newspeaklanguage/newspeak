// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if defined(OS_MACOS)

#include "os.h"

#include <errno.h>
#include <mach/mach_time.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "assert.h"

namespace psoup {

static mach_timebase_info_data_t timebase_info;


void OS::Startup() {
  kern_return_t kr = mach_timebase_info(&timebase_info);
  ASSERT(KERN_SUCCESS == kr);
}


void OS::Shutdown() {}


int64_t OS::CurrentMonotonicNanos() {
  ASSERT(timebase_info.denom != 0);
  // timebase_info converts absolute time tick units into nanoseconds.
  int64_t result = mach_absolute_time();
  result *= timebase_info.numer;
  result /= timebase_info.denom;
  return result;
}


const char* OS::Name() { return "macos"; }


int OS::NumberOfAvailableProcessors() {
  return sysconf(_SC_NPROCESSORS_ONLN);
}


void OS::DebugBreak() {
  __builtin_trap();
}


static void VFPrint(FILE* stream, const char* format, va_list args) {
  vfprintf(stream, format, args);
  fflush(stream);
}

void OS::Print(const char* format, ...) {
  va_list args;
  va_start(args, format);
  VFPrint(stdout, format, args);
  va_end(args);
}


void OS::PrintErr(const char* format, ...) {
  va_list args;
  va_start(args, format);
  VFPrint(stderr, format, args);
  va_end(args);
}


char* OS::PrintStr(const char* format, ...) {
  va_list args;
  va_start(args, format);
  va_list measure_args;
  va_copy(measure_args, args);
  intptr_t len = vsnprintf(NULL, 0, format, measure_args);
  va_end(measure_args);

  char* buffer = reinterpret_cast<char*>(malloc(len + 1));

  va_list print_args;
  va_copy(print_args, args);
  int r = vsnprintf(buffer, len + 1, format, print_args);
  ASSERT(r >= 0);
  va_end(print_args);
  va_end(args);
  return buffer;
}


void OS::Abort() {
  abort();
}


void OS::Exit(int code) {
  exit(code);
}

}  // namespace psoup

#endif  // __APPLE__
