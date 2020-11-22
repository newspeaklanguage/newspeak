// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "globals.h"
#if defined(OS_WINDOWS)

#include "os.h"

#include <malloc.h>
#include <process.h>
#include <time.h>

#include "assert.h"
#include "thread.h"

namespace psoup {


static int64_t qpc_ticks_per_second = 0;


static int64_t GetCurrentMonotonicTicks() {
  if (qpc_ticks_per_second == 0) {
    FATAL("QueryPerformanceCounter not supported");
  }
  // Grab performance counter value.
  LARGE_INTEGER now;
  QueryPerformanceCounter(&now);
  return static_cast<int64_t>(now.QuadPart);
}


static int64_t GetCurrentMonotonicFrequency() {
  if (qpc_ticks_per_second == 0) {
    FATAL("QueryPerformanceCounter not supported");
  }
  return qpc_ticks_per_second;
}


int64_t OS::CurrentMonotonicNanos() {
  int64_t ticks = GetCurrentMonotonicTicks();
  int64_t frequency = GetCurrentMonotonicFrequency();

  // Convert to microseconds.
  int64_t seconds = ticks / frequency;
  int64_t leftover_ticks = ticks - (seconds * frequency);
  int64_t result = seconds * kNanosecondsPerSecond;
  result += ((leftover_ticks * kNanosecondsPerSecond) / frequency);
  return result;
}


const char* OS::Name() { return "windows"; }


int OS::NumberOfAvailableProcessors() {
  SYSTEM_INFO info;
  GetSystemInfo(&info);
  return info.dwNumberOfProcessors;
}


void OS::DebugBreak() {
#if defined(_MSC_VER)
  // Microsoft Visual C/C++ or drop-in replacement.
  __debugbreak();
#elif defined(__GCC__)
  __builtin_trap();
#else
  // Microsoft style assembly.
  __asm {
    int 3
  }
#endif
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


static int VSNPrint(char* str, size_t size, const char* format, va_list args) {
  if (str == NULL || size == 0) {
    int retval = _vscprintf(format, args);
    if (retval < 0) {
      FATAL1("Fatal error in OS::VSNPrint with format '%s'", format);
    }
    return retval;
  }
  va_list args_copy;
  va_copy(args_copy, args);
  int written = _vsnprintf(str, size, format, args_copy);
  va_end(args_copy);
  if (written < 0) {
    // _vsnprintf returns -1 if the number of characters to be written is
    // larger than 'size', so we call _vscprintf which returns the number
    // of characters that would have been written.
    va_list args_retry;
    va_copy(args_retry, args);
    written = _vscprintf(format, args_retry);
    if (written < 0) {
      FATAL1("Fatal error in OS::VSNPrint with format '%s'", format);
    }
    va_end(args_retry);
  }
  // Make sure to zero-terminate the string if the output was
  // truncated or if there was an error.
  // The static cast is safe here as we have already determined that 'written'
  // is >= 0.
  if (static_cast<size_t>(written) >= size) {
    str[size - 1] = '\0';
  }
  return written;
}


char* OS::PrintStr(const char* format, ...) {
  va_list args;
  va_start(args, format);
  va_list measure_args;
  va_copy(measure_args, args);
  intptr_t len = VSNPrint(NULL, 0, format, measure_args);
  va_end(measure_args);

  char* buffer = reinterpret_cast<char*>(malloc(len + 1));

  va_list print_args;
  va_copy(print_args, args);
  int r = VSNPrint(buffer, len + 1, format, print_args);
  ASSERT(r >= 0);
  va_end(print_args);
  va_end(args);
  return buffer;
}


void OS::Startup() {
  // TODO(5411554): For now we check that initonce is called only once,
  // Once there is more formal mechanism to call Startup we can move
  // this check there.
  static bool init_once_called = false;
  ASSERT(init_once_called == false);
  init_once_called = true;
  // Do not pop up a message box when abort is called.
  _set_abort_behavior(0, _WRITE_ABORT_MSG);
  LARGE_INTEGER ticks_per_sec;
  if (!QueryPerformanceFrequency(&ticks_per_sec)) {
    qpc_ticks_per_second = 0;
  } else {
    qpc_ticks_per_second = static_cast<int64_t>(ticks_per_sec.QuadPart);
  }
}


void OS::Shutdown() {}


void OS::Abort() {
  abort();
}


void OS::Exit(int code) {
  // On Windows we use ExitProcess so that threads can't clobber the exit_code.
  // See: https://code.google.com/p/nativeclient/issues/detail?id=2870
  ::ExitProcess(code);
}

}  // namespace psoup

#endif  // defined(OS_WINDOWS)
