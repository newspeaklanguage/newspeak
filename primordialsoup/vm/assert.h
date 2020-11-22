// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_ASSERT_H_
#define VM_ASSERT_H_

#if !defined(DEBUG) && !defined(NDEBUG)
#error neither DEBUG nor NDEBUG defined
#elif defined(DEBUG) && defined(NDEBUG)
#error both DEBUG and NDEBUG defined
#endif

namespace psoup {

class Assert {
 public:
  Assert(const char* file, int line) : file_(file), line_(line) {}

    //NORETURN void Fail(const char* format, ...) PRINTF_ATTRIBUTE(2, 3);
    void Fail(const char* format, ...);

 private:
  const char* file_;
  int line_;
};

}  // namespace psoup

#define FATAL(error) psoup::Assert(__FILE__, __LINE__).Fail("%s", error)

#define FATAL1(format, p1) psoup::Assert(__FILE__, __LINE__).Fail(format, (p1))

#define FATAL2(format, p1, p2)                                                 \
  psoup::Assert(__FILE__, __LINE__).Fail(format, (p1), (p2))

#define UNIMPLEMENTED() FATAL("unimplemented code")

#define UNREACHABLE() FATAL("unreachable code")

#define OUT_OF_MEMORY() FATAL("Out of memory.")


#if defined(DEBUG)
// DEBUG binaries use assertions in the code.
// Note: We wrap the if statement in a do-while so that we get a compile
//       error if there is no semicolon after ASSERT(condition). This
//       ensures that we get the same behavior on DEBUG and RELEASE builds.

#define ASSERT(cond)                                                           \
  do {                                                                         \
    if (!(cond))                                                               \
        psoup::Assert(__FILE__, __LINE__).Fail("expected: %s", #cond);         \
  } while (false)

// DEBUG_ASSERT allows identifiers in condition to be undeclared in release
// mode.
#define DEBUG_ASSERT(cond) ASSERT(cond)

#else  // if defined(DEBUG)

// In order to avoid variable unused warnings for code that only uses
// a variable in an ASSERT or EXPECT, we make sure to use the macro
// argument.
#define ASSERT(condition)                                                      \
  do {                                                                         \
  } while (false && (condition))

#define DEBUG_ASSERT(cond)

#endif  // if defined(DEBUG)

#if !defined(COMPILE_ASSERT)
template <bool>
struct CompileAssert {
};
#define COMPILE_ASSERT_JOIN(a, b) COMPILE_ASSERT_JOIN_HELPER(a, b)
#define COMPILE_ASSERT_JOIN_HELPER(a, b) a##b
#define COMPILE_ASSERT(expr)                                                   \
  ATTRIBUTE_UNUSED typedef CompileAssert<(static_cast<bool>(expr))>            \
  COMPILE_ASSERT_JOIN(CompileAssertTypeDef, __LINE__)[static_cast<bool>(expr)  \
  ? 1 : -1]
#endif  // !defined(COMPILE_ASSERT)

#endif  // VM_ASSERT_H_
