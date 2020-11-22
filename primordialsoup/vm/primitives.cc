// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "primitives.h"

#ifdef __APPLE__
#include <cmath>
#else
#include <math.h>
#endif

#include <sys/stat.h>

#if defined(OS_FUCHSIA)
#include <zircon/status.h>
#include <zircon/syscalls.h>
#elif defined(OS_EMSCRIPTEN)
#include <emscripten.h>
#endif

#include "assert.h"
#include "double_conversion.h"
#include "heap.h"
#include "interpreter.h"
#include "isolate.h"
#include "math-vm.h"
#include "message_loop.h"
#include "object.h"
#include "os.h"

#define nil I->nil_obj()

namespace psoup {

const bool kSuccess = true;
const bool kFailure = false;

// TODO(rmacnak): Re-group the primitives and re-assign their numbers once the
// set of primitives is more stable.

#define PRIMITIVE_LIST(V)                                                      \
  V(1, Number_add)                                                             \
  V(2, Number_subtract)                                                        \
  V(3, Number_multiply)                                                        \
  V(4, Number_divide)                                                          \
  V(5, Number_div)                                                             \
  V(6, Number_mod)                                                             \
  V(7, Number_quo)                                                             \
  V(8, Number_rem)                                                             \
  V(9, Number_equal)                                                           \
  V(10, Number_less)                                                           \
  V(11, Number_greater)                                                        \
  V(12, Number_lessOrEqual)                                                    \
  V(13, Number_greaterOrEqual)                                                 \
  V(14, Number_asInteger)                                                      \
  V(15, Number_asDouble)                                                       \
  V(16, Integer_bitAnd)                                                        \
  V(17, Integer_bitOr)                                                         \
  V(18, Integer_bitXor)                                                        \
  V(19, Integer_bitShiftLeft)                                                  \
  V(20, Integer_bitShiftRight)                                                 \
  V(21, Double_floor)                                                          \
  V(22, Double_ceiling)                                                        \
  V(23, Double_sin)                                                            \
  V(24, Double_cos)                                                            \
  V(25, Double_tan)                                                            \
  V(26, Double_asin)                                                           \
  V(27, Double_acos)                                                           \
  V(28, Double_atan)                                                           \
  V(29, Double_atan2)                                                          \
  V(30, Double_exp)                                                            \
  V(31, Double_ln)                                                             \
  V(32, Double_log)                                                            \
  V(33, Double_sqrt)                                                           \
  V(34, Behavior_basicNew)                                                     \
  V(35, Object_instVarAt)                                                      \
  V(36, Object_instVarAtPut)                                                   \
  V(37, Object_instVarSize)                                                    \
  V(38, Array_class_new)                                                       \
  V(39, Array_at)                                                              \
  V(40, Array_atPut)                                                           \
  V(41, Array_size)                                                            \
  V(42, WeakArray_class_new)                                                   \
  V(43, WeakArray_at)                                                          \
  V(44, WeakArray_atPut)                                                       \
  V(45, WeakArray_size)                                                        \
  V(46, ByteArray_class_new)                                                   \
  V(47, ByteArray_at)                                                          \
  V(48, ByteArray_atPut)                                                       \
  V(49, ByteArray_size)                                                        \
  V(50, Bytes_copyByteArrayFromTo)                                             \
  V(51, String_at)                                                             \
  V(53, String_size)                                                           \
  V(54, String_hash)                                                           \
  V(55, Activation_sender)                                                     \
  V(56, Activation_senderPut)                                                  \
  V(57, Activation_bci)                                                        \
  V(58, Activation_bciPut)                                                     \
  V(59, Activation_method)                                                     \
  V(60, Activation_methodPut)                                                  \
  V(61, Activation_closure)                                                    \
  V(62, Activation_closurePut)                                                 \
  V(63, Activation_receiver)                                                   \
  V(64, Activation_receiverPut)                                                \
  V(65, Activation_tempAt)                                                     \
  V(66, Activation_tempAtPut)                                                  \
  V(67, Activation_tempSize)                                                   \
  V(68, Activation_class_new)                                                  \
  V(69, Closure_class_new)                                                     \
  V(70, Closure_numCopied)                                                     \
  V(71, Closure_definingActivation)                                            \
  V(72, Closure_definingActivationPut)                                         \
  V(73, Closure_initialBci)                                                    \
  V(74, Closure_initialBciPut)                                                 \
  V(75, Closure_numArgs)                                                       \
  V(76, Closure_numArgsPut)                                                    \
  V(77, Closure_copiedAt)                                                      \
  V(78, Closure_copiedAtPut)                                                   \
  V(79, ByteArray_replaceFromToWithStartingAt)                                 \
  V(80, Array_replaceFromToWithStartingAt)                                     \
  V(81, Array_copyFromTo)                                                      \
  V(85, Object_class)                                                          \
  V(86, Object_identical)                                                      \
  V(87, Object_identityHash)                                                   \
  V(89, Object_performWithAll)                                                 \
  V(90, Closure_value0)                                                        \
  V(91, Closure_value1)                                                        \
  V(92, Closure_value2)                                                        \
  V(93, Closure_value3)                                                        \
  V(94, Closure_valueArray)                                                    \
  V(95, Activation_jump)                                                       \
  V(96, Behavior_allInstances)                                                 \
  V(98, Array_elementsForwardIdentity)                                         \
  V(99, Platform_operatingSystem)                                              \
  V(100, Time_monotonicNanos)                                                  \
  V(101, Time_utcEpochNanos)                                                   \
  V(102, print)                                                                \
  V(103, panic)                                                                \
  V(104, flushCache)                                                           \
  V(105, collectGarbage)                                                       \
  V(106, Double_isFinite)                                                      \
  V(107, MessageLoop_exit)                                                     \
  V(108, Double_asStringFixed)                                                 \
  V(109, Double_asStringExponential)                                           \
  V(110, Double_asStringPrecision)                                             \
  V(111, Number_asString)                                                      \
  V(112, Double_isInfinite)                                                    \
  V(113, Closure_ensure)                                                       \
  V(114, String_equals)                                                        \
  V(115, String_concat)                                                        \
  V(116, Closure_onDo)                                                         \
  V(117, Bytes_startsWith)                                                     \
  V(118, Bytes_endsWith)                                                       \
  V(119, Bytes_indexOf)                                                        \
  V(120, Bytes_lastIndexOf)                                                    \
  V(121, Bytes_copyStringFromTo)                                               \
  V(122, ByteArray_class_withAll)                                              \
  V(123, String_class_with)                                                    \
  V(124, String_class_withAll)                                                 \
  V(125, Double_rounded)                                                       \
  V(126, Object_isCanonical)                                                   \
  V(127, Object_markCanonical)                                                 \
  V(128, writeBytesToFile)                                                     \
  V(130, readFileAsBytes)                                                      \
  V(131, Double_pow)                                                           \
  V(132, Double_class_parse)                                                   \
  V(133, currentActivation)                                                    \
  V(134, Behavior_adoptInstance)                                               \
  V(135, openPort)                                                             \
  V(136, closePort)                                                            \
  V(137, spawn)                                                                \
  V(138, send)                                                                 \
  V(139, MessageLoop_finish)                                                   \
  V(140, Activation_tempSizePut)                                               \
  V(141, doPrimitiveWithArgs)                                                  \
  V(142, simulationRoot)                                                       \
  V(143, MessageLoop_awaitSignal)                                              \
  V(144, MessageLoop_cancelSignalWait)                                         \
  V(145, ZXHandle_close)                                                       \
  V(146, ZXChannel_create)                                                     \
  V(147, ZXChannel_read)                                                       \
  V(148, ZXChannel_write)                                                      \
  V(149, ZXVmo_create)                                                         \
  V(150, ZXVmo_getSize)                                                        \
  V(151, ZXVmo_setSize)                                                        \
  V(152, ZXVmo_read)                                                           \
  V(153, ZXVmo_write)                                                          \
  V(154, JS_pushValue)                                                         \
  V(155, JS_pushAlien)                                                         \
  V(156, JS_pushExpat)                                                         \
  V(157, JS_popValue)                                                          \
  V(158, JS_peekAlien)                                                         \
  V(159, JS_peekExpat)                                                         \
  V(160, JS_performGet)                                                        \
  V(161, JS_performSet)                                                        \
  V(162, JS_performDelete)                                                     \
  V(163, JS_performInvoke)                                                     \
  V(164, JS_performNew)                                                        \
  V(165, ZXStatus_getString)                                                   \
  V(166, JS_performInstanceOf)                                                 \
  V(167, JS_performHas)                                                        \
  V(200, quickReturnSelf)                                                      \


#define DEFINE_PRIMITIVE(name)                                                 \
  static bool primitive##name(intptr_t num_args, Heap* H, Interpreter* I)

#define IS_SMI_OP(left, right)                                                 \
  left->IsSmallInteger() && right->IsSmallInteger()                            \

#define IS_MINT_OP(left, right)                                                \
  (left->IsSmallInteger() || left->IsMediumInteger()) &&                       \
  (right->IsSmallInteger() || right->IsMediumInteger())                        \

#define IS_LINT_OP(left, right)                                                \
  (left->IsSmallInteger() ||                                                   \
    left->IsMediumInteger() ||                                                 \
    left->IsLargeInteger()) &&                                                 \
  (right->IsSmallInteger() ||                                                  \
    right->IsMediumInteger() ||                                                \
    right->IsLargeInteger())                                                   \

#define IS_FLOAT_OP(left, right)                                               \
  (left->IsFloat64() || right->IsFloat64())                                    \

#define SMI_VALUE(integer)                                                     \
  static_cast<SmallInteger>(integer)->value()                                  \

#define MINT_VALUE(integer)                                                    \
  (integer->IsSmallInteger()                                                   \
     ? static_cast<SmallInteger>(integer)->value()                             \
     : static_cast<MediumInteger>(integer)->value())                           \

#define LINT_VALUES                                                            \
  LargeInteger large_left;                                                     \
  LargeInteger large_right;                                                    \
  {                                                                            \
    HandleScope h1(H, reinterpret_cast<Object*>(&right));                      \
    large_left = LargeInteger::Expand(left, H);                                \
    HandleScope h2(H, reinterpret_cast<Object*>(&large_left));                 \
    large_right = LargeInteger::Expand(right, H);                              \
  }                                                                            \

#define FLOAT_VALUE(raw_float, number)                                         \
  if (number->IsSmallInteger()) {                                              \
    raw_float = static_cast<SmallInteger>(number)->value();                    \
  } else if (number->IsMediumInteger()) {                                      \
    raw_float = static_cast<MediumInteger>(number)->value();                   \
  } else if (number->IsFloat64()) {                                            \
    raw_float = static_cast<Float64>(number)->value();                         \
  } else if (number->IsLargeInteger()) {                                       \
    raw_float = LargeInteger::AsDouble(static_cast<LargeInteger>(number));     \
  } else {                                                                     \
    return kFailure;                                                           \
  }                                                                            \

#define FLOAT_VALUE_OR_FALSE(raw_float, number)                                \
  if (number->IsSmallInteger()) {                                              \
    raw_float = static_cast<SmallInteger>(number)->value();                    \
  } else if (number->IsMediumInteger()) {                                      \
    raw_float = static_cast<MediumInteger>(number)->value();                   \
  } else if (number->IsFloat64()) {                                            \
    raw_float = static_cast<Float64>(number)->value();                         \
  } else if (number->IsLargeInteger()) {                                       \
    raw_float = LargeInteger::AsDouble(static_cast<LargeInteger>(number));     \
  } else {                                                                     \
    RETURN_BOOL(false);                                                        \
  }                                                                            \

#define SMI_ARGUMENT(name, index)                                              \
  intptr_t name;                                                               \
  if (I->Stack(index)->IsSmallInteger()) {                                     \
    name = static_cast<SmallInteger>(I->Stack(index))->value();                \
  } else {                                                                     \
    return kFailure;                                                           \
  }                                                                            \

#define MINT_ARGUMENT(name, index)                                             \
  int64_t name;                                                                \
  if (I->Stack(index)->IsSmallInteger()) {                                     \
    name = static_cast<SmallInteger>(I->Stack(index))->value();                \
  } else if (I->Stack(index)->IsMediumInteger()) {                             \
    name = static_cast<MediumInteger>(I->Stack(index))->value();               \
  } else {                                                                     \
    return kFailure;                                                           \
  }                                                                            \

#define FLOAT_ARGUMENT(name, index)                                            \
  double name;                                                                 \
  if (I->Stack(index)->IsFloat64()) {                                          \
    name = static_cast<Float64>(I->Stack(index))->value();                     \
  } else {                                                                     \
    return kFailure;                                                           \
  }                                                                            \

#define RETURN_SELF()                                                          \
  I->Drop(num_args);                                                           \
  return kSuccess;                                                             \

#define RETURN(result)                                                         \
  I->PopNAndPush(num_args + 1, result);                                        \
  return kSuccess;                                                             \

#define RETURN_SMI(raw_integer)                                                \
  ASSERT(SmallInteger::IsSmiValue(raw_integer));                               \
  RETURN(SmallInteger::New(raw_integer));                                      \

#define RETURN_MINT(raw_integer)                                               \
  if (SmallInteger::IsSmiValue(raw_integer)) {                                 \
    RETURN(SmallInteger::New(raw_integer));                                    \
  } else {                                                                     \
    MediumInteger result = H->AllocateMediumInteger();                         \
    result->set_value(raw_integer);                                            \
    RETURN(result);                                                            \
  }                                                                            \

#define RETURN_LINT(large_integer)                                             \
  RETURN(LargeInteger::Reduce(large_integer, H));                              \

#define RETURN_FLOAT(raw_float)                                                \
  Float64 result = H->AllocateFloat64();                                       \
  result->set_value(raw_float);                                                \
  RETURN(result);                                                              \

#define RETURN_BOOL(raw_bool)                                                  \
  RETURN((raw_bool) ? I->true_obj() : I->false_obj());                         \


DEFINE_PRIMITIVE(Unimplemented) {
  UNIMPLEMENTED();
  return kFailure;
}


DEFINE_PRIMITIVE(Number_add) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    intptr_t raw_result = raw_left + raw_right;  // Cannot overflow.
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    int64_t raw_result;
    if (Math::AddHasOverflow64(raw_left, raw_right, &raw_result)) {
      // Fall through to large integer operation.
    } else {
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    LargeInteger large_result = LargeInteger::Add(large_left, large_right, H);
    RETURN_LINT(large_result);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    double raw_result = raw_left + raw_right;
    RETURN_FLOAT(raw_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_subtract) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    intptr_t raw_result = raw_left - raw_right;  // Cannot overflow.
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    int64_t raw_result;
    if (Math::SubtractHasOverflow64(raw_left, raw_right, &raw_result)) {
      // Fall through to large integer operation.
    } else {
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    LargeInteger large_result =
        LargeInteger::Subtract(large_left, large_right, H);
    RETURN_LINT(large_result);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    double raw_result = raw_left - raw_right;
    RETURN_FLOAT(raw_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_multiply) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
#if defined(ARCH_IS_32_BIT)
    int64_t raw_left = SMI_VALUE(left);
    int64_t raw_right = SMI_VALUE(right);
    int64_t raw_result = raw_left * raw_right;  // Cannot overflow.
    RETURN_MINT(raw_result);
#elif defined(ARCH_IS_64_BIT)
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    intptr_t raw_result;
    if (Math::MultiplyHasOverflow(raw_left, raw_right, &raw_result)) {
      // Fall through to large integer operation.
    } else {
      RETURN_MINT(raw_result);
    }
#else
#error Unimplemented
#endif
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    int64_t raw_result;
    if (Math::MultiplyHasOverflow64(raw_left, raw_right, &raw_result)) {
      // Fall through to large integer operation.
    } else {
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    LargeInteger large_result =
        LargeInteger::Multiply(large_left, large_right, H);
    RETURN_LINT(large_result);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    double raw_result = raw_left * raw_right;
    RETURN_FLOAT(raw_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_divide) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    if ((raw_left % raw_right) != 0) {
      return kFailure;  // Inexact division.
    }
    intptr_t raw_result = raw_left / raw_right;
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    if ((raw_right == -1) && (raw_left == kMinInt64)) {
      // Overflow. Fall through to large integer operation.
    } else {
      if ((raw_left % raw_right) != 0) {
        return kFailure;  // Inexact division.
      }
      int64_t raw_result = raw_left / raw_right;
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    if (large_right->size() == 0) {
      return kFailure;  // Division by zero.
    }
    LargeInteger large_result = LargeInteger::Divide(LargeInteger::kExact,
                                                     LargeInteger::kQuoitent,
                                                     large_left,
                                                     large_right, H);
    if (large_result == nullptr) {
      return kFailure;  // Inexact division.
    }
    RETURN_LINT(large_result);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    double raw_result = Math::DivideF64(raw_left, raw_right);
    RETURN_FLOAT(raw_result);
  }

  return kFailure;
}

DEFINE_PRIMITIVE(Number_div) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    intptr_t raw_result = Math::FloorDiv(raw_left, raw_right);
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    if ((raw_right == -1) && (raw_left == kMinInt64)) {
      // Overflow. Fall through to large integer operation.
    } else {
      int64_t raw_result = Math::FloorDiv64(raw_left, raw_right);
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    if (large_right->size() == 0) {
      return kFailure;  // Division by zero.
    }
    LargeInteger large_result = LargeInteger::Divide(LargeInteger::kFloored,
                                                     LargeInteger::kQuoitent,
                                                     large_left,
                                                     large_right, H);
    RETURN_LINT(large_result);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    // TODO(rmacnak): Return result as float or integer?
    //double raw_result = floor(raw_left / raw_right);
    RETURN_FLOAT(0);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_mod) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    intptr_t raw_result = Math::FloorMod(raw_left, raw_right);
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    if ((raw_right == -1) && (raw_left == kMinInt64)) {
      // Overflow. Fall through to large integer operation.
    } else {
      int64_t raw_result = Math::FloorMod64(raw_left, raw_right);
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    if (large_right->size() == 0) {
      return kFailure;  // Division by zero.
    }
    LargeInteger large_result = LargeInteger::Divide(LargeInteger::kFloored,
                                                     LargeInteger::kRemainder,
                                                     large_left,
                                                     large_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_quo) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    intptr_t raw_result = Math::TruncDiv(raw_left, raw_right);
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    if ((raw_right == -1) && (raw_left == kMinInt64)) {
      // Overflow. Fall through to large integer operation.
    } else {
      int64_t raw_result = Math::TruncDiv64(raw_left, raw_right);
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    if (large_right->size() == 0) {
      return kFailure;  // Division by zero.
    }
    LargeInteger large_result = LargeInteger::Divide(LargeInteger::kTruncated,
                                                     LargeInteger::kQuoitent,
                                                     large_left,
                                                     large_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_rem) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    intptr_t raw_result = Math::TruncMod(raw_left, raw_right);
    RETURN_MINT(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right == 0) {
      return kFailure;  // Division by zero.
    }
    if ((raw_right == -1) && (raw_left == kMinInt64)) {
      // Overflow. Fall through to large integer operation.
    } else {
      int64_t raw_result = Math::TruncMod64(raw_left, raw_right);
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    if (large_right->size() == 0) {
      return kFailure;  // Division by zero.
    }
    LargeInteger large_result = LargeInteger::Divide(LargeInteger::kTruncated,
                                                     LargeInteger::kRemainder,
                                                     large_left,
                                                     large_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_equal) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    RETURN_BOOL(raw_left == raw_right);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    RETURN_BOOL(raw_left == raw_right);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    RETURN_BOOL(LargeInteger::Compare(large_left, large_right) == 0);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE_OR_FALSE(raw_right, right);
    RETURN_BOOL(raw_left == raw_right);
  }

  RETURN_BOOL(false);
}


DEFINE_PRIMITIVE(Number_less) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    RETURN_BOOL(raw_left < raw_right);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    RETURN_BOOL(raw_left < raw_right);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    RETURN_BOOL(LargeInteger::Compare(large_left, large_right) > 0);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    RETURN_BOOL(raw_left < raw_right);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_greater) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    RETURN_BOOL(raw_left > raw_right);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    RETURN_BOOL(raw_left > raw_right);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    RETURN_BOOL(LargeInteger::Compare(large_left, large_right) < 0);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    RETURN_BOOL(raw_left > raw_right);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_lessOrEqual) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    RETURN_BOOL(raw_left <= raw_right);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    RETURN_BOOL(raw_left <= raw_right);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    RETURN_BOOL(LargeInteger::Compare(large_left, large_right) >= 0);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    RETURN_BOOL(raw_left <= raw_right);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_greaterOrEqual) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    RETURN_BOOL(raw_left >= raw_right);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    RETURN_BOOL(raw_left >= raw_right);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    RETURN_BOOL(LargeInteger::Compare(large_left, large_right) <= 0);
  }

  if (IS_FLOAT_OP(left, right)) {
    double raw_left, raw_right;
    FLOAT_VALUE(raw_left, left);
    FLOAT_VALUE(raw_right, right);
    RETURN_BOOL(raw_left >= raw_right);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Number_asInteger) {
  ASSERT(num_args == 0);
  Object receiver = I->Stack(0);
  if (receiver->IsFloat64()) {
    double raw_receiver = static_cast<Float64>(receiver)->value();
    Object result;
    if (LargeInteger::FromDouble(raw_receiver, &result, H)) {
      RETURN(result);
    } else {
      return kFailure;
    }
  }
  UNIMPLEMENTED();
  return kFailure;
}


DEFINE_PRIMITIVE(Number_asDouble) {
  ASSERT(num_args == 0);
  Object receiver = I->Stack(0);
  if (receiver->IsSmallInteger()) {
    intptr_t raw_receiver = static_cast<SmallInteger>(receiver)->value();
    RETURN_FLOAT(static_cast<double>(raw_receiver));
  }
  if (receiver->IsMediumInteger()) {
    int64_t raw_receiver = static_cast<MediumInteger>(receiver)->value();
    RETURN_FLOAT(static_cast<double>(raw_receiver));
  }
  if (receiver->IsLargeInteger()) {
    RETURN_FLOAT(LargeInteger::AsDouble(static_cast<LargeInteger>(receiver)));
  }
  UNIMPLEMENTED();
  return kFailure;
}


DEFINE_PRIMITIVE(Integer_bitAnd) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    intptr_t raw_result = raw_left & raw_right;
    RETURN_SMI(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    int64_t raw_result = raw_left & raw_right;
    RETURN_MINT(raw_result);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    LargeInteger large_result = LargeInteger::And(large_left, large_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Integer_bitOr) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    intptr_t raw_result = raw_left | raw_right;
    RETURN_SMI(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    int64_t raw_result = raw_left | raw_right;
    RETURN_MINT(raw_result);  // In fact, we know it can't be Smi.
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    LargeInteger large_result = LargeInteger::Or(large_left, large_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Integer_bitXor) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    intptr_t raw_result = raw_left ^ raw_right;
    RETURN_SMI(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    int64_t raw_result = raw_left ^ raw_right;
    RETURN_MINT(raw_result);
  }

  if (IS_LINT_OP(left, right)) {
    LINT_VALUES;
    LargeInteger large_result = LargeInteger::Xor(large_left, large_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Integer_bitShiftLeft) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right < 0) {
      return kFailure;
    }
    // bit length is for wrong size
    if (Utils::BitLength(raw_left) + raw_right < SmallInteger::kBits) {
      intptr_t raw_result = Math::ShiftLeft(raw_left, raw_right);
      ASSERT((raw_result >> raw_right) == raw_left);
      RETURN_SMI(raw_result);
    }
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right < 0) {
      return kFailure;
    }
    if (Utils::BitLength(raw_left) <= (63 - raw_right)) {
      int64_t raw_result = Math::ShiftLeft64(raw_left, raw_right);
      ASSERT(raw_result >> raw_right == raw_left);
      RETURN_MINT(raw_result);
    }
  }

  if (IS_LINT_OP(left, right)) {
    LargeInteger large_left = LargeInteger::Expand(left, H);
    right = I->Stack(0);
    if (right->IsLargeInteger()) {
      if (static_cast<LargeInteger>(right)->negative()) {
        return kFailure;
      }
      OUT_OF_MEMORY();
    }
    if (right->IsMediumInteger()) {
      int64_t raw_right = MINT_VALUE(right);
      if (raw_right < 0) {
        return kFailure;
      }
      OUT_OF_MEMORY();
    }
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right < 0) {
      return kFailure;
    }
    LargeInteger large_result =
        LargeInteger::ShiftLeft(large_left, raw_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


DEFINE_PRIMITIVE(Integer_bitShiftRight) {
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  if (IS_SMI_OP(left, right)) {
    intptr_t raw_left = SMI_VALUE(left);
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right < 0) {
      return kFailure;
    }
    if (raw_right > SmallInteger::kBits) {
      raw_right = SmallInteger::kBits;
    }
    intptr_t raw_result = raw_left >> raw_right;
    RETURN_SMI(raw_result);
  }

  if (IS_MINT_OP(left, right)) {
    int64_t raw_left = MINT_VALUE(left);
    int64_t raw_right = MINT_VALUE(right);
    if (raw_right < 0) {
      return kFailure;
    }
    if (raw_right > 63) {
      raw_right = 63;
    }
    int64_t raw_result = raw_left >> raw_right;
    RETURN_MINT(raw_result);
  }

  if (IS_LINT_OP(left, right)) {
    LargeInteger large_left = LargeInteger::Expand(left, H);
    right = I->Stack(0);
    if (right->IsLargeInteger()) {
      if (static_cast<LargeInteger>(right)->negative()) {
        return kFailure;
      }
      // Shift leaves only sign bit.
      intptr_t raw_result = large_left->negative() ? -1 : 0;
      RETURN_SMI(raw_result);
    }
    if (right->IsMediumInteger()) {
      int64_t raw_right = MINT_VALUE(right);
      if (raw_right < 0) {
        return kFailure;
      }
      // Shift leaves only sign bit.
      intptr_t raw_result = large_left->negative() ? -1 : 0;
      RETURN_SMI(raw_result);
    }
    intptr_t raw_right = SMI_VALUE(right);
    if (raw_right < 0) {
      return kFailure;
    }
    intptr_t left_bits = large_left->size() * sizeof(digit_t) * kBitsPerByte;
    if (raw_right >= left_bits) {
      intptr_t raw_result = large_left->negative() ? -1 : 0;
      RETURN_SMI(raw_result);
    }

    LargeInteger large_result =
        LargeInteger::ShiftRight(large_left, raw_right, H);
    RETURN_LINT(large_result);
  }

  return kFailure;
}


#define FLOAT_FUNCTION_1(func)                                  \
  ASSERT(num_args == 0);                                        \
  Float64 rcvr = static_cast<Float64>(I->Stack(0));             \
  if (!rcvr->IsFloat64()) {                                     \
    return kFailure;                                            \
  }                                                             \
  RETURN_FLOAT(func(rcvr->value()));                            \


#define FLOAT_FUNCTION_2(func)                                  \
  ASSERT(num_args == 1);                                        \
  Float64 rcvr = static_cast<Float64>(I->Stack(1));             \
  Float64 arg = static_cast<Float64>(I->Stack(0));              \
  if (!rcvr->IsFloat64()) {                                     \
    return kFailure;                                            \
  }                                                             \
  if (!arg->IsFloat64()) {                                      \
    return kFailure;                                            \
  }                                                             \
  RETURN_FLOAT(func(rcvr->value(), arg->value()));              \


DEFINE_PRIMITIVE(Double_floor) { FLOAT_FUNCTION_1(floor); }
DEFINE_PRIMITIVE(Double_ceiling) { FLOAT_FUNCTION_1(ceil); }
DEFINE_PRIMITIVE(Double_rounded) { FLOAT_FUNCTION_1(round); }
DEFINE_PRIMITIVE(Double_sin) { FLOAT_FUNCTION_1(sin); }
DEFINE_PRIMITIVE(Double_cos) { FLOAT_FUNCTION_1(cos); }
DEFINE_PRIMITIVE(Double_tan) { FLOAT_FUNCTION_1(tan); }
DEFINE_PRIMITIVE(Double_asin) { FLOAT_FUNCTION_1(asin); }
DEFINE_PRIMITIVE(Double_acos) { FLOAT_FUNCTION_1(acos); }
DEFINE_PRIMITIVE(Double_atan) { FLOAT_FUNCTION_1(atan); }
DEFINE_PRIMITIVE(Double_atan2) { FLOAT_FUNCTION_2(atan2); }
DEFINE_PRIMITIVE(Double_exp) { FLOAT_FUNCTION_1(exp); }
DEFINE_PRIMITIVE(Double_ln) { FLOAT_FUNCTION_1(log); }
DEFINE_PRIMITIVE(Double_log) { FLOAT_FUNCTION_1(log10); }
DEFINE_PRIMITIVE(Double_sqrt) { FLOAT_FUNCTION_1(sqrt); }
DEFINE_PRIMITIVE(Double_pow) { FLOAT_FUNCTION_2(pow); }

DEFINE_PRIMITIVE(Double_isFinite) {
  ASSERT(num_args == 0);
  FLOAT_ARGUMENT(rcvr, 0);
  RETURN_BOOL(isfinite(rcvr));
}

DEFINE_PRIMITIVE(Double_isInfinite) {
  ASSERT(num_args == 0);
  FLOAT_ARGUMENT(rcvr, 0);
  RETURN_BOOL(isinf(rcvr));
}

DEFINE_PRIMITIVE(Behavior_basicNew) {
  ASSERT((num_args == 0) || (num_args == 1));

  Behavior behavior = static_cast<Behavior>(I->Stack(0));
  ASSERT(behavior->IsRegularObject());
  behavior->AssertCouldBeBehavior();
  SmallInteger id = behavior->id();
  if (id == nil) {
    id = SmallInteger::New(H->AllocateClassId());  // SAFEPOINT
    behavior = static_cast<Behavior>(I->Stack(0));
    behavior->set_id(id);
    H->RegisterClass(id->value(), behavior);
  }
  ASSERT(id->IsSmallInteger());
  ASSERT(H->ClassAt(id->value()) == behavior);
  SmallInteger format = behavior->format();
  ASSERT(format->IsSmallInteger());
  intptr_t num_slots = format->value();
  ASSERT(num_slots >= 0);
  ASSERT(num_slots < 255);

  RegularObject new_instance = H->AllocateRegularObject(id->value(),
                                                         num_slots);
  for (intptr_t i = 0; i < num_slots; i++) {
    new_instance->set_slot(i, nil, kNoBarrier);
  }
  RETURN(new_instance);
}


DEFINE_PRIMITIVE(Object_instVarAt) {
  ASSERT(num_args == 2);  // Always a mirror primitive.
  RegularObject object = static_cast<RegularObject>(I->Stack(1));
  if (!object->IsRegularObject() && !object->IsEphemeron()) {
    return kFailure;
  }
  SMI_ARGUMENT(index, 0);
  if ((index <= 0) || (index > object->Klass(H)->format()->value())) {
    return kFailure;
  }
  RETURN(object->slot(index - 1));
}


DEFINE_PRIMITIVE(Object_instVarAtPut) {
  ASSERT(num_args == 3);  // Always a mirror primitive.
  RegularObject object = static_cast<RegularObject>(I->Stack(2));
  if (!object->IsRegularObject() && !object->IsEphemeron()) {
    return kFailure;
  }
  SMI_ARGUMENT(index, 1);
  if ((index <= 0) || (index > object->Klass(H)->format()->value())) {
    return kFailure;
  }
  Object value = I->Stack(0);
  object->set_slot(index - 1, value);
  RETURN(value);
}


DEFINE_PRIMITIVE(Object_instVarSize) { UNIMPLEMENTED(); return kSuccess; }


DEFINE_PRIMITIVE(Array_class_new) {
  ASSERT(num_args == 1);
  SMI_ARGUMENT(length, 0);
  if (length < 0) {
    return kFailure;
  }
  Array result = H->AllocateArray(length);  // SAFEPOINT
  for (intptr_t i = 0; i < length; i++) {
    result->set_element(i, nil, kNoBarrier);
  }
  RETURN(result);
}


DEFINE_PRIMITIVE(Array_at) {
  ASSERT(num_args == 1);
  Array array = static_cast<Array>(I->Stack(1));
  ASSERT(array->IsArray());
  SMI_ARGUMENT(index, 0);
  index--;
  if ((index < 0) || (index >= array->Size())) {
    return kFailure;
  }
  RETURN(array->element(index));
}


DEFINE_PRIMITIVE(Array_atPut) {
  ASSERT(num_args == 2);
  Array array = static_cast<Array>(I->Stack(2));
  ASSERT(array->IsArray());
  SMI_ARGUMENT(index, 1);
  index--;
  if ((index < 0) || (index >= array->Size())) {
    return kFailure;
  }
  Object value = I->Stack(0);
  array->set_element(index, value);
  RETURN(value);
}


DEFINE_PRIMITIVE(Array_size) {
  ASSERT(num_args == 0);
  Array array = static_cast<Array>(I->Stack(0));
  ASSERT(array->IsArray());
  RETURN(array->size());
}


DEFINE_PRIMITIVE(WeakArray_class_new) {
  ASSERT(num_args == 1);
  SMI_ARGUMENT(length, 0);
  if (length < 0) {
    return kFailure;
  }
  WeakArray result = H->AllocateWeakArray(length);  // SAFEPOINT
  for (intptr_t i = 0; i < length; i++) {
    result->set_element(i, nil, kNoBarrier);
  }
  RETURN(result);
}


DEFINE_PRIMITIVE(WeakArray_at) {
  ASSERT(num_args == 1);
  WeakArray array = static_cast<WeakArray>(I->Stack(1));
  ASSERT(array->IsWeakArray());
  SMI_ARGUMENT(index, 0);
  index--;
  if ((index < 0) || (index >= array->Size())) {
    return kFailure;
  }
  RETURN(array->element(index));
}


DEFINE_PRIMITIVE(WeakArray_atPut) {
  ASSERT(num_args == 2);
  WeakArray array = static_cast<WeakArray>(I->Stack(2));
  ASSERT(array->IsWeakArray());
  SMI_ARGUMENT(index, 1);
  index--;
  if ((index < 0) || (index >= array->Size())) {
    return kFailure;
  }
  Object value = I->Stack(0);
  array->set_element(index, value);
  RETURN(value);
}


DEFINE_PRIMITIVE(WeakArray_size) {
  ASSERT(num_args == 0);
  WeakArray array = static_cast<WeakArray>(I->Stack(0));
  ASSERT(array->IsWeakArray());
  RETURN(array->size());
}


DEFINE_PRIMITIVE(ByteArray_class_new) {
  ASSERT(num_args == 1);
  SMI_ARGUMENT(length, 0);
  if (length < 0) {
    return kFailure;
  }
  ByteArray result = H->AllocateByteArray(length);  // SAFEPOINT
  memset(result->element_addr(0), 0, length);
  RETURN(result);
}


DEFINE_PRIMITIVE(ByteArray_at) {
  ASSERT(num_args == 1);
  ByteArray array = static_cast<ByteArray>(I->Stack(1));
  ASSERT(array->IsByteArray());
  SMI_ARGUMENT(index, 0);
  index--;
  if ((index < 0) || (index >= array->Size())) {
    return kFailure;
  }
  uint8_t value = array->element(index);
  RETURN(SmallInteger::New(value));
}


DEFINE_PRIMITIVE(ByteArray_atPut) {
  ASSERT(num_args == 2);
  ByteArray array = static_cast<ByteArray>(I->Stack(2));
  ASSERT(array->IsByteArray());
  SMI_ARGUMENT(index, 1);
  index--;
  if ((index < 0) || (index >= array->Size())) {
    return kFailure;
  }
  SMI_ARGUMENT(value, 0);
  if ((value < 0) || (value > 255)) {
    return kFailure;
  }
  array->set_element(index, value);
  RETURN_SMI(value);
}


DEFINE_PRIMITIVE(ByteArray_size) {
  ASSERT(num_args == 0);
  ByteArray array = static_cast<ByteArray>(I->Stack(0));
  ASSERT(array->IsByteArray());
  RETURN(array->size());
}


DEFINE_PRIMITIVE(Bytes_copyByteArrayFromTo) {
  ASSERT(num_args == 2);

  if (!I->Stack(1)->IsSmallInteger()) return kFailure;
  intptr_t start = static_cast<SmallInteger>(I->Stack(1))->value();

  if (!I->Stack(0)->IsSmallInteger()) return kFailure;
  intptr_t stop = static_cast<SmallInteger>(I->Stack(0))->value();

  if (!I->Stack(2)->IsBytes()) return kFailure;

  Bytes bytes = static_cast<Bytes>(I->Stack(2));
  if ((start <= 0) || (stop > bytes->Size())) return kFailure;

  intptr_t subsize = stop - (start - 1);
  if (subsize < 0) {
    return kFailure;
  }

  ByteArray result = H->AllocateByteArray(subsize);  // SAFEPOINT
  bytes = static_cast<Bytes>(I->Stack(2));
  memcpy(result->element_addr(0),
         bytes->element_addr(start - 1),
         subsize);
  RETURN(result);
}


DEFINE_PRIMITIVE(ByteArray_replaceFromToWithStartingAt) {
  ASSERT(num_args == 4);
  ByteArray receiver = static_cast<ByteArray>(I->Stack(4));
  if (!receiver->IsByteArray()) {
    UNREACHABLE();
  }
  SMI_ARGUMENT(start, 3);
  SMI_ARGUMENT(stop, 2);
  Bytes replacement = static_cast<Bytes>(I->Stack(1));
  if (!replacement->IsBytes()) {
    return kFailure;
  }
  SMI_ARGUMENT(replacementStart, 0);

  if (start <= 0) {
    return kFailure;
  }
  if (stop < start) {
    // Empty copy.
    RETURN_SELF();
  }
  if (stop > receiver->Size()) {
    return kFailure;
  }

  intptr_t count = stop - start + 1;

  if (replacementStart <= 0) {
    return kFailure;
  }
  if (replacementStart + count - 1 > replacement->Size()) {
    return kFailure;
  }

  // Note replacement may be receiver.
  memmove(receiver->element_addr(start - 1),
          replacement->element_addr(replacementStart - 1),
          count);
  RETURN_SELF();
}


DEFINE_PRIMITIVE(Array_replaceFromToWithStartingAt) {
  ASSERT(num_args == 4);
  Array receiver = static_cast<Array>(I->Stack(4));
  if (!receiver->IsArray()) {
    UNREACHABLE();
  }
  SMI_ARGUMENT(start, 3);
  SMI_ARGUMENT(stop, 2);
  Array replacement = static_cast<Array>(I->Stack(1));
  if (!replacement->IsArray()) {
    return kFailure;
  }
  SMI_ARGUMENT(replacementStart, 0);

  if (start <= 0) {
    return kFailure;
  }
  if (stop < start) {
    // Empty copy.
    RETURN_SELF();
  }
  if (stop > receiver->Size()) {
    return kFailure;
  }

  intptr_t count = stop - start + 1;

  if (replacementStart <= 0) {
    return kFailure;
  }
  if (replacementStart + count - 1 > replacement->Size()) {
    return kFailure;
  }

  // Note replacement may be receiver.
  if (replacementStart < start) {
    for (intptr_t i = count - 1; i >= 0; i--) {
      receiver->set_element(start - 1 + i,
                            replacement->element(replacementStart - 1 + i));
    }
  } else {
    for (intptr_t i = 0; i < count; i++) {
      receiver->set_element(start - 1 + i,
                            replacement->element(replacementStart - 1 + i));
    }
  }

  RETURN_SELF();
}

DEFINE_PRIMITIVE(Array_copyFromTo) {
  ASSERT(num_args == 2);

  if (!I->Stack(1)->IsSmallInteger()) return kFailure;
  intptr_t start = static_cast<SmallInteger>(I->Stack(1))->value();

  if (!I->Stack(0)->IsSmallInteger()) return kFailure;
  intptr_t stop = static_cast<SmallInteger>(I->Stack(0))->value();

  if (!I->Stack(2)->IsArray()) return kFailure;

  Array array = static_cast<Array>(I->Stack(2));
  if ((start <= 0) || (stop > array->Size())) return kFailure;

  intptr_t subsize = stop - (start - 1);
  if (subsize < 0) {
    return kFailure;
  }

  Array result = H->AllocateArray(subsize);  // SAFEPOINT
  array = static_cast<Array>(I->Stack(2));
  for (intptr_t i = 0; i < subsize; i++) {
    result->set_element(i, array->element(i + start - 1));
  }
  RETURN(result);
}

DEFINE_PRIMITIVE(String_at) {
  ASSERT(num_args == 1);
  String string = static_cast<String>(I->Stack(1));
  ASSERT(string->IsString());
  SMI_ARGUMENT(index, 0);
  index--;
  if ((index < 0) || (index >= string->Size())) {
    return kFailure;
  }
  uint8_t value = string->element(index);
  RETURN(SmallInteger::New(value));
}


DEFINE_PRIMITIVE(String_size) {
  ASSERT(num_args == 0);
  String string = static_cast<String>(I->Stack(0));
  ASSERT(string->IsString());
  RETURN(string->size());
}


DEFINE_PRIMITIVE(String_hash) {
  ASSERT(num_args == 0);
  String string = static_cast<String>(I->Stack(0));
  ASSERT(string->IsString());
  SmallInteger hash = string->EnsureHash(I->isolate());
  RETURN(hash);
}


DEFINE_PRIMITIVE(Activation_sender) {
  ASSERT(num_args == 0);
  Activation activation = static_cast<Activation>(I->Stack(0));
  ASSERT(activation->IsActivation());
  RETURN(I->ActivationSender(activation));  // SAFEPOINT
}


DEFINE_PRIMITIVE(Activation_senderPut) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  Activation new_sender = static_cast<Activation>(I->Stack(0));
  if (!new_sender->IsActivation() && (new_sender != nil)) {
    return kFailure;
  }
  I->ActivationSenderPut(activation, new_sender);  // SAFEPOINT
  RETURN_SELF();
}


DEFINE_PRIMITIVE(Activation_bci) {
  ASSERT(num_args == 0);
  Activation activation = static_cast<Activation>(I->Stack(0));
  ASSERT(activation->IsActivation());
  RETURN(I->ActivationBCI(activation));
}


DEFINE_PRIMITIVE(Activation_bciPut) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  SmallInteger new_bci = static_cast<SmallInteger>(I->Stack(0));
  if (!new_bci->IsSmallInteger() && (new_bci != nil)) {
    return kFailure;
  }
  I->ActivationBCIPut(activation, new_bci);  // SAFEPOINT
  RETURN_SELF();
}


DEFINE_PRIMITIVE(Activation_method) {
  ASSERT(num_args == 0);
  Activation activation = static_cast<Activation>(I->Stack(0));
  ASSERT(activation->IsActivation());
  // No frame state to sync.
  RETURN(activation->method());
}


DEFINE_PRIMITIVE(Activation_methodPut) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  Method new_method = static_cast<Method>(I->Stack(0));
  I->ActivationMethodPut(activation, new_method);  // SAFEPOINT
  RETURN_SELF();
}


DEFINE_PRIMITIVE(Activation_closure) {
  ASSERT(num_args == 0);
  Activation activation = static_cast<Activation>(I->Stack(0));
  ASSERT(activation->IsActivation());
  // No frame state to sync.
  RETURN(activation->closure());
}


DEFINE_PRIMITIVE(Activation_closurePut) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  Closure new_closure = static_cast<Closure>(I->Stack(0));
  if (!new_closure->IsClosure() && (new_closure != nil)) {
    return kFailure;
  }
  I->ActivationClosurePut(activation, new_closure);  // SAFEPOINT
  RETURN_SELF();
}


DEFINE_PRIMITIVE(Activation_receiver) {
  ASSERT(num_args == 0);
  Activation activation = static_cast<Activation>(I->Stack(0));
  ASSERT(activation->IsActivation());
  // No frame state to sync.
  RETURN(activation->receiver());
}


DEFINE_PRIMITIVE(Activation_receiverPut) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  Object new_receiver = I->Stack(0);
  I->ActivationReceiverPut(activation, new_receiver);  // SAFEPOINT
  RETURN_SELF();
}


DEFINE_PRIMITIVE(Activation_tempAt) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  SMI_ARGUMENT(index, 0);
  index--;
  if ((index < 0) || (index >= I->ActivationTempSize(activation))) {
    return kFailure;
  }
  RETURN(I->ActivationTempAt(activation, index));
}


DEFINE_PRIMITIVE(Activation_tempAtPut) {
  ASSERT(num_args == 2);
  Activation activation = static_cast<Activation>(I->Stack(2));
  ASSERT(activation->IsActivation());
  SMI_ARGUMENT(index, 1);
  Object value = I->Stack(0);
  index--;
  if ((index < 0) || (index >= I->ActivationTempSize(activation))) {
    return kFailure;
  }
  I->ActivationTempAtPut(activation, index, value);  // SAFEPOINT
  value = I->Stack(0);
  RETURN(value);
}


DEFINE_PRIMITIVE(Activation_tempSize) {
  ASSERT(num_args == 0);
  Activation activation = static_cast<Activation>(I->Stack(0));
  ASSERT(activation->IsActivation());
  RETURN_SMI(I->ActivationTempSize(activation));
}


DEFINE_PRIMITIVE(Activation_tempSizePut) {
  ASSERT(num_args == 1);
  Activation activation = static_cast<Activation>(I->Stack(1));
  ASSERT(activation->IsActivation());
  SMI_ARGUMENT(new_size, 0);
  if ((new_size < 0) || (new_size > kMaxTemps)) {
    return kFailure;
  }
  I->ActivationTempSizePut(activation, new_size);  // SAFEPOINT
  RETURN_SMI(new_size);
}


DEFINE_PRIMITIVE(Activation_class_new) {
  ASSERT(num_args == 0);
  Activation result = H->AllocateActivation();  // SAFEPOINT
  result->set_sender(static_cast<Activation>(nil), kNoBarrier);
  result->set_bci(static_cast<SmallInteger>(nil));
  result->set_method(static_cast<Method>(nil), kNoBarrier);
  result->set_closure(static_cast<Closure>(nil), kNoBarrier);
  result->set_receiver(nil, kNoBarrier);
  result->set_stack_depth(SmallInteger::New(0));
  RETURN(result);
}


DEFINE_PRIMITIVE(Closure_class_new) {
  ASSERT(num_args == 4);
  Activation defining_activation = static_cast<Activation>(I->Stack(3));
  SmallInteger initial_bci = static_cast<SmallInteger>(I->Stack(2));
  SmallInteger closure_num_args = static_cast<SmallInteger>(I->Stack(1));
  SmallInteger num_copied = static_cast<SmallInteger>(I->Stack(0));
  if (!defining_activation->IsActivation()) {
    return kFailure;
  }
  if (!initial_bci->IsSmallInteger()) {
    return kFailure;
  }
  if (!closure_num_args->IsSmallInteger()) {
    return kFailure;
  }
  if (!num_copied->IsSmallInteger()) {
    return kFailure;
  }
  if (num_copied->value() < 0) {
    return kFailure;
  }

  Closure result = H->AllocateClosure(num_copied->value());  // SAFEPOINT
  defining_activation = static_cast<Activation>(I->Stack(3));
  initial_bci = static_cast<SmallInteger>(I->Stack(2));
  closure_num_args = static_cast<SmallInteger>(I->Stack(1));
  num_copied = static_cast<SmallInteger>(I->Stack(0));

  result->set_defining_activation(defining_activation);
  result->set_initial_bci(initial_bci);
  result->set_num_args(closure_num_args);
  for (intptr_t i = 0; i < num_copied->value(); i++) {
    result->set_copied(i, nil, kNoBarrier);
  }

  RETURN(result);
}


DEFINE_PRIMITIVE(Closure_numCopied) {
  ASSERT(num_args == 1);
  Closure subject = static_cast<Closure>(I->Stack(0));
  if (!subject->IsClosure()) {
    UNIMPLEMENTED();
  }
  RETURN_SMI(subject->NumCopied());
}


DEFINE_PRIMITIVE(Closure_definingActivation) {
  ASSERT(num_args == 0 || num_args == 1);
  Closure subject = static_cast<Closure>(I->Stack(0));
  if (!subject->IsClosure()) {
    UNIMPLEMENTED();
  }
  RETURN(subject->defining_activation());
}


DEFINE_PRIMITIVE(Closure_definingActivationPut) {
  UNIMPLEMENTED();
  return kSuccess;
}


DEFINE_PRIMITIVE(Closure_initialBci) {
  ASSERT(num_args == 1);
  Closure subject = static_cast<Closure>(I->Stack(0));
  if (!subject->IsClosure()) {
    UNIMPLEMENTED();
  }
  RETURN(subject->initial_bci());
}


DEFINE_PRIMITIVE(Closure_initialBciPut) { UNIMPLEMENTED(); return kSuccess; }


DEFINE_PRIMITIVE(Closure_numArgs) {
  ASSERT(num_args == 0);
  Closure rcvr = static_cast<Closure>(I->Stack(0));
  if (!rcvr->IsClosure()) {
    UNREACHABLE();
    return kFailure;
  }
  RETURN(rcvr->num_args());
}


DEFINE_PRIMITIVE(Closure_numArgsPut) { UNIMPLEMENTED(); return kSuccess; }


DEFINE_PRIMITIVE(Closure_copiedAt) {
  ASSERT(num_args == 2);
  Closure receiver = static_cast<Closure>(I->Stack(1));
  SmallInteger index = static_cast<SmallInteger>(I->Stack(0));
  if (!receiver->IsClosure()) {
    return kFailure;
  }
  if (!index->IsSmallInteger()) {
    return kFailure;
  }
  if (index->value() <= 0) {
    return kFailure;
  }
  if (index->value() > receiver->NumCopied()) {
    return kFailure;
  }
  Object value = receiver->copied(index->value() - 1);
  RETURN(value);
}


DEFINE_PRIMITIVE(Closure_copiedAtPut) {
  ASSERT(num_args == 3);
  Closure receiver = static_cast<Closure>(I->Stack(2));
  SmallInteger index = static_cast<SmallInteger>(I->Stack(1));
  Object value = I->Stack(0);
  if (!receiver->IsClosure()) {
    return kFailure;
  }
  if (!index->IsSmallInteger()) {
    return kFailure;
  }
  if (index->value() <= 0) {
    return kFailure;
  }
  if (index->value() > receiver->NumCopied()) {
    return kFailure;
  }
  receiver->set_copied(index->value() - 1, value);
  RETURN(value);
}


DEFINE_PRIMITIVE(Object_class) {
  ASSERT((num_args == 0) || (num_args == 1));
  Object subject = I->Stack(0);
  RETURN(subject->Klass(H));
}


DEFINE_PRIMITIVE(Object_identical) {
  ASSERT(num_args == 1 || num_args == 2);
  Object left = I->Stack(1);
  Object right = I->Stack(0);
  RETURN_BOOL(left == right);
}


DEFINE_PRIMITIVE(Object_identityHash) {
  ASSERT(num_args == 0 || num_args == 1);
  Object receiver = I->Stack(0);
  intptr_t hash;
  if (receiver->IsSmallInteger()) {
    hash = static_cast<SmallInteger>(receiver)->value();
    if (hash == 0) {
      hash = 1;
    }
  } else if (receiver->IsMediumInteger()) {
    hash = static_cast<MediumInteger>(receiver)->value();
    hash &= SmallInteger::kMaxValue;
    if (hash == 0) {
      hash = 1;
    }
  } else if (receiver->IsString()) {
    static_cast<String>(receiver)->EnsureHash(I->isolate());
    hash = static_cast<String>(receiver)->header_hash();
  } else {
    hash = static_cast<HeapObject>(receiver)->header_hash();
    if (hash == 0) {
      hash = I->isolate()->random().NextUInt64() & SmallInteger::kMaxValue;
      if (hash == 0) {
        hash = 1;
      }
      static_cast<HeapObject>(receiver)->set_header_hash(hash);
    }
  }
  RETURN_SMI(hash);
}


DEFINE_PRIMITIVE(Object_performWithAll) {
  ASSERT(num_args == 3);

  Object receiver = I->Stack(2);
  String selector = static_cast<String>(I->Stack(1));
  Array arguments = static_cast<Array>(I->Stack(0));

  if (!selector->IsString() ||
      !selector->is_canonical() ||
      !arguments->IsArray()) {
    UNIMPLEMENTED();
    return kFailure;
  }

  I->Drop(num_args + 1);

  intptr_t perform_args = arguments->Size();
  I->Push(receiver);
  for (intptr_t i = 0; i < perform_args; i++) {
    I->Push(arguments->element(i));
  }

  I->Perform(selector, perform_args);
  return kSuccess;
}


DEFINE_PRIMITIVE(Closure_value0) {
  ASSERT(num_args == 0);
  Closure closure = static_cast<Closure>(I->Stack(num_args));
  ASSERT(closure->IsClosure());
  if (closure->num_args() != SmallInteger::New(0)) {
    return kFailure;
  }

  I->ActivateClosure(0);
  return kSuccess;
}


DEFINE_PRIMITIVE(Closure_value1) {
  ASSERT(num_args == 1);
  Closure closure = static_cast<Closure>(I->Stack(num_args));
  ASSERT(closure->IsClosure());
  if (closure->num_args() != SmallInteger::New(1)) {
    return kFailure;
  }

  I->ActivateClosure(1);
  return kSuccess;
}


DEFINE_PRIMITIVE(Closure_value2) {
  ASSERT(num_args == 2);
  Closure closure = static_cast<Closure>(I->Stack(num_args));
  ASSERT(closure->IsClosure());
  if (closure->num_args() != SmallInteger::New(2)) {
    return kFailure;
  }

  I->ActivateClosure(2);
  return kSuccess;
}


DEFINE_PRIMITIVE(Closure_value3) {
  ASSERT(num_args == 3);
  Closure closure = static_cast<Closure>(I->Stack(num_args));
  ASSERT(closure->IsClosure());
  if (closure->num_args() != SmallInteger::New(3)) {
    return kFailure;
  }

  I->ActivateClosure(3);
  return kSuccess;
}


DEFINE_PRIMITIVE(Closure_valueArray) {
  ASSERT(num_args == 1);
  Closure closure = static_cast<Closure>(I->Stack(1));
  ASSERT(closure->IsClosure());
  Array args = static_cast<Array>(I->Stack(0));
  if (!args->IsArray() || args->size() != closure->num_args()) {
    return kFailure;
  }

  I->Pop();
  intptr_t closure_args = args->Size();
  for (intptr_t i = 0; i < closure_args; i++) {
    I->Push(args->element(i));
  }

  I->ActivateClosure(closure_args);
  return kSuccess;
}


DEFINE_PRIMITIVE(Activation_jump) {
  ASSERT(num_args == 1);
  Activation target = static_cast<Activation>(I->Stack(0));
  if (!target->IsActivation() ||
      !target->bci()->IsSmallInteger()) {
    return kFailure;
  }

  I->Drop(num_args + 1);
  I->SetCurrentActivation(target);  // SAFEPOINT
  return kSuccess;
}


DEFINE_PRIMITIVE(Behavior_allInstances) {
  ASSERT(num_args == 1);
  Behavior cls = static_cast<Behavior>(I->Stack(0));
  if (!cls->IsRegularObject()) {
    UNREACHABLE();
  }
  if (cls->id() == nil) {
    // Class not yet registered: no instance has been allocated.
    Array result = H->AllocateArray(0);  // SAFEPOINT
    RETURN(result);
  }

  ASSERT(cls->id()->IsSmallInteger());
  intptr_t cid = cls->id()->value();
  if (cid == kIllegalCid) {
    UNREACHABLE();
  }
  intptr_t num_instances = H->CountInstances(cid);
  if (cid == kArrayCid) {
    num_instances++;
  }
  Array result = H->AllocateArray(num_instances);  // SAFEPOINT
  result->set_size(SmallInteger::New(num_instances));
  intptr_t num_instances2 = H->CollectInstances(cid, result);

  ASSERT(num_instances == num_instances2);
  // Note that if a GC happens there may be fewer instances than
  // we initially counted. TODO(rmacnak): truncate result.
  // OS::PrintErr("Found %" Pd " instances of %" Pd "\n", num_instances, cid);

  RETURN(result);
}


DEFINE_PRIMITIVE(Array_elementsForwardIdentity) {
  ASSERT(num_args == 2);
  Array left = static_cast<Array>(I->Stack(1));
  Array right = static_cast<Array>(I->Stack(0));
  if (left->IsArray() && right->IsArray()) {
    if (H->BecomeForward(left, right)) {
      RETURN_SELF();
    }
  }
  return kFailure;
}


DEFINE_PRIMITIVE(Platform_operatingSystem) {
  const char* name = OS::Name();
  intptr_t length = strlen(name);
  String result = H->AllocateString(length);  // SAFEPOINT
  memcpy(result->element_addr(0), name, length);
  RETURN(result);
}


DEFINE_PRIMITIVE(Time_monotonicNanos) {
  ASSERT(num_args == 0);
  int64_t now = OS::CurrentMonotonicNanos();
  RETURN_MINT(now);
}


DEFINE_PRIMITIVE(Time_utcEpochNanos) { UNIMPLEMENTED(); return kSuccess; }


DEFINE_PRIMITIVE(print) {
  ASSERT(num_args == 1);
  ASSERT(I->StackDepth() >= 2);

  Object message = I->Stack(0);
  if (message->IsString()) {
    String string = static_cast<String>(message);
    const char* cstr =
        reinterpret_cast<const char*>(string->element_addr(0));
    OS::Print("%.*s\n", static_cast<int>(string->Size()), cstr);
  } else {
    char* cstr = message->ToCString(H);
    OS::Print("[print] %s\n", cstr);
    free(cstr);
  }
  RETURN_SELF();
}


DEFINE_PRIMITIVE(panic) {
  OS::PrintErr("Panic:\n");
  I->PrintStack();
  OS::Exit(-1);
  UNREACHABLE();
  return kFailure;
}


DEFINE_PRIMITIVE(flushCache) {
  // Atomicity may require this to be part of an atomic install's become. If so,
  // remove this separate primitive.
  UNREACHABLE();
  return kFailure;
}


DEFINE_PRIMITIVE(collectGarbage) {
  H->CollectAll(Heap::kPrimitive);  // SAFEPOINT
  RETURN_SELF();
}


DEFINE_PRIMITIVE(MessageLoop_exit) {
  ASSERT(num_args == 1);
  SmallInteger exit_code = static_cast<SmallInteger>(I->Stack(0));
  if (!exit_code->IsSmallInteger()) {
    return kFailure;
  }
  I->isolate()->loop()->Exit(exit_code->value());
  I->Exit();
  UNREACHABLE();
  return kFailure;
}

DEFINE_PRIMITIVE(Double_asStringFixed) {
  ASSERT(num_args == 1);
  FLOAT_ARGUMENT(value, 1);
  SMI_ARGUMENT(fraction_digits, 0);
  if (fraction_digits < 0 || fraction_digits > 20) {
    return kFailure;
  }

  char buffer[64];
  intptr_t length;
  if (value < 1e21 && value > -1e21) {
    length = DoubleToCStringAsFixed(value, fraction_digits,
                                    buffer, sizeof(buffer));
  } else {
    length = DoubleToCStringAsShortest(value, buffer, sizeof(buffer));
  }
  ASSERT(length < 64);

  String result = H->AllocateString(length);  // SAFEPOINT
  memcpy(result->element_addr(0), buffer, length);
  RETURN(result);
}

DEFINE_PRIMITIVE(Double_asStringExponential) {
  ASSERT(num_args == 1);
  FLOAT_ARGUMENT(value, 1);
  SMI_ARGUMENT(fraction_digits, 0);
  if (fraction_digits < 0 || fraction_digits > 20) {
    return kFailure;
  }

  char buffer[64];
  intptr_t length = DoubleToCStringAsExponential(value, fraction_digits,
                                                 buffer, sizeof(buffer));
  ASSERT(length < 64);

  String result = H->AllocateString(length);  // SAFEPOINT
  memcpy(result->element_addr(0), buffer, length);
  RETURN(result);
}

DEFINE_PRIMITIVE(Double_asStringPrecision) {
  ASSERT(num_args == 1);
  FLOAT_ARGUMENT(value, 1);
  SMI_ARGUMENT(precision, 0);
  if (precision < 1 || precision > 21) {
    return kFailure;
  }

  char buffer[64];
  intptr_t length = DoubleToCStringAsPrecision(value, precision,
                                               buffer, sizeof(buffer));
  ASSERT(length < 64);

  String result = H->AllocateString(length);  // SAFEPOINT
  memcpy(result->element_addr(0), buffer, length);
  RETURN(result);
}

DEFINE_PRIMITIVE(Number_asString) {
  ASSERT(num_args == 0);
  Object receiver = I->Stack(0);

  char buffer[64];
  intptr_t length = -1;
  if (receiver->IsSmallInteger()) {
    intptr_t value = static_cast<SmallInteger>(receiver)->value();
    length = snprintf(buffer, sizeof(buffer), "%" Pd "", value);
  } else if (receiver->IsMediumInteger()) {
    int64_t value = static_cast<MediumInteger>(receiver)->value();
    length = snprintf(buffer, sizeof(buffer), "%" Pd64 "", value);
  } else if (receiver->IsFloat64()) {
    double value = static_cast<Float64>(receiver)->value();
    length = DoubleToCStringAsShortest(value, buffer, sizeof(buffer));
  } else if (receiver->IsLargeInteger()) {
    LargeInteger large = static_cast<LargeInteger>(receiver);
    String result = LargeInteger::PrintString(large, H);  // SAFEPOINT
    RETURN(result);
  } else {
    UNIMPLEMENTED();
  }
  ASSERT(length < 64);

  String result = H->AllocateString(length);  // SAFEPOINT
  memcpy(result->element_addr(0), buffer, length);

  RETURN(result);
}


DEFINE_PRIMITIVE(Closure_ensure) {
  // This is a marker primitive checked on non-local return.
  return kFailure;
}


DEFINE_PRIMITIVE(String_equals) {
  ASSERT(num_args == 1);

  String left = static_cast<String>(I->Stack(1));
  String right = static_cast<String>(I->Stack(0));
  if (left == right) {
    RETURN_BOOL(true);
    return kSuccess;
  }
  if (!left->IsString() || !right->IsString()) {
    RETURN_BOOL(false);
  }
  if (left->size() != right->size()) {
    RETURN_BOOL(false);
  }
  if (left->EnsureHash(I->isolate()) != right->EnsureHash(I->isolate())) {
    RETURN_BOOL(false);
  }
  intptr_t length = left->Size();
  for (intptr_t i = 0; i < length; i++) {
    if (left->element(i) != right->element(i)) {
      RETURN_BOOL(false);
    }
  }
  RETURN_BOOL(true);
}


DEFINE_PRIMITIVE(String_concat) {
  ASSERT(num_args == 1);
  String a = static_cast<String>(I->Stack(1));
  String b = static_cast<String>(I->Stack(0));
  if (!a->IsString() || !b->IsString()) {
    return kFailure;
  }
  intptr_t a_length = a->Size();
  intptr_t b_length = b->Size();
  String result =
      H->AllocateString(a_length + b_length);  // SAFEPOINT
  a = static_cast<String>(I->Stack(1));
  b = static_cast<String>(I->Stack(0));
  memcpy(result->element_addr(0), a->element_addr(0), a_length);
  memcpy(result->element_addr(a_length), b->element_addr(0), b_length);
  RETURN(result);
}


DEFINE_PRIMITIVE(Closure_onDo) {
  // This is a marker primitive for the in-image exception handling machinary.
  return kFailure;
}


DEFINE_PRIMITIVE(Bytes_startsWith) {
  ASSERT(num_args == 1);
  Bytes string = static_cast<Bytes>(I->Stack(1));
  Bytes prefix = static_cast<Bytes>(I->Stack(0));
  if (!string->IsBytes() || !prefix->IsBytes()) {
    return kFailure;
  }

  intptr_t string_length = string->Size();
  intptr_t prefix_length = prefix->Size();
  if (prefix_length > string_length) {
    RETURN_BOOL(false);
  }
  for (intptr_t i = 0; i < prefix_length; i++) {
    if (string->element(i) != prefix->element(i)) {
      RETURN_BOOL(false);
    }
  }
  RETURN_BOOL(true);
}


DEFINE_PRIMITIVE(Bytes_endsWith) {
  ASSERT(num_args == 1);
  Bytes string = static_cast<Bytes>(I->Stack(1));
  Bytes suffix = static_cast<Bytes>(I->Stack(0));
  if (!string->IsBytes() || !suffix->IsBytes()) {
    return kFailure;
  }

  intptr_t string_length = string->Size();
  intptr_t suffix_length = suffix->Size();
  if (suffix_length > string_length) {
    RETURN_BOOL(false);
  }
  intptr_t offset = string_length - suffix_length;
  for (intptr_t i = 0; i < suffix_length; i++) {
    if (string->element(offset + i) != suffix->element(i)) {
      RETURN_BOOL(false);
    }
  }

  RETURN_BOOL(true);
}


DEFINE_PRIMITIVE(Bytes_indexOf) {
  ASSERT(num_args == 2);

  Bytes string = static_cast<Bytes>(I->Stack(2));
  Bytes substring = static_cast<Bytes>(I->Stack(1));
  SmallInteger start = static_cast<SmallInteger>(I->Stack(0));
  if (!(string->IsBytes())) {
    UNREACHABLE();
    return kFailure;
  }
  if (!(substring->IsBytes())) {
    return kFailure;
  }
  if (!start->IsSmallInteger()) {
    return kFailure;
  }
  intptr_t string_length = string->Size();
  intptr_t substring_length = substring->Size();
  intptr_t start_index = start->value() - 1;
  if (start_index < 0) {
    return kFailure;
  }
  if (start_index > string_length) {
    return kFailure;
  }

  if (substring_length > string_length) {
    RETURN_SMI(static_cast<intptr_t>(0));
  }

  intptr_t limit = string_length - substring_length;
  for (intptr_t start = start_index; start <= limit; start++) {
    bool found = true;
    for (intptr_t i = 0; i < substring_length; i++) {
      if (string->element(start + i) != substring->element(i)) {
        found = false;
        break;
      }
    }
    if (found) {
      RETURN_SMI(start + 1);
    }
  }
  RETURN_SMI(static_cast<intptr_t>(0));
}


DEFINE_PRIMITIVE(Bytes_lastIndexOf) {
  ASSERT(num_args == 2);

  Bytes string = static_cast<Bytes>(I->Stack(2));
  Bytes substring = static_cast<Bytes>(I->Stack(1));
  SmallInteger start = static_cast<SmallInteger>(I->Stack(0));
  if (!(string->IsBytes())) {
    UNREACHABLE();
    return kFailure;
  }
  if (!(substring->IsBytes())) {
    return kFailure;
  }
  if (!start->IsSmallInteger()) {
    return kFailure;
  }

  intptr_t string_length = string->Size();
  intptr_t substring_length = substring->Size();
  intptr_t start_index = start->value() - 1;
  if (start_index < 0) {
    return kFailure;
  }
  if (start_index > string_length) {
    return kFailure;
  }
  if (substring_length > string_length) {
    RETURN_SMI(static_cast<intptr_t>(0));
  }

  intptr_t limit = string_length - substring_length;
  if (limit > start_index) {
    limit = start_index;
  }
  for (intptr_t start = limit; start >= 0; start--) {
    bool found = true;
    for (intptr_t i = 0; i < substring_length; i++) {
      if (string->element(start + i) != substring->element(i)) {
        found = false;
      }
    }
    if (found) {
      RETURN_SMI(start + 1);
    }
  }
  RETURN_SMI(static_cast<intptr_t>(0));
}


DEFINE_PRIMITIVE(Bytes_copyStringFromTo) {
  ASSERT(num_args == 2);

  if (!I->Stack(1)->IsSmallInteger()) return kFailure;
  intptr_t start = static_cast<SmallInteger>(I->Stack(1))->value();

  if (!I->Stack(0)->IsSmallInteger()) return kFailure;
  intptr_t stop = static_cast<SmallInteger>(I->Stack(0))->value();

  if (!I->Stack(2)->IsBytes()) return kFailure;

  Bytes bytes = static_cast<Bytes>(I->Stack(2));
  if ((start <= 0) || (stop > bytes->Size())) return kFailure;

  intptr_t subsize = stop - (start - 1);
  if (subsize < 0) {
    return kFailure;
  }

  String result = H->AllocateString(subsize);  // SAFEPOINT
  bytes = static_cast<Bytes>(I->Stack(2));
  memcpy(result->element_addr(0),
         bytes->element_addr(start - 1),
         subsize);
  RETURN(result);
}


DEFINE_PRIMITIVE(String_class_with) {
  ASSERT(num_args == 1);
  SMI_ARGUMENT(byte, 0);
  if ((byte < 0) || (byte > 255)) {
    return kFailure;
  }
  String result = H->AllocateString(1);  // SAFEPOINT
  result->set_element(0, byte);
  RETURN(result);
}


DEFINE_PRIMITIVE(String_class_withAll) {
  ASSERT(num_args == 1);

  if (I->Stack(0)->IsBytes()) {
    intptr_t length = static_cast<Bytes>(I->Stack(0))->Size();
    String result = H->AllocateString(length);  // SAFEPOINT
    Bytes bytes = static_cast<Bytes>(I->Stack(0));
    memcpy(result->element_addr(0), bytes->element_addr(0), length);
    RETURN(result);
  } else if (I->Stack(0)->IsArray()) {
    Array bytes = static_cast<Array>(I->Stack(0));
    if (!bytes->IsArray()) {
      return kFailure;
    }

    intptr_t length = bytes->Size();
    for (intptr_t i = 0; i < length; i++) {
      SmallInteger byte = static_cast<SmallInteger>(bytes->element(i));
      if (!byte->IsSmallInteger()) {
        return kFailure;
      }
      intptr_t raw_byte = byte->value();
      if ((raw_byte < 0) || (raw_byte > 255)) {
        return kFailure;
      }
    }

    String result = H->AllocateString(length);  // SAFEPOINT
    bytes = static_cast<Array>(I->Stack(0));

    for (intptr_t i = 0; i < length; i++) {
      SmallInteger byte = static_cast<SmallInteger>(bytes->element(i));
      intptr_t raw_byte = byte->value();
      result->set_element(i, raw_byte);
    }

    RETURN(result);
  }
  return kFailure;
}


DEFINE_PRIMITIVE(ByteArray_class_withAll) {
  ASSERT(num_args == 1);

  if (I->Stack(0)->IsBytes()) {
    intptr_t length = static_cast<Bytes>(I->Stack(0))->Size();
    String result = H->AllocateString(length);  // SAFEPOINT
    Bytes bytes = static_cast<Bytes>(I->Stack(0));
    memcpy(result->element_addr(0), bytes->element_addr(0), length);
    RETURN(result);
  } else if (I->Stack(0)->IsArray()) {
    Array bytes = static_cast<Array>(I->Stack(0));
    if (!bytes->IsArray()) {
      return kFailure;
    }

    intptr_t length = bytes->Size();
    for (intptr_t i = 0; i < length; i++) {
      SmallInteger byte = static_cast<SmallInteger>(bytes->element(i));
      if (!byte->IsSmallInteger()) {
        return kFailure;
      }
      intptr_t raw_byte = byte->value();
      if ((raw_byte < 0) || (raw_byte > 255)) {
        return kFailure;
      }
    }

    String result = H->AllocateString(length);  // SAFEPOINT
    bytes = static_cast<Array>(I->Stack(0));

    for (intptr_t i = 0; i < length; i++) {
      SmallInteger byte = static_cast<SmallInteger>(bytes->element(i));
      intptr_t raw_byte = byte->value();
      result->set_element(i, raw_byte);
    }

    RETURN(result);
  }
  return kFailure;
}


DEFINE_PRIMITIVE(Object_isCanonical) {
  ASSERT(num_args == 1);
  Object object = I->Stack(0);
  if (object->IsHeapObject()) {
    RETURN_BOOL(static_cast<HeapObject>(object)->is_canonical());
  } else {
    RETURN_BOOL(true);
  }
}


DEFINE_PRIMITIVE(Object_markCanonical) {
  ASSERT(num_args == 1);
  Object object = I->Stack(0);
  if (object->IsHeapObject()) {
    static_cast<HeapObject>(object)->set_is_canonical(true);
  } else {
    // Nop.
  }
  RETURN(object);
}


DEFINE_PRIMITIVE(writeBytesToFile) {
  ASSERT(num_args == 2);
  ByteArray content = static_cast<ByteArray>(I->Stack(1));
  String filename = static_cast<String>(I->Stack(0));
  if (!content->IsByteArray() || !filename->IsString()) {
    return kFailure;
  }

  char* raw_filename = reinterpret_cast<char*>(malloc(filename->Size() + 1));
  memcpy(raw_filename, filename->element_addr(0), filename->Size());
  raw_filename[filename->Size()] = 0;
  FILE* f = fopen(raw_filename, "wb");
  if (f == NULL) {
    FATAL1("Cannot open %s\n", raw_filename);
  }

  size_t length = content->Size();
  size_t start = 0;
  while (start != length) {
    size_t written = fwrite(content->element_addr(start), 1, length - start, f);
    if (written == 0) {
      FATAL1("Failed to write '%s'\n", raw_filename);
    }
    start += written;
  }
  fflush(f);
  fclose(f);

  free(raw_filename);

  RETURN_SELF();
}


DEFINE_PRIMITIVE(readFileAsBytes) {
  ASSERT(num_args == 1);
  String filename = static_cast<String>(I->Stack(0));
  if (!filename->IsString()) {
    return kFailure;
  }

  char* raw_filename = reinterpret_cast<char*>(malloc(filename->Size() + 1));
  memcpy(raw_filename, filename->element_addr(0), filename->Size());
  raw_filename[filename->Size()] = 0;
  FILE* f = fopen(raw_filename, "rb");
  if (f == NULL) {
    FATAL1("Failed to stat '%s'\n", raw_filename);
  }
  struct stat st;
  if (fstat(fileno(f), &st) != 0) {
    FATAL1("Failed to stat '%s'\n", raw_filename);
  }
  size_t length = st.st_size;

  ByteArray result = H->AllocateByteArray(length);  // SAFEPOINT
  size_t start = 0;
  size_t remaining = length;
  while (remaining > 0) {
    size_t bytes_read = fread(result->element_addr(start), 1, remaining, f);
    if (bytes_read == 0) {
      FATAL1("Failed to read '%s'\n", raw_filename);
    }
    start += bytes_read;
    remaining -= bytes_read;
  }

  fclose(f);
  free(raw_filename);

  RETURN(result);
}


DEFINE_PRIMITIVE(Double_class_parse) {
  ASSERT(num_args == 1);
  String string = static_cast<String>(I->Stack(0));
  if (!string->IsString()) {
    return kFailure;
  }
  double raw_result;
  const char* cstr = reinterpret_cast<const char*>(string->element_addr(0));
  intptr_t length = string->Size();
  if (CStringToDouble(cstr, length, &raw_result)) {
    RETURN_FLOAT(raw_result);
  }
  return kFailure;
}


DEFINE_PRIMITIVE(currentActivation) {
  ASSERT(num_args == 0);
  RETURN(I->CurrentActivation());  // SAFEPOINT
}


DEFINE_PRIMITIVE(Behavior_adoptInstance) {
  ASSERT(num_args == 2);
  Behavior new_cls = static_cast<Behavior>(I->Stack(1));
  HeapObject instance = static_cast<HeapObject>(I->Stack(0));
  Behavior old_cls = instance->Klass(H);

  ASSERT(old_cls->cid() >= kFirstRegularObjectCid);
  ASSERT(old_cls->format() == new_cls->format());

  SmallInteger id = new_cls->id();
  if (id == nil) {
    id = SmallInteger::New(H->AllocateClassId());  // SAFEPOINT
    new_cls = static_cast<Behavior>(I->Stack(1));
    instance = static_cast<HeapObject>(I->Stack(0));
    new_cls->set_id(id);
    H->RegisterClass(id->value(), new_cls);
  }
  ASSERT(id->IsSmallInteger());
  instance->set_cid(id->value());

  RETURN_SELF();
}


DEFINE_PRIMITIVE(openPort) {
  ASSERT(num_args == 0);
  Port new_port = I->isolate()->loop()->OpenPort();
  RETURN_MINT(new_port);
}


DEFINE_PRIMITIVE(closePort) {
  ASSERT(num_args == 1);
  MINT_ARGUMENT(port, 0);
  I->isolate()->loop()->ClosePort(port);
  RETURN_SELF();
}


DEFINE_PRIMITIVE(spawn) {
  ASSERT(num_args == 1);
  ByteArray message = static_cast<ByteArray>(I->Stack(0));
  if (message->IsByteArray()) {
    intptr_t length = message->Size();
    uint8_t* data = reinterpret_cast<uint8_t*>(malloc(length));
    memcpy(data, message->element_addr(0), length);

    I->isolate()->Spawn(new IsolateMessage(ILLEGAL_PORT, data, length));

    RETURN_SELF();
  }

  return kFailure;
}


DEFINE_PRIMITIVE(send) {
  ASSERT(num_args == 2);
  MINT_ARGUMENT(port, 1);
  ByteArray data = static_cast<ByteArray>(I->Stack(0));
  if (!data->IsByteArray()) {
    return kFailure;
  }

  intptr_t length = data->Size();
  uint8_t* raw_data = reinterpret_cast<uint8_t*>(malloc(length));
  memcpy(raw_data, data->element_addr(0), length);
  IsolateMessage* message = new IsolateMessage(port, raw_data, length);
  bool result = PortMap::PostMessage(message);

  RETURN_BOOL(result);
}


DEFINE_PRIMITIVE(MessageLoop_finish) {
  ASSERT(num_args == 1);
  MINT_ARGUMENT(new_wakeup, 0);
  I->isolate()->loop()->MessageEpilogue(new_wakeup);
  I->ReturnFromDispatch();
  I->Exit();
  UNREACHABLE();
  return kFailure;
}


DEFINE_PRIMITIVE(doPrimitiveWithArgs) {
  ASSERT(num_args == 3);
  SmallInteger primitive_index = static_cast<SmallInteger>(I->Stack(2));
  Object receiver = I->Stack(1);
  Array arguments = static_cast<Array>(I->Stack(0));

  if (!primitive_index->IsSmallInteger()) {
    return kFailure;
  }
  if (!arguments->IsArray()) {
    return kFailure;
  }

  intptr_t index = primitive_index->value();
  if (index == 133 ||  // currentActivation
      index == 90 ||  // Closure_value0
      index == 91 ||  // Closure_value1
      index == 92 ||  // Closure_value2
      index == 93 ||  // Closure_value3
      index == 94 ||  // Closure_valueArray
      index == 95 ||  // Activation_jump
      index == 89) {  // Object_performWithAll
    return kFailure;
  }

  intptr_t callee_num_args = arguments->Size();

  // TODO(rmacnak): We're repeating the accessor primitives in the interpreter
  // and here. We should invoke these uniformly.
  if ((index & 256) != 0) {
    // Getter
    intptr_t offset = index & 255;
    ASSERT(callee_num_args == 0);
    ASSERT(receiver->IsRegularObject() || receiver->IsEphemeron());
    Object value = static_cast<RegularObject>(receiver)->slot(offset);
    RETURN(value);
  } else if ((index & 512) != 0) {
    // Setter
    intptr_t offset = index & 255;
    ASSERT(callee_num_args == 1);
    Object value = arguments->element(0);
    ASSERT(receiver->IsRegularObject() || receiver->IsEphemeron());
    static_cast<RegularObject>(receiver)->set_slot(offset, value);
    RETURN(receiver);
  }

  intptr_t incoming_depth = I->StackDepth();

  I->Push(receiver);
  for (intptr_t i = 0; i < callee_num_args; i++) {
    if (arguments->element(i) == arguments) {
      FATAL("simulation error");
    }
    I->Push(arguments->element(i));
  }

  const uint8_t* initial_ip = I->IPForAssert();

  bool callee_success = Primitives::Invoke(index, callee_num_args, H, I);

  if (initial_ip != I->IPForAssert()) {
    // FP can move if the Activation setter primitives flush.
    FATAL1("Control flow in doPrimitiveWithArgs: %" Pd, index);
  }

  if (callee_success) {
    ASSERT(I->StackDepth() == incoming_depth + 1);
    Object result = I->Stack(0);
    I->PopNAndPush(num_args + 1 + 1, result);
    return kSuccess;
  } else {
    I->Drop(callee_num_args + 1);
    ASSERT(I->StackDepth() == incoming_depth);

    Object failure_token = I->Stack(0);  // Arguments array
    ASSERT(failure_token->IsArray());
    I->PopNAndPush(num_args + 1, failure_token);
    return kSuccess;
  }
}


DEFINE_PRIMITIVE(simulationRoot) {
  // This is a marker primitive for the non-local return and exception
  // signaling.
  return kFailure;
}


DEFINE_PRIMITIVE(MessageLoop_awaitSignal) {
  ASSERT(num_args == 2);
  SMI_ARGUMENT(handle, 1);
  SMI_ARGUMENT(signals, 0);
  intptr_t wait_id = I->isolate()->loop()->AwaitSignal(handle, signals);
  RETURN_SMI(wait_id);
}

DEFINE_PRIMITIVE(MessageLoop_cancelSignalWait) {
  ASSERT(num_args == 1);
  SMI_ARGUMENT(wait_id, 0);
  I->isolate()->loop()->CancelSignalWait(wait_id);
  RETURN_SELF();
}

#if defined(OS_FUCHSIA)
static zx_handle_t AsHandle(SmallInteger handle) {
  return static_cast<zx_handle_t>(handle->value());
}
#endif

DEFINE_PRIMITIVE(ZXStatus_getString) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 1);
  SMI_ARGUMENT(status, 0);
  const char* raw_string = zx_status_get_string(status);
  intptr_t length = strlen(raw_string);
  String result = H->AllocateString(length);  // SAFEPOINT
  memcpy(result->element_addr(0), raw_string, length);
  RETURN(result);
#endif
}

DEFINE_PRIMITIVE(ZXHandle_close) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 1);
  SmallInteger handle = static_cast<SmallInteger>(I->Stack(0));
  if (!handle->IsSmallInteger()) {
    return kFailure;
  }
  zx_status_t status = zx_handle_close(AsHandle(handle));
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXChannel_create) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 2);
  SmallInteger options = static_cast<SmallInteger>(I->Stack(1));
  if (!options->IsSmallInteger() || options->value() < 0) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 1)) {
    return kFailure;
  }
  zx_handle_t out0 = ZX_HANDLE_INVALID;
  zx_handle_t out1 = ZX_HANDLE_INVALID;
  zx_status_t status = zx_channel_create(options->value(), &out0, &out1);
  multiple_return->set_element(0, SmallInteger::New(out0));
  multiple_return->set_element(1, SmallInteger::New(out1));
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXChannel_read) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 2);
  SmallInteger channel = static_cast<SmallInteger>(I->Stack(1));
  if (!channel->IsSmallInteger()) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 2)) {
    return kFailure;
  }

  uint32_t actual_bytes = 0;
  uint32_t actual_handles = 0;
  zx_status_t status = zx_channel_read(AsHandle(channel), 0, nullptr, nullptr,
                                       0, 0, &actual_bytes, &actual_handles);
  if ((status != ZX_OK) && (status != ZX_ERR_BUFFER_TOO_SMALL)) {
    RETURN_SMI(status);
  }

  HandleScope h1(H, reinterpret_cast<Object*>(&multiple_return));
  ByteArray bytes = H->AllocateByteArray(actual_bytes);
  HandleScope h2(H, reinterpret_cast<Object*>(&bytes));
  Array handles = H->AllocateArray(actual_handles);

  zx_handle_t raw_handles[ZX_CHANNEL_MAX_MSG_HANDLES];

  if (status == ZX_ERR_BUFFER_TOO_SMALL) {
    status = zx_channel_read(AsHandle(channel), 0,
                             bytes->element_addr(0), raw_handles,
                             actual_bytes, actual_handles,
                             &actual_bytes, &actual_handles);
  }
  if (status == ZX_OK) {
    for (intptr_t i = 0; i < actual_handles; i++) {
      handles->set_element(i, SmallInteger::New(raw_handles[i]));
    }
    multiple_return->set_element(0, bytes);
    multiple_return->set_element(1, handles);
  }
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXChannel_write) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 4);
  SmallInteger channel = static_cast<SmallInteger>(I->Stack(3));
  if (!channel->IsSmallInteger()) {
    return kFailure;
  }
  ByteArray bytes = static_cast<ByteArray>(I->Stack(2));
  if (!bytes->IsByteArray()) {
    return kFailure;
  }
  Array handles = static_cast<Array>(I->Stack(1));
  if (!handles->IsArray()) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 2)) {
    return kFailure;
  }
  if (handles->Size() > ZX_CHANNEL_MAX_MSG_HANDLES) {
    RETURN_SMI(ZX_ERR_OUT_OF_RANGE);
  }
  zx_handle_t raw_handles[ZX_CHANNEL_MAX_MSG_HANDLES];
  for (intptr_t i = 0; i < handles->Size(); i++) {
    if (!handles->element(i)->IsSmallInteger()) {
      return kFailure;
    }
    raw_handles[i] = static_cast<SmallInteger>(handles->element(i))->value();
  }
  zx_status_t status = zx_channel_write(AsHandle(channel), 0,
                                        bytes->element_addr(0), bytes->Size(),
                                        raw_handles, handles->Size());
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXVmo_create) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 3);
  SmallInteger size = static_cast<SmallInteger>(I->Stack(2));
  if (!size->IsSmallInteger() || size->value() < 0) {
    return kFailure;
  }
  SmallInteger options = static_cast<SmallInteger>(I->Stack(1));
  if (!options->IsSmallInteger()) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 1)) {
    return kFailure;
  }
  zx_handle_t vmo = ZX_HANDLE_INVALID;
  zx_status_t status = zx_vmo_create(size->value(), options->value(), &vmo);
  multiple_return->set_element(0, SmallInteger::New(vmo));
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXVmo_getSize) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 2);
  SmallInteger vmo = static_cast<SmallInteger>(I->Stack(1));
  if (!vmo->IsSmallInteger()) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 1)) {
    return kFailure;
  }
  uint64_t size = 0;
  zx_status_t status = zx_vmo_get_size(AsHandle(vmo), &size);
  multiple_return->set_element(0, SmallInteger::New(size));
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXVmo_setSize) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 3);
  SmallInteger vmo = static_cast<SmallInteger>(I->Stack(2));
  if (!vmo->IsSmallInteger()) {
    return kFailure;
  }
  SmallInteger size = static_cast<SmallInteger>(I->Stack(1));
  if (!size->IsSmallInteger() || size->value() < 0) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 2)) {
    return kFailure;
  }
  zx_status_t status = zx_vmo_set_size(AsHandle(vmo), size->value());
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXVmo_read) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 4);
  SmallInteger vmo = static_cast<SmallInteger>(I->Stack(3));
  if (!vmo->IsSmallInteger()) {
    return kFailure;
  }
  SmallInteger size = static_cast<SmallInteger>(I->Stack(2));
  if (!size->IsSmallInteger() || size->value() < 0) {
    return kFailure;
  }
  SmallInteger offset = static_cast<SmallInteger>(I->Stack(1));
  if (!offset->IsSmallInteger() || offset->value() < 0) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 1)) {
    return kFailure;
  }
  HandleScope h1(H, reinterpret_cast<Object*>(&multiple_return));
  ByteArray buffer = H->AllocateByteArray(size->value());  // SAFEPOINT
  zx_status_t status = zx_vmo_read(AsHandle(vmo), buffer->element_addr(0),
                                   offset->value(), size->value());
  multiple_return->set_element(0, buffer);
  RETURN_SMI(status);
#endif
}

DEFINE_PRIMITIVE(ZXVmo_write) {
#if !defined(OS_FUCHSIA)
  return kFailure;
#else
  ASSERT(num_args == 4);
  SmallInteger vmo = static_cast<SmallInteger>(I->Stack(3));
  if (!vmo->IsSmallInteger()) {
    return kFailure;
  }
  ByteArray buffer = static_cast<ByteArray>(I->Stack(2));
  if (!buffer->IsByteArray()) {
    return kFailure;
  }
  SmallInteger offset = static_cast<SmallInteger>(I->Stack(1));
  if (!offset->IsSmallInteger() || offset->value() < 0) {
    return kFailure;
  }
  Array multiple_return = static_cast<Array>(I->Stack(0));
  if (!multiple_return->IsArray() || (multiple_return->Size() < 1)) {
    return kFailure;
  }
  zx_status_t status = zx_vmo_write(AsHandle(vmo), buffer->element_addr(0),
                                    offset->value(), buffer->Size());
  RETURN_SMI(status);
#endif
}

#if defined(OS_EMSCRIPTEN)
EM_JS(void, _JS_pushInteger, (int64_t value), {
  var aliens = Module.aliens;
  aliens.push(value);
});
EM_JS(void, _JS_pushFloat, (double value), {
  var aliens = Module.aliens;
  aliens.push(value);
});
EM_JS(void, _JS_pushString, (intptr_t addr, intptr_t size), {
  var aliens = Module.aliens;
  var value = UTF8ToString(addr, size);
  aliens.push(value);
});
EM_JS(void, _JS_pushAlien, (intptr_t index), {
  var aliens = Module.aliens;
  aliens.push(aliens[index]);
});
EM_JS(void, _JS_pushExpat, (intptr_t index), {
  var aliens = Module.aliens;
  function expat() {
    for (var i = 0; i < arguments.length; i++) {
      aliens.push(arguments[i]);
    }
    Module._handle_signal(index, arguments.length, 0, 0);
    return aliens.pop();
  }
  aliens.push(expat);
});
EM_JS(int, _JS_peekType, (), {
  var aliens = Module.aliens;
  var alien = aliens[aliens.length - 1];
  if (null === alien) {
    return -1;
  }
  if (false === alien) {
    return -2;
  }
  if (true === alien) {
    return -3;
  }
  if (typeof alien === "number") {
    return Number.isInteger(alien) ? -4 : -5;
  }
  if (typeof alien === "string") {
    return lengthBytesUTF8(alien);
  }
  return -6;
});
EM_JS(intptr_t, _JS_popInteger, (), {
  var aliens = Module.aliens;
  return aliens.pop();
});
EM_JS(double, _JS_popFloat, (), {
  var aliens = Module.aliens;
  return aliens.pop();
});
EM_JS(void, _JS_popString, (intptr_t addr, intptr_t size), {
  var aliens = Module.aliens;
  var string = aliens.pop();
  // TODO(rmacnak): This will write a terminating NUL past the end of our
  // String object.
  stringToUTF8(string, addr, size + 1);
});
EM_JS(intptr_t, _JS_peekAlien, (), {
  var aliens = Module.aliens;
  var lastIndex = aliens.length - 1;
  if (undefined === aliens[lastIndex]) {
    aliens.pop();
    return 0;
  } else {
    return lastIndex;
  }
});
EM_JS(intptr_t, _JS_peekExpat, (), {
  throw "Unimplemented";
});
EM_JS(bool, _JS_performGet, (), {
  var aliens = Module.aliens;
  var selector = aliens.pop();
  var receiver = aliens.pop();
  try {
    var result = Reflect.get(receiver, selector);
    aliens.push(result);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
EM_JS(bool, _JS_performSet, (), {
  var aliens = Module.aliens;
  var argument = aliens.pop();
  var selector = aliens.pop();
  var receiver = aliens.pop();
  try {
    var result = Reflect.set(receiver, selector, argument);
    aliens.push(argument);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
EM_JS(bool, _JS_performDelete, (), {
  var aliens = Module.aliens;
  var selector = aliens.pop();
  var receiver = aliens.pop();
  try {
    var result = Reflect.deleteProperty(receiver, selector);
    aliens.push(result);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
EM_JS(bool, _JS_performInvoke, (intptr_t numArgs), {
  var aliens = Module.aliens;
  var arguments = new Array(numArgs);
  for (var i = numArgs - 1; i >= 0; i--) {
    arguments[i] = aliens.pop();
  }
  var selector = aliens.pop();
  var receiver = aliens.pop();
  if ((undefined === receiver) ||
      (undefined === receiver[selector])) {
    aliens.push("NoSuchMethod: " + selector);
    return false;
  }
  try {
    var result = Reflect.apply(receiver[selector], receiver, arguments);
    aliens.push(result);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
EM_JS(bool, _JS_performNew, (intptr_t numArgs), {
  var aliens = Module.aliens;
  var arguments = new Array(numArgs);
  for (var i = numArgs - 1; i >= 0; i--) {
    arguments[i] = aliens.pop();
  }
  var receiver = aliens.pop();
  try {
    var result = Reflect.construct(receiver, arguments);
    aliens.push(result);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
EM_JS(bool, _JS_performInstanceOf, (), {
  var aliens = Module.aliens;
  var constructor = aliens.pop();
  var receiver = aliens.pop();
  try {
    var result = receiver instanceof constructor;
    aliens.push(result);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
EM_JS(bool, _JS_performHas, (), {
  var aliens = Module.aliens;
  var selector = aliens.pop();
  var receiver = aliens.pop();
  try {
    var result = Reflect.has(receiver, selector);
    aliens.push(result);
    return true;
  } catch (exception) {
    aliens.push(exception);
    return false;
  }
});
#endif  // defined(OS_EMSCRIPTEN)

DEFINE_PRIMITIVE(JS_pushValue) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 1);
  Object object = I->Stack(0);
  if (object->IsSmallInteger()) {
    intptr_t value = static_cast<SmallInteger>(object)->value();
    _JS_pushInteger(value);
    RETURN_SELF();
  }
  if (object->IsMediumInteger()) {
    int64_t value = static_cast<MediumInteger>(object)->value();
    _JS_pushInteger(value);
    RETURN_SELF();
  }
  if (object->IsFloat64()) {
    double value = static_cast<Float64>(object)->value();
    _JS_pushFloat(value);
    RETURN_SELF();
  }
  if (object->IsString()) {
    intptr_t size = static_cast<String>(object)->Size();
    uint8_t* addr = static_cast<String>(object)->element_addr(0);
    _JS_pushString(reinterpret_cast<intptr_t>(addr), size);
    RETURN_SELF();
  }
  if (object == I->nil_obj()) {
    _JS_pushAlien(1);
    RETURN_SELF();
  }
  if (object == I->false_obj()) {
    _JS_pushAlien(2);
    RETURN_SELF();
  }
  if (object == I->true_obj()) {
    _JS_pushAlien(3);
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_pushAlien) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 1);
  SMI_ARGUMENT(index, 0);
  _JS_pushAlien(index);
  RETURN_SELF();
#endif
}

DEFINE_PRIMITIVE(JS_pushExpat) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 1);
  SMI_ARGUMENT(index, 0);
  _JS_pushExpat(index);
  RETURN_SELF();
#endif
}

DEFINE_PRIMITIVE(JS_popValue) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  intptr_t type = _JS_peekType();
  if (type == -1) {
    RETURN(I->nil_obj());
  } else if (type == -2) {
    RETURN(I->false_obj());
  } else if (type == -3) {
    RETURN(I->true_obj());
  } else if (type == -4) {
    intptr_t value = _JS_popInteger();
    RETURN_MINT(value);
  } else if (type == -5) {
    double value = _JS_popFloat();
    RETURN_FLOAT(value);
  } else if (type >= 0) {
    intptr_t size = type;
    String result = H->AllocateString(size);  // SAFEPOINT
    uint8_t* addr = result->element_addr(0);
    _JS_popString(reinterpret_cast<intptr_t>(addr), size);
    RETURN(result);
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_peekAlien) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  intptr_t index = _JS_peekAlien();
  RETURN_SMI(index);
#endif
}

DEFINE_PRIMITIVE(JS_peekExpat) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  intptr_t index = _JS_peekExpat();
  RETURN_SMI(index);
#endif
}

DEFINE_PRIMITIVE(JS_performGet) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  if (_JS_performGet()) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_performSet) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  if (_JS_performSet()) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_performDelete) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  if (_JS_performDelete()) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_performInvoke) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 1);
  SMI_ARGUMENT(js_num_args, 0);
  if (_JS_performInvoke(js_num_args)) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_performNew) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 1);
  SMI_ARGUMENT(js_num_args, 0);
  if (_JS_performNew(js_num_args)) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_performInstanceOf) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  if (_JS_performInstanceOf()) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(JS_performHas) {
#if !defined(OS_EMSCRIPTEN)
  return kFailure;
#else
  ASSERT(num_args == 0);
  if (_JS_performHas()) {
    RETURN_SELF();
  }
  return kFailure;
#endif
}

DEFINE_PRIMITIVE(quickReturnSelf) {
  ASSERT(num_args == 0);
  return kSuccess;
}


PrimitiveFunction** Primitives::primitive_table_ = NULL;


void Primitives::Startup() {
  primitive_table_ = new PrimitiveFunction*[kNumPrimitives];
  for (intptr_t i = 0; i < kNumPrimitives; i++) {
    primitive_table_[i] = primitiveUnimplemented;
  }
#define ADD_PRIMITIVE(number, name)                                            \
  primitive_table_[number] = primitive##name;
PRIMITIVE_LIST(ADD_PRIMITIVE);
#undef ADD_PRIMITIVE
}


void Primitives::Shutdown() {
  delete[] primitive_table_;
  primitive_table_ = NULL;
}

}  // namespace psoup
