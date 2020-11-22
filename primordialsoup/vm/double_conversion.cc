// Copyright (c) 2011, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "double_conversion.h"

#include "assert.h"

#include "../double-conversion/double-conversion.h"

namespace psoup {

static const char kDoubleToStringCommonExponentChar = 'e';
static const char* kDoubleToStringCommonInfinitySymbol = "Infinity";
static const char* kDoubleToStringCommonNaNSymbol = "NaN";

int DoubleToCStringAsShortest(double d, char* buffer, int buffer_size) {
  static const int kDecimalLow = -6;
  static const int kDecimalHigh = 21;

  // The output contains the sign, at most kDecimalHigh - 1 digits,
  // the decimal point followed by a 0 plus the \0.
  ASSERT(buffer_size >= 1 + (kDecimalHigh - 1) + 1 + 1 + 1);
  // Or it contains the sign, a 0, the decimal point, kDecimalLow '0's,
  // 17 digits (the precision needed for doubles), plus the \0.
  ASSERT(buffer_size >= 1 + 1 + 1 + kDecimalLow + 17 + 1);
  // Alternatively it contains a sign, at most 17 digits (precision needed for
  // any double), the decimal point, the exponent character, the exponent's
  // sign, at most three exponent digits, plus the \0.
  ASSERT(buffer_size >= 1 + 17 + 1 + 1 + 1 + 3 + 1);

  static const int kConversionFlags =
      double_conversion::DoubleToStringConverter::EMIT_POSITIVE_EXPONENT_SIGN |
      double_conversion::DoubleToStringConverter::EMIT_TRAILING_DECIMAL_POINT |
     double_conversion::DoubleToStringConverter::EMIT_TRAILING_ZERO_AFTER_POINT;

  const double_conversion::DoubleToStringConverter converter(
      kConversionFlags,
      kDoubleToStringCommonInfinitySymbol,
      kDoubleToStringCommonNaNSymbol,
      kDoubleToStringCommonExponentChar,
      kDecimalLow,
      kDecimalHigh,
      0, 0);  // Last two values are ignored in shortest mode.

  double_conversion::StringBuilder builder(buffer, buffer_size);
  bool status = converter.ToShortest(d, &builder);
  ASSERT(status);
  return builder.position();
}

int DoubleToCStringAsFixed(double d, int fraction_digits,
                           char* buffer, int buffer_size) {
  static const int kMinFractionDigits = 0;
  static const int kMaxFractionDigits = 20;
  static const int kMaxDigitsBeforePoint = 20;
  // The boundaries are exclusive.
  static const double kLowerBoundary = -1e21;
  static const double kUpperBoundary = 1e21;
  static const int kConversionFlags =
      double_conversion::DoubleToStringConverter::NO_FLAGS;

  // The output contains the sign, at most kMaxDigitsBeforePoint digits,
  // the decimal point followed by at most fraction_digits digits plus the \0.
  ASSERT(buffer_size >= 1 + kMaxDigitsBeforePoint + 1 + kMaxFractionDigits + 1);

  ASSERT(kLowerBoundary < d && d < kUpperBoundary);

  ASSERT(kMinFractionDigits <= fraction_digits &&
         fraction_digits <= kMaxFractionDigits);

  const double_conversion::DoubleToStringConverter converter(
      kConversionFlags, kDoubleToStringCommonInfinitySymbol,
      kDoubleToStringCommonNaNSymbol, kDoubleToStringCommonExponentChar, 0, 0,
      0, 0);  // Last four values are ignored in fixed mode.

  double_conversion::StringBuilder builder(buffer, buffer_size);
  bool status = converter.ToFixed(d, fraction_digits, &builder);
  ASSERT(status);
  return builder.position();
}

int DoubleToCStringAsExponential(double d, int fraction_digits,
                                 char* buffer, int buffer_size) {
  static const int kMinFractionDigits = -1;  // -1 represents shortest mode.
  static const int kMaxFractionDigits = 20;
  static const int kConversionFlags =
      double_conversion::DoubleToStringConverter::EMIT_POSITIVE_EXPONENT_SIGN;

  // The output contains the sign, at most 1 digits, the decimal point followed
  // by at most kMaxFractionDigits digits, the exponent-character, the
  // exponent-sign and three exponent digits plus \0.
  ASSERT(buffer_size >= 1 + 1 + kMaxFractionDigits + 1 + 1 + 3 + 1);

  ASSERT(kMinFractionDigits <= fraction_digits &&
         fraction_digits <= kMaxFractionDigits);

  const double_conversion::DoubleToStringConverter converter(
      kConversionFlags, kDoubleToStringCommonInfinitySymbol,
      kDoubleToStringCommonNaNSymbol, kDoubleToStringCommonExponentChar, 0, 0,
      0, 0);  // Last four values are ignored in exponential mode.

  double_conversion::StringBuilder builder(buffer, buffer_size);
  bool status = converter.ToExponential(d, fraction_digits, &builder);
  ASSERT(status);
  return builder.position();
}

int DoubleToCStringAsPrecision(double d, int precision,
                               char* buffer, int buffer_size) {
  static const int kMinPrecisionDigits = 1;
  static const int kMaxPrecisionDigits = 21;
  static const int kMaxLeadingPaddingZeroes = 6;
  static const int kMaxTrailingPaddingZeroes = 0;
  static const int kConversionFlags =
      double_conversion::DoubleToStringConverter::EMIT_POSITIVE_EXPONENT_SIGN;

  // The output contains the sign, a potential leading 0, the decimal point,
  // at most kMax{Leading|Trailing} padding zeroes, precision digits,
  // the exponent-character, the exponent-sign, three exponent digits
  // plus the \0.
  // Note that padding and exponent are exclusive. We still add them up.
  ASSERT(buffer_size >= 1 + 1 + 1 + kMaxLeadingPaddingZeroes +
                            kMaxTrailingPaddingZeroes + kMaxPrecisionDigits +
                            1 + 1 + 3 + 1);

  ASSERT(kMinPrecisionDigits <= precision && precision <= kMaxPrecisionDigits);

  const double_conversion::DoubleToStringConverter converter(
      kConversionFlags, kDoubleToStringCommonInfinitySymbol,
      kDoubleToStringCommonNaNSymbol, kDoubleToStringCommonExponentChar, 0,
      0,  // Ignored in precision mode.
      kMaxLeadingPaddingZeroes, kMaxTrailingPaddingZeroes);

  double_conversion::StringBuilder builder(buffer, buffer_size);
  bool status = converter.ToPrecision(d, precision, &builder);
  ASSERT(status);
  return builder.position();
}

bool CStringToDouble(const char* str, int length, double* result) {
  if (length == 0) {
    return false;
  }

  double_conversion::StringToDoubleConverter converter(
    double_conversion::StringToDoubleConverter::NO_FLAGS,
    0.0,
    0.0,
    kDoubleToStringCommonInfinitySymbol,
    kDoubleToStringCommonNaNSymbol);

  int parsed_count = 0;
  *result = converter.StringToDouble(str, length, &parsed_count);
  return (parsed_count == length);
}

}  // namespace psoup
