// Copyright (c) 2011, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_DOUBLE_CONVERSION_H_
#define VM_DOUBLE_CONVERSION_H_

#include "globals.h"

namespace psoup {

int DoubleToCStringAsShortest(double d, char* buffer, int buffer_size);
int DoubleToCStringAsFixed(double d, int fraction_digits,
                           char* buffer, int buffer_size);
int DoubleToCStringAsExponential(double d, int fraction_digits,
                                 char* buffer, int buffer_size);
int DoubleToCStringAsPrecision(double d, int precision,
                               char* buffer, int buffer_size);
bool CStringToDouble(const char* str, int length, double* result);

}  // namespace psoup

#endif  // VM_DOUBLE_CONVERSION_H_
