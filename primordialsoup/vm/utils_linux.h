// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_UTILS_LINUX_H_
#define VM_UTILS_LINUX_H_

namespace psoup {

inline char* Utils::StrError(int err, char* buffer, size_t bufsize) {
#if !defined(__GLIBC__) ||                                              \
((_POSIX_C_SOURCE >= 200112L || _XOPEN_SOURCE >= 600) && !_GNU_SOURCE)
  // Use the XSI version.
  if (strerror_r(err, buffer, bufsize) != 0) {
    snprintf(buffer, bufsize, "%s", "strerror_r failed");
  }
  return buffer;
#else
  // Use the GNU specific version.
  return strerror_r(err, buffer, bufsize);
#endif
}

}  // namespace psoup

#endif  // VM_UTILS_LINUX_H_
