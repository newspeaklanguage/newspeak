// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_LOOKUP_CACHE_H_
#define VM_LOOKUP_CACHE_H_

#include "globals.h"
#include "object.h"

namespace psoup {

enum LookupRule {
  kSelf = 0,
  kSuper = 256,
  kImplicitReceiver = 257,
  kMNU = 258,
};

class LookupCache {
 public:
  LookupCache() {
    Clear();
  }

  INLINE
  bool LookupOrdinary(intptr_t cid,
                      String selector,
                      Method* target) {
    intptr_t hash = cid
        ^ (static_cast<intptr_t>(selector) >> kObjectAlignmentLog2);

    intptr_t probe1 = hash & kMask;
    if (entries_[probe1].ordinary_cid == cid &&
        entries_[probe1].ordinary_selector == selector) {
      *target = entries_[probe1].ordinary_target;
      return true;
    }

    intptr_t probe2 = (hash >> 3) & kMask;
    if (entries_[probe2].ordinary_cid == cid &&
        entries_[probe2].ordinary_selector == selector) {
      *target = entries_[probe2].ordinary_target;
      return true;
    }

    return false;
  }

  void InsertOrdinary(intptr_t cid,
                      String selector,
                      Method target);

  INLINE
  bool LookupNS(intptr_t cid,
                String selector,
                Method caller,
                intptr_t rule,
                Object* absent_receiver,
                Method* target) {
    intptr_t hash = cid
        ^ (static_cast<intptr_t>(selector) >> kObjectAlignmentLog2)
        ^ (static_cast<intptr_t>(caller) >> kObjectAlignmentLog2);
    intptr_t cid_and_rule = (cid << 16) | rule;

    intptr_t probe1 = hash & kMask;
    if (entries_[probe1].ns_cid_and_rule == cid_and_rule &&
        entries_[probe1].ns_selector == selector &&
        entries_[probe1].ns_caller == caller) {
      *absent_receiver = entries_[probe1].ns_absent_receiver;
      *target = entries_[probe1].ns_target;
      return true;
    }

    intptr_t probe2 = (hash >> 3) & kMask;
    if (entries_[probe2].ns_cid_and_rule == cid_and_rule &&
        entries_[probe2].ns_selector == selector &&
        entries_[probe2].ns_caller == caller) {
      *absent_receiver = entries_[probe2].ns_absent_receiver;
      *target = entries_[probe2].ns_target;
      return true;
    }

    return false;
  }

  void InsertNS(intptr_t cid,
                String selector,
                Method caller,
                intptr_t rule,
                Object absent_receiver,
                Method target);

  void Clear();

 private:
  struct Entry {
    intptr_t ordinary_cid;
    String ordinary_selector;
    Method ordinary_target;

    intptr_t ns_cid_and_rule;
    String ns_selector;
    Method ns_caller;
    Object ns_absent_receiver;
    Method ns_target;
  };

  static const intptr_t kSize = 512;
  static const intptr_t kMask = kSize - 1;

  Entry entries_[kSize];
};

}  // namespace psoup

#endif  // VM_LOOKUP_CACHE_H_
