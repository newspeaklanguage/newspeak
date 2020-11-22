// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "lookup_cache.h"

namespace psoup {

void LookupCache::InsertOrdinary(intptr_t cid,
                                 String selector,
                                 Method target) {
  intptr_t hash = cid
      ^ (static_cast<intptr_t>(selector) >> kObjectAlignmentLog2);

  intptr_t probe1 = hash & kMask;
  entries_[probe1].ordinary_cid = cid;
  entries_[probe1].ordinary_selector = selector;
  entries_[probe1].ordinary_target = target;

  intptr_t probe2 = (hash >> 3) & kMask;
  entries_[probe2].ordinary_cid = cid;
  entries_[probe2].ordinary_selector = selector;
  entries_[probe2].ordinary_target = target;
}


void LookupCache::InsertNS(intptr_t cid,
                           String selector,
                           Method caller,
                           intptr_t rule,
                           Object absent_receiver,
                           Method target) {
  intptr_t hash = cid
      ^ (static_cast<intptr_t>(selector) >> kObjectAlignmentLog2)
      ^ (static_cast<intptr_t>(caller) >> kObjectAlignmentLog2);
  intptr_t cid_and_rule = (cid << 16) | rule;

  intptr_t probe1 = hash & kMask;
  entries_[probe1].ns_cid_and_rule = cid_and_rule;
  entries_[probe1].ns_selector = selector;
  entries_[probe1].ns_caller = caller;
  entries_[probe1].ns_target = target;
  entries_[probe1].ns_absent_receiver = absent_receiver;

  intptr_t probe2 = (hash >> 3) & kMask;
  entries_[probe2].ns_cid_and_rule = cid_and_rule;
  entries_[probe2].ns_selector = selector;
  entries_[probe2].ns_caller = caller;
  entries_[probe2].ns_target = target;
  entries_[probe2].ns_absent_receiver = absent_receiver;
}


void LookupCache::Clear() {
  for (intptr_t i = 0; i < kSize; i++) {
    entries_[i].ordinary_cid = kIllegalCid;
    entries_[i].ns_cid_and_rule = kIllegalCid << 16;
  }
}

}  // namespace psoup
