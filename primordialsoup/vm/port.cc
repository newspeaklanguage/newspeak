// Copyright (c) 2012, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "port.h"

#include "flags.h"
#include "lockers.h"
#include "message_loop.h"
#include "os.h"
#include "random.h"
#include "thread.h"
#include "utils.h"

namespace psoup {

Mutex* PortMap::mutex_ = NULL;
PortMap::Entry* PortMap::map_ = NULL;
MessageLoop* PortMap::deleted_entry_ = reinterpret_cast<MessageLoop*>(1);
intptr_t PortMap::capacity_ = 0;
intptr_t PortMap::used_ = 0;
intptr_t PortMap::deleted_ = 0;
Random* PortMap::prng_ = NULL;


intptr_t PortMap::FindPort(Port port) {
  // ILLEGAL_PORT (0) is used as a sentinel value in Entry.port. The loop below
  // could return the index to a deleted port when we are searching for
  // port id ILLEGAL_PORT. Return -1 immediately to indicate the port
  // does not exist.
  if (port == ILLEGAL_PORT) {
    return -1;
  }
  ASSERT(port != ILLEGAL_PORT);
  intptr_t index = port % capacity_;
  intptr_t start_index = index;
  Entry entry = map_[index];
  while (entry.loop != NULL) {
    if (entry.port == port) {
      return index;
    }
    index = (index + 1) % capacity_;
    // Prevent endless loops.
    ASSERT(index != start_index);
    entry = map_[index];
  }
  return -1;
}


void PortMap::Rehash(intptr_t new_capacity) {
  Entry* new_ports = new Entry[new_capacity];
  memset(new_ports, 0, new_capacity * sizeof(Entry));

  for (intptr_t i = 0; i < capacity_; i++) {
    Entry entry = map_[i];
    // Skip free and deleted entries.
    if (entry.port != 0) {
      intptr_t new_index = entry.port % new_capacity;
      while (new_ports[new_index].port != 0) {
        new_index = (new_index + 1) % new_capacity;
      }
      new_ports[new_index] = entry;
    }
  }
  delete[] map_;
  map_ = new_ports;
  capacity_ = new_capacity;
  deleted_ = 0;
}


Port PortMap::AllocatePort() {
  Port result = prng_->NextUInt64() & kMaxInt64;

  // Keep getting new values while we have an illegal port number or the port
  // number is already in use.
  while ((result == ILLEGAL_PORT) || (FindPort(result) >= 0)) {
    result = prng_->NextUInt64() & kMaxInt64;
  }

  ASSERT(result != 0);
  ASSERT(FindPort(result) < 0);
  return result;
}


void PortMap::MaintainInvariants() {
  intptr_t empty = capacity_ - used_ - deleted_;
  if (used_ > ((capacity_ / 4) * 3)) {
    // Grow the port map.
    Rehash(capacity_ * 2);
  } else if (empty < deleted_) {
    // Rehash without growing the table to flush the deleted slots out of the
    // map.
    Rehash(capacity_);
  }
}


Port PortMap::CreatePort(MessageLoop* loop) {
  ASSERT(loop != NULL);
  MutexLocker ml(mutex_);
#if defined(DEBUG)
  /// queue->CheckAccess();
#endif

  Entry entry;
  entry.port = AllocatePort();
  entry.loop = loop;
  /// entry.state = kNewPort;

  // Search for the first unused slot. Make use of the knowledge that here is
  // currently no port with this id in the port map.
  ASSERT(FindPort(entry.port) < 0);
  intptr_t index = entry.port % capacity_;
  Entry cur = map_[index];
  // Stop the search at the first found unused (free or deleted) slot.
  while (cur.port != 0) {
    index = (index + 1) % capacity_;
    cur = map_[index];
  }

  // Insert the newly created port at the index.
  ASSERT(index >= 0);
  ASSERT(index < capacity_);
  ASSERT(map_[index].port == 0);
  ASSERT((map_[index].loop == NULL) ||
         (map_[index].loop == deleted_entry_));
  if (map_[index].loop == deleted_entry_) {
    // Consuming a deleted entry.
    deleted_--;
  }
  map_[index] = entry;

  // Increment number of used slots and grow if necessary.
  used_++;
  MaintainInvariants();

  return entry.port;
}


bool PortMap::PostMessage(IsolateMessage* message) {
  MutexLocker ml(mutex_);
  intptr_t index = FindPort(message->dest_port());
  if (index < 0) {
    delete message;
    return false;
  }
  ASSERT(index >= 0);
  ASSERT(index < capacity_);
  MessageLoop* loop = map_[index].loop;
  ASSERT(map_[index].port != 0);
  ASSERT((loop != NULL) && (loop != deleted_entry_));
  loop->PostMessage(message);
  return true;
}


bool PortMap::ClosePort(Port port) {
  MutexLocker ml(mutex_);
  intptr_t index = FindPort(port);
  if (index < 0) {
    return false;
  }
  ASSERT(index < capacity_);
  ASSERT(map_[index].port != 0);
  ASSERT(map_[index].loop != deleted_entry_);
  ASSERT(map_[index].loop != NULL);

  map_[index].port = 0;
  map_[index].loop = deleted_entry_;

  used_--;
  deleted_++;
  MaintainInvariants();
  return true;
}


void PortMap::CloseAllPorts(MessageLoop* loop) {
  MutexLocker ml(mutex_);
  for (intptr_t index = 0; index < capacity_; index++) {
    if (map_[index].loop == loop) {
      ASSERT(map_[index].port != 0);
      map_[index].port = 0;
      map_[index].loop = deleted_entry_;
      used_--;
      deleted_++;
    }
  }
  MaintainInvariants();
}


void PortMap::Startup() {
  mutex_ = new Mutex();
  prng_ = new Random(OS::CurrentMonotonicNanos());

  static const intptr_t kInitialCapacity = 8;
  // TODO(iposva): Verify whether we want to keep exponentially growing.
  ASSERT(Utils::IsPowerOfTwo(kInitialCapacity));
  map_ = new Entry[kInitialCapacity];
  memset(map_, 0, kInitialCapacity * sizeof(Entry));
  capacity_ = kInitialCapacity;
  used_ = 0;
  deleted_ = 0;
}


void PortMap::Shutdown() {
  delete mutex_;
  mutex_ = NULL;
  delete prng_;
  prng_ = NULL;
  delete[] map_;
  map_ = NULL;
}

}  // namespace psoup
