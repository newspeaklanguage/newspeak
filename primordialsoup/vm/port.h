// Copyright (c) 2011, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#ifndef VM_PORT_H_
#define VM_PORT_H_

#include "globals.h"
#include "allocation.h"

namespace psoup {

typedef int64_t Port;
#define ILLEGAL_PORT 0

class IsolateMessage;
class MessageLoop;
class Mutex;
class Random;

class PortMap : public AllStatic {
 public:
  static Port CreatePort(MessageLoop* loop);
  static bool PostMessage(IsolateMessage* message);
  static bool ClosePort(Port port);
  static void CloseAllPorts(MessageLoop* loop);

  static void Startup();
  static void Shutdown();

 private:
  // Allocate a new unique port.
  static Port AllocatePort();

  static intptr_t FindPort(Port port);
  static void Rehash(intptr_t new_capacity);

  static void MaintainInvariants();

  typedef struct {
    Port port;
    MessageLoop* loop;
  } Entry;

  static Mutex* mutex_;

  static Entry* map_;
  static MessageLoop* deleted_entry_;
  static intptr_t capacity_;
  static intptr_t used_;
  static intptr_t deleted_;

  static Random* prng_;
};

}  // namespace psoup

#endif  // VM_PORT_H_
