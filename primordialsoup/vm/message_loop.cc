// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "message_loop.h"

#include "isolate.h"
#include "os.h"

namespace psoup {

MessageLoop::MessageLoop(Isolate* isolate)
    : isolate_(isolate), open_ports_(0), open_waits_(0), exit_code_(0) {}

MessageLoop::~MessageLoop() {}

void MessageLoop::DispatchMessage(IsolateMessage* message) {
  if (isolate_ == NULL) {
    delete message;
    return;
  }

  isolate_->ActivateMessage(message);
  delete message;
  isolate_->Interpret();
}

void MessageLoop::DispatchWakeup() {
  if (isolate_ == NULL) {
    return;
  }

  isolate_->ActivateWakeup();
  isolate_->Interpret();
}

void MessageLoop::DispatchSignal(intptr_t handle,
                                 intptr_t status,
                                 intptr_t signals,
                                 intptr_t count) {
  if (isolate_ == NULL) {
    return;
  }

  isolate_->ActivateSignal(handle, status, signals, count);
  isolate_->Interpret();
}

Port MessageLoop::OpenPort() {
  open_ports_++;
  return PortMap::CreatePort(this);
}

void MessageLoop::ClosePort(Port port) {
  if (PortMap::ClosePort(port)) {
    open_ports_--;
  }
}

}  // namespace psoup
