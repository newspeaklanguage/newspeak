import Newspeak.ActorSystemSteps

namespace Newspeak

def ValueTransferDeterministic (transfer : ValueTransferRelation) : Prop :=
  ∀ world source destination object after₁ represented₁ after₂ represented₂,
    transfer world source destination object after₁ represented₁ →
    transfer world source destination object after₂ represented₂ →
    after₁ = after₂ ∧ represented₁ = represented₂

theorem RemoteRepresentation.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {world : ActorWorld} {source destination : ActorId}
    {reference : EventualRef} {after₁ after₂ : ActorWorld}
    {represented₁ represented₂ : EventualRef}
    (first : RemoteRepresentation isValue valueTransfer world source destination
      reference after₁ represented₁)
    (second : RemoteRepresentation isValue valueTransfer world source destination
      reference after₂ represented₂) :
    after₁ = after₂ ∧ represented₁ = represented₂ := by
  cases first <;> cases second <;> try {simp_all}
  case value.value representedObject₁ _ _ transfer₁ representedObject₂ _ _ transfer₂ =>
    rcases transferDeterministic _ _ _ _ _ _ _ _ transfer₁ transfer₂ with
      ⟨worldEqual, objectEqual⟩
    exact ⟨worldEqual, by simpa using objectEqual⟩

theorem RemoteArgumentListRepresentation.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {source destination : ActorId} {world : ActorWorld}
    {arguments : List EventualRef} {after₁ after₂ : ActorWorld}
    {represented₁ represented₂ : List EventualRef}
    (first : RemoteArgumentListRepresentation isValue valueTransfer
      source destination world arguments after₁ represented₁)
    (second : RemoteArgumentListRepresentation isValue valueTransfer
      source destination world arguments after₂ represented₂) :
    after₁ = after₂ ∧ represented₁ = represented₂ := by
  induction first generalizing after₂ represented₂ with
  | nil =>
      cases second
      exact ⟨rfl, rfl⟩
  | @cons world middle₁ after₁ argument representedArgument₁ arguments
      representedArguments₁ head₁ tail₁ ih =>
      cases second with
      | @cons _ middle₂ after₂ _ representedArgument₂ _
          representedArguments₂ head₂ tail₂ =>
          rcases head₁.deterministic transferDeterministic head₂ with
            ⟨middleEqual, argumentEqual⟩
          subst middle₂
          rcases ih tail₂ with ⟨afterEqual, tailEqual⟩
          subst after₂
          subst representedArgument₂
          subst representedArguments₂
          exact ⟨rfl, rfl⟩

theorem RemoteMessageRepresentation.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {source destination : ActorId} {world : ActorWorld}
    {message : EventualMessage} {after₁ after₂ : ActorWorld}
    {represented₁ represented₂ : EventualMessage}
    (first : RemoteMessageRepresentation isValue valueTransfer source
      destination world message after₁ represented₁)
    (second : RemoteMessageRepresentation isValue valueTransfer source
      destination world message after₂ represented₂) :
    after₁ = after₂ ∧ represented₁ = represented₂ := by
  cases first with
  | message arguments₁ =>
      cases second with
      | message arguments₂ =>
          rcases arguments₁.deterministic transferDeterministic arguments₂ with
            ⟨worldEqual, argumentsEqual⟩
          cases worldEqual
          cases argumentsEqual
          exact ⟨rfl, rfl⟩

theorem PromiseSettlement.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {world : ActorWorld} {promise : PromiseId}
    {disposition : SettlementDisposition} {source : ActorId}
    {result : EventualRef} {history : List EventId}
    {after₁ after₂ : ActorWorld}
    (first : PromiseSettlement isValue valueTransfer world promise disposition
      source result history after₁)
    (second : PromiseSettlement isValue valueTransfer world promise disposition
      source result history after₂) : after₁ = after₂ := by
  cases first with
  | @settle world representedWorld₁ promise owner₁ source waiters₁ disposition result
      represented₁ history pending₁ subset₁ representation₁ result₁ =>
      cases second with
      | @settle _ representedWorld₂ _ owner₂ _ waiters₂ _ _ represented₂ _
          pending₂ subset₂ representation₂ result₂ =>
          have pendingEqual := Option.some.inj (pending₁.symm.trans pending₂)
          have stateParts := PromiseState.pending.inj pendingEqual
          rcases stateParts with ⟨ownerEqual, waitersEqual⟩
          subst owner₂
          subst waiters₂
          rcases representation₁.deterministic transferDeterministic
              representation₂ with ⟨worldEqual, representedEqual⟩
          cases worldEqual
          cases representedEqual
          exact result₁.trans result₂.symm

theorem RouteEventualMessage.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {world : ActorWorld} {requester : ActorId} {receiver : EventualRef}
    {message : EventualMessage} {resultPromise : PromiseId}
    {history : List EventId} {after₁ after₂ : ActorWorld}
    (first : RouteEventualMessage isValue valueTransfer world requester receiver
      message resultPromise history after₁)
    (second : RouteEventualMessage isValue valueTransfer world requester receiver
      message resultPromise history after₂) : after₁ = after₂ := by
  induction first generalizing after₂ with
  | @target world representedWorld₁ after₁ requester targetActor₁ receiver
      targetObject₁ message representedMessage₁ resultPromise history
      target₁ representation₁ result₁ =>
      cases second with
      | @target _ representedWorld₂ _ _ targetActor₂ _ targetObject₂ _
          representedMessage₂ _ _ target₂ representation₂ result₂ =>
          rcases target₁.unique_actor_and_object target₂ with
            ⟨actorEqual, objectEqual⟩
          subst targetActor₂
          subst targetObject₂
          rcases representation₁.deterministic transferDeterministic
              representation₂ with ⟨worldEqual, messageEqual⟩
          cases worldEqual
          cases messageEqual
          exact result₁.trans result₂.symm
      | pending _ => cases target₁
      | fulfilled _ _ _ => cases target₁
      | broken _ _ _ => cases target₁
  | @pending world requester owner promise resultPromise waiters message history
      lookup₁ =>
      cases second with
      | target target _ _ => cases target
      | pending lookup₂ =>
          have equal := Option.some.inj (lookup₁.symm.trans lookup₂)
          cases equal
          rfl
      | fulfilled lookup₂ _ _ =>
          rw [lookup₁] at lookup₂
          simp at lookup₂
      | broken lookup₂ _ _ =>
          rw [lookup₁] at lookup₂
          simp at lookup₂
  | @fulfilled world representedWorld₁ after₁ requester owner₁ promise
      resultPromise result₁ represented₁ message history lookup₁
      representation₁ route₁ ih =>
      cases second with
      | target target _ _ => cases target
      | pending lookup₂ =>
          rw [lookup₁] at lookup₂
          simp at lookup₂
      | @fulfilled _ representedWorld₂ _ _ owner₂ _ _ result₂
          represented₂ _ _ lookup₂ representation₂ route₂ =>
          have equal := Option.some.inj (lookup₁.symm.trans lookup₂)
          have parts := PromiseState.fulfilled.inj equal
          rcases parts with ⟨ownerEqual, resultEqual⟩
          subst owner₂
          subst result₂
          rcases representation₁.deterministic transferDeterministic
              representation₂ with ⟨worldEqual, representedEqual⟩
          cases worldEqual
          cases representedEqual
          exact ih route₂
      | broken lookup₂ _ _ =>
          rw [lookup₁] at lookup₂
          simp at lookup₂
  | @broken world representedWorld₁ after₁ requester owner₁ promise
      resultPromise exception₁ represented₁ message history lookup₁
      representation₁ settlement₁ =>
      cases second with
      | target target _ _ => cases target
      | pending lookup₂ =>
          rw [lookup₁] at lookup₂
          simp at lookup₂
      | fulfilled lookup₂ _ _ =>
          rw [lookup₁] at lookup₂
          simp at lookup₂
      | @broken _ representedWorld₂ _ _ owner₂ _ _ exception₂
          represented₂ _ _ lookup₂ representation₂ settlement₂ =>
          have equal := Option.some.inj (lookup₁.symm.trans lookup₂)
          have parts := PromiseState.broken.inj equal
          rcases parts with ⟨ownerEqual, exceptionEqual⟩
          subst owner₂
          subst exception₂
          rcases representation₁.deterministic transferDeterministic
              representation₂ with ⟨worldEqual, representedEqual⟩
          cases worldEqual
          cases representedEqual
          exact settlement₁.deterministic transferDeterministic settlement₂

theorem AsynchronousSend.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {world : ActorWorld} {actor : ActorId} {receiver : EventualRef}
    {message : EventualMessage} {history : List EventId}
    {after₁ after₂ : ActorWorld} {promise₁ promise₂ : PromiseId}
    (first : AsynchronousSend isValue valueTransfer world actor receiver message
      history after₁ promise₁)
    (second : AsynchronousSend isValue valueTransfer world actor receiver message
      history after₂ promise₂) : after₁ = after₂ ∧ promise₁ = promise₂ := by
  cases first
  cases second
  subst_vars
  constructor
  · apply RouteEventualMessage.deterministic transferDeterministic <;> assumption
  · rfl

theorem ActorEventualSendStep.deterministic
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (referenceDeterministic :
      ReferenceInterpretationDeterministic interpretReference)
    (messageDeterministic : MessageInterpretationDeterministic interpretMessage)
    (handleDeterministic :
      PromiseHandleInstallationDeterministic installPromiseHandle)
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before after₁)
    (second : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before after₂) :
    after₁ = after₂ := by
  cases first with
  | @send routed₁ config₁ reply₁ event₁ receiverObject₁ promiseObject₁
      message₁ receiver₁ eventualMessage₁ resultPromise₁ resultAllocation₁
      run₁ allocation₁ control₁ reference₁ messageInterpretation₁ async₁ handle₁ =>
      cases second with
      | @send routed₂ config₂ reply₂ event₂ receiverObject₂ promiseObject₂
          message₂ receiver₂ eventualMessage₂ resultPromise₂ resultAllocation₂
          run₂ allocation₂ control₂ reference₂ messageInterpretation₂ async₂ handle₂ =>
          have runEqual := Option.some.inj (run₁.symm.trans run₂)
          have runParts := ActorRunState.runningTurn.inj runEqual
          rcases runParts with ⟨configEqual, replyEqual, eventEqual⟩
          subst config₂
          subst reply₂
          subst event₂
          have controlEqual := ControlTerm.dispatch.inj (control₁.symm.trans control₂)
          have requestEqual := SendRequest.eventual.inj controlEqual.1
          have localMessageEqual := controlEqual.2
          subst receiverObject₂
          subst message₂
          have receiverEqual := referenceDeterministic before actor receiverObject₁
            receiver₁ receiver₂ reference₁ reference₂
          subst receiver₂
          have eventualMessageEqual := messageDeterministic before actor message₁
            eventualMessage₁ eventualMessage₂ messageInterpretation₁
            messageInterpretation₂
          subst eventualMessage₂
          rcases async₁.deterministic transferDeterministic async₂ with
            ⟨routedEqual, promiseEqual⟩
          subst routed₂
          subst resultPromise₂
          rcases handleDeterministic routed₁ actor config₁.allocation
              resultPromise₁ resultAllocation₁ promiseObject₁
              resultAllocation₂ promiseObject₂ handle₁ handle₂ with
            ⟨allocationEqual, objectEqual⟩
          subst resultAllocation₂
          subst promiseObject₂
          rfl

theorem SettlementPacketDequeueStep.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : SettlementPacketDequeueStep isValue valueTransfer actor before after₁)
    (second : SettlementPacketDequeueStep isValue valueTransfer actor before after₂) :
    after₁ = after₂ := by
  cases first with
  | @dequeue consumed₁ _ packet₁ remaining₁ promise₁ disposition₁ result₁
      idle₁ mailbox₁ payload₁ consumedEqual₁ settlement₁ =>
      cases second with
      | @dequeue consumed₂ _ packet₂ remaining₂ promise₂ disposition₂ result₂
          idle₂ mailbox₂ payload₂ consumedEqual₂ settlement₂ =>
          have mailboxEqual := mailbox₁.symm.trans mailbox₂
          have packetEqual := (List.cons.inj mailboxEqual).1
          have remainingEqual := (List.cons.inj mailboxEqual).2
          subst packet₂
          subst remaining₂
          have payloadEqual := payload₁.symm.trans payload₂
          have parts := ActorPacketPayload.settlement.inj payloadEqual
          rcases parts with ⟨promiseEqual, dispositionEqual, resultEqual⟩
          subst promise₂
          subst disposition₂
          subst result₂
          have consumedWorldEqual := consumedEqual₁.trans consumedEqual₂.symm
          cases consumedWorldEqual
          exact settlement₁.deterministic transferDeterministic settlement₂

theorem WakePacketDequeueStep.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : WakePacketDequeueStep isValue valueTransfer actor before after₁)
    (second : WakePacketDequeueStep isValue valueTransfer actor before after₂) :
    after₁ = after₂ := by
  cases first with
  | @fulfilled consumed₁ representedWorld₁ _ packet₁ remaining₁
      settledPromise₁ resultPromise₁ result₁ represented₁ message₁ waiterHistory₁
      idle₁ mailbox₁ payload₁ consumedEqual₁ representation₁ route₁ =>
      cases second with
      | @fulfilled consumed₂ representedWorld₂ _ packet₂ remaining₂
          settledPromise₂ resultPromise₂ result₂ represented₂ message₂ waiterHistory₂
          idle₂ mailbox₂ payload₂ consumedEqual₂ representation₂ route₂ =>
          have mailboxEqual := mailbox₁.symm.trans mailbox₂
          have packetEqual := (List.cons.inj mailboxEqual).1
          have remainingEqual := (List.cons.inj mailboxEqual).2
          subst packet₂
          subst remaining₂
          have payloadEqual := payload₁.symm.trans payload₂
          have parts := ActorPacketPayload.wake.inj payloadEqual
          rcases parts with
            ⟨settledPromiseEqual, resultPromiseEqual, dispositionEqual,
              resultEqual, messageEqual, historyEqual⟩
          subst settledPromise₂
          subst resultPromise₂
          subst result₂
          subst message₂
          subst waiterHistory₂
          have consumedWorldEqual := consumedEqual₁.trans consumedEqual₂.symm
          cases consumedWorldEqual
          rcases representation₁.deterministic transferDeterministic
              representation₂ with ⟨representedWorldEqual, representedEqual⟩
          subst representedWorld₂
          subst represented₂
          exact route₁.deterministic transferDeterministic route₂
      | @broken consumed₂ _ packet₂ remaining₂ settledPromise₂ resultPromise₂ result₂
          message₂ waiterHistory₂ idle₂ mailbox₂ payload₂
          consumedEqual₂ settlement₂ =>
          have mailboxEqual := mailbox₁.symm.trans mailbox₂
          have packetEqual := (List.cons.inj mailboxEqual).1
          subst packet₂
          have payloadEqual := payload₁.symm.trans payload₂
          cases payloadEqual
  | @broken consumed₁ _ packet₁ remaining₁ settledPromise₁ resultPromise₁ result₁
      message₁ waiterHistory₁ idle₁ mailbox₁ payload₁
      consumedEqual₁ settlement₁ =>
      cases second with
      | @fulfilled consumed₂ representedWorld₂ _ packet₂ remaining₂
          settledPromise₂ resultPromise₂ result₂ represented₂ message₂ waiterHistory₂
          idle₂ mailbox₂ payload₂ consumedEqual₂ representation₂ route₂ =>
          have mailboxEqual := mailbox₁.symm.trans mailbox₂
          have packetEqual := (List.cons.inj mailboxEqual).1
          subst packet₂
          have payloadEqual := payload₁.symm.trans payload₂
          cases payloadEqual
      | @broken consumed₂ _ packet₂ remaining₂ settledPromise₂ resultPromise₂ result₂
          message₂ waiterHistory₂ idle₂ mailbox₂ payload₂
          consumedEqual₂ settlement₂ =>
          have mailboxEqual := mailbox₁.symm.trans mailbox₂
          have packetEqual := (List.cons.inj mailboxEqual).1
          have remainingEqual := (List.cons.inj mailboxEqual).2
          subst packet₂
          subst remaining₂
          have payloadEqual := payload₁.symm.trans payload₂
          have parts := ActorPacketPayload.wake.inj payloadEqual
          rcases parts with
            ⟨settledPromiseEqual, resultPromiseEqual, dispositionEqual,
              resultEqual, messageEqual, historyEqual⟩
          subst settledPromise₂
          subst resultPromise₂
          subst result₂
          subst message₂
          subst waiterHistory₂
          have consumedWorldEqual := consumedEqual₁.trans consumedEqual₂.symm
          cases consumedWorldEqual
          exact settlement₁.deterministic transferDeterministic settlement₂

theorem ActorTurnCompletionStep.deterministic
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : ActorTurnCompletionStep isValue valueTransfer actor before after₁)
    (second : ActorTurnCompletionStep isValue valueTransfer actor before after₂) :
    after₁ = after₂ := by
  cases first with
  | @«local» settled₁ config₁ reply₁ event₁ disposition₁ value₁ waiters₁ run₁
      stack₁ control₁ pending₁ settlement₁ =>
      cases second with
      | @«local» settled₂ config₂ reply₂ event₂ disposition₂ value₂ waiters₂ run₂
          stack₂ control₂ pending₂ settlement₂ =>
          have runEqual := Option.some.inj (run₁.symm.trans run₂)
          have runParts := ActorRunState.runningTurn.inj runEqual
          rcases runParts with ⟨configEqual, replyEqual, eventEqual⟩
          subst config₂
          subst reply₂
          subst event₂
          have controlEqual := control₁.symm.trans control₂
          have outcomeEqual : disposition₁ = disposition₂ ∧ value₁ = value₂ := by
            cases disposition₁ <;> cases disposition₂ <;>
              simp [SequentialConfig.turnCompletionControl] at controlEqual ⊢ <;>
              assumption
          rcases outcomeEqual with ⟨dispositionEqual, valueEqual⟩
          subst disposition₂
          subst value₂
          have pendingEqual := Option.some.inj (pending₁.symm.trans pending₂)
          have pendingParts := PromiseState.pending.inj pendingEqual
          rcases pendingParts with ⟨ownerEqual, waitersEqual⟩
          subst waiters₂
          have settledEqual := settlement₁.deterministic transferDeterministic settlement₂
          subst settled₂
          rfl
      | @remote config₂ reply₂ event₂ disposition₂ value₂ owner₂ waiters₂ run₂
          stack₂ control₂ pending₂ remoteOwner₂ =>
          have runEqual := Option.some.inj (run₁.symm.trans run₂)
          have runParts := ActorRunState.runningTurn.inj runEqual
          rcases runParts with ⟨configEqual, replyEqual, eventEqual⟩
          subst config₂
          subst reply₂
          have pendingEqual := Option.some.inj (pending₁.symm.trans pending₂)
          have pendingParts := PromiseState.pending.inj pendingEqual
          exact False.elim (remoteOwner₂ pendingParts.1.symm)
  | @remote config₁ reply₁ event₁ disposition₁ value₁ owner₁ waiters₁ run₁
      stack₁ control₁ pending₁ remoteOwner₁ =>
      cases second with
      | @«local» settled₂ config₂ reply₂ event₂ disposition₂ value₂ waiters₂ run₂
          stack₂ control₂ pending₂ settlement₂ =>
          have runEqual := Option.some.inj (run₁.symm.trans run₂)
          have runParts := ActorRunState.runningTurn.inj runEqual
          rcases runParts with ⟨configEqual, replyEqual, eventEqual⟩
          subst config₂
          subst reply₂
          have pendingEqual := Option.some.inj (pending₁.symm.trans pending₂)
          have pendingParts := PromiseState.pending.inj pendingEqual
          exact False.elim (remoteOwner₁ pendingParts.1)
      | @remote config₂ reply₂ event₂ disposition₂ value₂ owner₂ waiters₂ run₂
          stack₂ control₂ pending₂ remoteOwner₂ =>
          have runEqual := Option.some.inj (run₁.symm.trans run₂)
          have runParts := ActorRunState.runningTurn.inj runEqual
          rcases runParts with ⟨configEqual, replyEqual, eventEqual⟩
          subst config₂
          subst reply₂
          subst event₂
          have controlEqual := control₁.symm.trans control₂
          have outcomeEqual : disposition₁ = disposition₂ ∧ value₁ = value₂ := by
            cases disposition₁ <;> cases disposition₂ <;>
              simp [SequentialConfig.turnCompletionControl] at controlEqual ⊢ <;>
              assumption
          rcases outcomeEqual with ⟨dispositionEqual, valueEqual⟩
          subst disposition₂
          subst value₂
          have pendingEqual := Option.some.inj (pending₁.symm.trans pending₂)
          have pendingParts := PromiseState.pending.inj pendingEqual
          rcases pendingParts with ⟨ownerEqual, waitersEqual⟩
          subst owner₂
          rfl

theorem ActorTurnStartStep.sequential_disjoint
    (start : ActorTurnStartStep materialize actor before startAfter)
    (sequential : ActorSequentialStep p reifier actor before sequentialAfter) :
    False := by
  cases start
  cases sequential
  simp_all

theorem ActorTurnStartStep.completion_disjoint
    (start : ActorTurnStartStep materialize actor before startAfter)
    (completion : ActorTurnCompletionStep isValue valueTransfer actor before
      completionAfter) : False := by
  cases start
  cases completion <;> simp_all

theorem ActorTurnStartStep.eventual_disjoint
    (start : ActorTurnStartStep materialize actor before startAfter)
    (eventual : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before eventualAfter) :
    False := by
  cases start
  cases eventual
  simp_all

theorem ActorTurnStartStep.settlement_disjoint
    (start : ActorTurnStartStep materialize actor before startAfter)
    (settlement : SettlementPacketDequeueStep isValue valueTransfer actor before
      settlementAfter) : False := by
  cases start
  cases settlement
  simp_all

theorem ActorTurnStartStep.wake_disjoint
    (start : ActorTurnStartStep materialize actor before startAfter)
    (wake : WakePacketDequeueStep isValue valueTransfer actor before wakeAfter) :
    False := by
  cases start
  cases wake <;> simp_all

theorem ActorSequentialStep.completion_disjoint
    (sequential : ActorSequentialStep p reifier actor before sequentialAfter)
    (completion : ActorTurnCompletionStep isValue valueTransfer actor before
      completionAfter) : False := by
  cases sequential
  cases completion <;> simp_all [SequentialConfig.TurnTerminal]

theorem ActorSequentialStep.eventual_disjoint
    (sequential : ActorSequentialStep p reifier actor before sequentialAfter)
    (eventual : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before eventualAfter) :
    False := by
  cases sequential
  cases eventual
  simp_all [SequentialConfig.EventualDispatch]

theorem ActorSequentialStep.settlement_disjoint
    (sequential : ActorSequentialStep p reifier actor before sequentialAfter)
    (settlement : SettlementPacketDequeueStep isValue valueTransfer actor before
      settlementAfter) : False := by
  cases sequential
  cases settlement
  simp_all

theorem ActorSequentialStep.wake_disjoint
    (sequential : ActorSequentialStep p reifier actor before sequentialAfter)
    (wake : WakePacketDequeueStep isValue valueTransfer actor before wakeAfter) :
    False := by
  cases sequential
  cases wake <;> simp_all

theorem ActorTurnCompletionStep.settlement_disjoint
    (completion : ActorTurnCompletionStep isValue valueTransfer actor before
      completionAfter)
    (settlement : SettlementPacketDequeueStep isValue valueTransfer actor before
      settlementAfter) : False := by
  cases completion <;> cases settlement <;> simp_all

theorem ActorEventualSendStep.completion_disjoint
    (eventual : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before eventualAfter)
    (completion : ActorTurnCompletionStep isValue valueTransfer actor before
      completionAfter) : False := by
  cases eventual
  cases completion <;>
    simp_all [SequentialConfig.turnCompletionControl] <;>
    split at * <;> simp_all

theorem ActorEventualSendStep.settlement_disjoint
    (eventual : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before eventualAfter)
    (settlement : SettlementPacketDequeueStep isValue valueTransfer actor before
      settlementAfter) : False := by
  cases eventual
  cases settlement
  simp_all

theorem ActorEventualSendStep.wake_disjoint
    (eventual : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before eventualAfter)
    (wake : WakePacketDequeueStep isValue valueTransfer actor before wakeAfter) :
    False := by
  cases eventual
  cases wake <;> simp_all

theorem ActorTurnCompletionStep.wake_disjoint
    (completion : ActorTurnCompletionStep isValue valueTransfer actor before
      completionAfter)
    (wake : WakePacketDequeueStep isValue valueTransfer actor before wakeAfter) :
    False := by
  cases completion <;> cases wake <;> simp_all

theorem SettlementPacketDequeueStep.wake_disjoint
    (settlement : SettlementPacketDequeueStep isValue valueTransfer actor before
      settlementAfter)
    (wake : WakePacketDequeueStep isValue valueTransfer actor before wakeAfter) :
    False := by
  cases settlement
  cases wake <;> simp_all

/-- Once an actor and its current world are selected, its computation step is
    deterministic.  The remaining nondeterminism of the actor system is the
    external choice of actor or deliverable network packet. -/
theorem SelectedActorStep.deterministic
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (materializationDeterministic : MaterializationDeterministic materialize)
    (referenceDeterministic :
      ReferenceInterpretationDeterministic interpretReference)
    (messageDeterministic : MessageInterpretationDeterministic interpretMessage)
    (handleDeterministic :
      PromiseHandleInstallationDeterministic installPromiseHandle)
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : SelectedActorStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer actor before
      after₁)
    (second : SelectedActorStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer actor before
      after₂) : after₁ = after₂ := by
  cases first with
  | start start₁ =>
      cases second with
      | start start₂ =>
          exact start₁.deterministic materializationDeterministic start₂
      | sequential sequential₂ => exact False.elim (start₁.sequential_disjoint sequential₂)
      | eventual eventual₂ => exact False.elim (start₁.eventual_disjoint eventual₂)
      | complete completion₂ => exact False.elim (start₁.completion_disjoint completion₂)
      | settlement settlement₂ => exact False.elim (start₁.settlement_disjoint settlement₂)
      | wake wake₂ => exact False.elim (start₁.wake_disjoint wake₂)
  | sequential sequential₁ =>
      cases second with
      | start start₂ => exact False.elim (start₂.sequential_disjoint sequential₁)
      | sequential sequential₂ => exact sequential₁.deterministic sequential₂
      | eventual eventual₂ => exact False.elim (sequential₁.eventual_disjoint eventual₂)
      | complete completion₂ => exact False.elim (sequential₁.completion_disjoint completion₂)
      | settlement settlement₂ => exact False.elim (sequential₁.settlement_disjoint settlement₂)
      | wake wake₂ => exact False.elim (sequential₁.wake_disjoint wake₂)
  | eventual eventual₁ =>
      cases second with
      | start start₂ => exact False.elim (start₂.eventual_disjoint eventual₁)
      | sequential sequential₂ => exact False.elim (sequential₂.eventual_disjoint eventual₁)
      | eventual eventual₂ =>
          exact eventual₁.deterministic referenceDeterministic
            messageDeterministic handleDeterministic transferDeterministic
            eventual₂
      | complete completion₂ => exact False.elim (eventual₁.completion_disjoint completion₂)
      | settlement settlement₂ => exact False.elim (eventual₁.settlement_disjoint settlement₂)
      | wake wake₂ => exact False.elim (eventual₁.wake_disjoint wake₂)
  | complete completion₁ =>
      cases second with
      | start start₂ => exact False.elim (start₂.completion_disjoint completion₁)
      | sequential sequential₂ => exact False.elim (sequential₂.completion_disjoint completion₁)
      | eventual eventual₂ => exact False.elim (eventual₂.completion_disjoint completion₁)
      | complete completion₂ =>
          exact completion₁.deterministic transferDeterministic completion₂
      | settlement settlement₂ => exact False.elim (completion₁.settlement_disjoint settlement₂)
      | wake wake₂ => exact False.elim (completion₁.wake_disjoint wake₂)
  | settlement settlement₁ =>
      cases second with
      | start start₂ => exact False.elim (start₂.settlement_disjoint settlement₁)
      | sequential sequential₂ => exact False.elim (sequential₂.settlement_disjoint settlement₁)
      | eventual eventual₂ => exact False.elim (eventual₂.settlement_disjoint settlement₁)
      | complete completion₂ => exact False.elim (completion₂.settlement_disjoint settlement₁)
      | settlement settlement₂ =>
          exact settlement₁.deterministic transferDeterministic settlement₂
      | wake wake₂ => exact False.elim (settlement₁.wake_disjoint wake₂)
  | wake wake₁ =>
      cases second with
      | start start₂ => exact False.elim (start₂.wake_disjoint wake₁)
      | sequential sequential₂ => exact False.elim (sequential₂.wake_disjoint wake₁)
      | eventual eventual₂ => exact False.elim (eventual₂.wake_disjoint wake₁)
      | complete completion₂ => exact False.elim (completion₂.wake_disjoint wake₁)
      | settlement settlement₂ => exact False.elim (settlement₂.wake_disjoint wake₁)
      | wake wake₂ => exact wake₁.deterministic transferDeterministic wake₂

end Newspeak
