import Newspeak.ActorTurns

namespace Newspeak

/-- Platform interpretation of a locally represented eventual capability.
    The ordinary object is the result of evaluating the receiver expression;
    the result says whether it denotes a near object, promise, or far handle. -/
abbrev LocalEventualReferenceInterpretation :=
  ActorWorld → ActorId → ObjRef → EventualRef → Prop

/-- Platform interpretation of the evaluated arguments of an eventual send. -/
abbrev LocalEventualMessageInterpretation :=
  ActorWorld → ActorId → Message → EventualMessage → Prop

/-- Installation of the newly allocated promise's ordinary Newspeak handle
    in the sending actor's private allocation state. -/
abbrev PromiseHandleInstallation :=
  ActorWorld → ActorId → AllocationState → PromiseId →
    AllocationState → ObjRef → Prop

def ReferenceInterpretationDeterministic
    (interpret : LocalEventualReferenceInterpretation) : Prop :=
  ∀ world actor object first second,
    interpret world actor object first →
    interpret world actor object second → first = second

def MessageInterpretationDeterministic
    (interpret : LocalEventualMessageInterpretation) : Prop :=
  ∀ world actor message first second,
    interpret world actor message first →
    interpret world actor message second → first = second

def PromiseHandleInstallationDeterministic
    (install : PromiseHandleInstallation) : Prop :=
  ∀ world actor before promise after₁ object₁ after₂ object₂,
    install world actor before promise after₁ object₁ →
    install world actor before promise after₂ object₂ →
      after₁ = after₂ ∧ object₁ = object₂

namespace SequentialConfig

def returnEventualPromise (config : SequentialConfig)
    (allocation : AllocationState) (handle : ObjRef) : SequentialConfig :=
  { config with allocation := allocation, control := .object handle }

end SequentialConfig

/-- Exact actor interception of an evaluated `eventualRequest`.  Ordinary
    sequential dispatch has no rule for this request constructor.  The actor
    boundary interprets local handles, allocates and routes a fresh result
    promise, installs its local Newspeak handle, and replaces the dispatch by
    that handle as the value of the expression. -/
inductive ActorEventualSendStep
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | send {world routed : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId}
      {receiverObject promiseObject : ObjRef} {message : Message}
      {receiver : EventualRef} {eventualMessage : EventualMessage}
      {resultPromise : PromiseId} {resultAllocation : AllocationState} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      world.actorAllocations actor = some config.allocation →
      config.control = .dispatch (.eventual receiverObject) message →
      interpretReference world actor receiverObject receiver →
      interpretMessage world actor message eventualMessage →
      AsynchronousSend isValue valueTransfer world actor receiver
        eventualMessage (world.causalHistory actor) routed resultPromise →
      installPromiseHandle routed actor config.allocation resultPromise
        resultAllocation promiseObject →
      ActorEventualSendStep interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer actor world
        (routed.advanceRunningTurn actor
          (config.returnEventualPromise resultAllocation promiseObject)
          replyPromise triggeringEvent)

end Newspeak
