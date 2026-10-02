import Newspeak.ActorRouting

namespace Newspeak

/-- Platform boundary turning actor-level promise/far handles into the local
    Newspeak objects that implement their ordinary synchronous protocols. -/
abbrev LocalMessageMaterialization :=
  ActorWorld → ActorId → EventualMessage → Message → Prop

def MaterializationDeterministic
    (materialize : LocalMessageMaterialization) : Prop :=
  ∀ world actor eventual first second,
    materialize world actor eventual first →
    materialize world actor eventual second → first = second

namespace Program

def applicationTurnConfiguration (p : Program) (state : AllocationState)
    (receiver : ObjRef) (message : Message) : SequentialConfig :=
  { allocation := (p.allocateTopLevelActivation state).1
    stack := .push .empty
      ⟨(p.allocateTopLevelActivation state).2, .empty⟩
    control := .dispatch (.ordinary receiver) message }

end Program

namespace SequentialConfig

/-- Actor-turn terminal control indexed by promise disposition. -/
def turnCompletionControl : SettlementDisposition → ObjRef → ControlTerm
  | .fulfilled, value => .halt value
  | .broken, exception => .abort exception

/-- The unique control shape in which an actor turn has finished and must be
    handed back to the actor scheduler rather than stepped sequentially. -/
def TurnTerminal (config : SequentialConfig) : Prop :=
  ∃ disposition value,
    config.stack = .empty ∧
      config.control = turnCompletionControl disposition value

def EventualDispatch (config : SequentialConfig) : Prop :=
  ∃ receiver message,
    config.control = .dispatch (.eventual receiver) message

end SequentialConfig

namespace ActorWorld

def startApplicationTurn (world : ActorWorld) (actor : ActorId)
    (state : AllocationState) (packet : ActorPacket) (remaining : List ActorPacket)
    (receiver : ObjRef) (message : Message) (replyPromise : PromiseId) :
    ActorWorld :=
  let config := world.program.applicationTurnConfiguration state receiver message
  let history := mergeEventSets (world.causalHistory actor)
    packet.causalHistory
  let history := addEventToSet history packet.identity
  { world with
    actorAllocations := world.actorAllocations.install actor config.allocation
    runStates := world.runStates.install actor
      (.runningTurn config replyPromise packet.identity)
    mailboxes := world.mailboxes.install actor remaining
    histories := world.histories.install actor history }

@[simp] theorem startApplicationTurn_runState (world : ActorWorld)
    (actor : ActorId) (state : AllocationState) (packet : ActorPacket)
    (remaining : List ActorPacket) (receiver : ObjRef) (message : Message)
    (replyPromise : PromiseId) :
    (world.startApplicationTurn actor state packet remaining receiver message
      replyPromise).runStates actor =
      some (.runningTurn
        (world.program.applicationTurnConfiguration state receiver message)
        replyPromise packet.identity) := by
  simp [startApplicationTurn]

@[simp] theorem startApplicationTurn_allocation (world : ActorWorld)
    (actor : ActorId) (state : AllocationState) (packet : ActorPacket)
    (remaining : List ActorPacket) (receiver : ObjRef) (message : Message)
    (replyPromise : PromiseId) :
    (world.startApplicationTurn actor state packet remaining receiver message
      replyPromise).actorAllocations actor =
      some (Program.applicationTurnConfiguration world.program state receiver message).allocation := by
  simp [startApplicationTurn]

@[simp] theorem startApplicationTurn_mailbox (world : ActorWorld)
    (actor : ActorId) (state : AllocationState) (packet : ActorPacket)
    (remaining : List ActorPacket) (receiver : ObjRef) (message : Message)
    (replyPromise : PromiseId) :
    (world.startApplicationTurn actor state packet remaining receiver message
      replyPromise).mailbox actor = remaining := by
  simp [startApplicationTurn, ActorWorld.mailbox]

def advanceRunningTurn (world : ActorWorld) (actor : ActorId)
    (after : SequentialConfig) (replyPromise : PromiseId)
    (triggeringEvent : EventId) : ActorWorld :=
  { world with
    actorAllocations := world.actorAllocations.install actor after.allocation
    runStates := world.runStates.install actor
      (.runningTurn after replyPromise triggeringEvent) }

@[simp] theorem advanceRunningTurn_runState (world : ActorWorld)
    (actor : ActorId) (after : SequentialConfig) (replyPromise : PromiseId)
    (triggeringEvent : EventId) :
    (world.advanceRunningTurn actor after replyPromise triggeringEvent).runStates
      actor = some (ActorRunState.runningTurn after replyPromise triggeringEvent) := by
  simp [advanceRunningTurn]

@[simp] theorem advanceRunningTurn_allocation (world : ActorWorld)
    (actor : ActorId) (after : SequentialConfig) (replyPromise : PromiseId)
    (triggeringEvent : EventId) :
    (world.advanceRunningTurn actor after replyPromise triggeringEvent).actorAllocations
      actor = some after.allocation := by
  simp [advanceRunningTurn]

end ActorWorld

/-- FIFO application dequeue.  Only an idle actor whose head packet is an
    application may start a user turn. -/
inductive ActorTurnStartStep (materialize : LocalMessageMaterialization)
    (actor : ActorId) : ActorWorld → ActorWorld → Prop where
  | application {world : ActorWorld} {state : AllocationState}
      {packet : ActorPacket} {remaining : List ActorPacket}
      {receiver : ObjRef} {eventualMessage : EventualMessage}
      {message : Message} {replyPromise : PromiseId} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      world.actorAllocations actor = some state →
      packet.payload = .application receiver eventualMessage replyPromise →
      materialize world actor eventualMessage message →
      ActorTurnStartStep materialize actor world
        (world.startApplicationTurn actor state packet remaining receiver message
          replyPromise)

theorem ActorTurnStartStep.deterministic
    {materialize : LocalMessageMaterialization}
    (functional : MaterializationDeterministic materialize)
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : ActorTurnStartStep materialize actor before after₁)
    (second : ActorTurnStartStep materialize actor before after₂) :
    after₁ = after₂ := by
  cases first with
  | @application state₁ packet₁ remaining₁ receiver₁ eventual₁
      message₁ reply₁ idle₁ mailbox₁ allocation₁ payload₁ materialized₁ =>
    cases second with
    | @application state₂ packet₂ remaining₂ receiver₂ eventual₂
        message₂ reply₂ idle₂ mailbox₂ allocation₂ payload₂ materialized₂ =>
      have mailboxEqual := mailbox₁.symm.trans mailbox₂
      have packetEqual : packet₁ = packet₂ := (List.cons.inj mailboxEqual).1
      have remainingEqual : remaining₁ = remaining₂ :=
        (List.cons.inj mailboxEqual).2
      subst packet₂
      subst remaining₂
      have allocationEqual := Option.some.inj (allocation₁.symm.trans allocation₂)
      subst state₂
      have payloadEqual := payload₁.symm.trans payload₂
      have applicationEqual := ActorPacketPayload.application.inj payloadEqual
      rcases applicationEqual with ⟨receiverEqual, eventualEqual, replyEqual⟩
      subst receiver₂
      subst eventual₂
      subst reply₂
      have messageEqual := functional before actor eventual₁ message₁ message₂
        materialized₁ materialized₂
      subst message₂
      rfl

/-- One ordinary sequential step inside the uniquely selected running actor.
    Paused and idle actors have no constructor. -/
inductive ActorSequentialStep (p : Program) (reifier : ErrorReifier p)
    (actor : ActorId) : ActorWorld → ActorWorld → Prop where
  | advance {world : ActorWorld} {before after : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId} :
      world.runStates actor =
        some (.runningTurn before replyPromise triggeringEvent) →
      world.actorAllocations actor = some before.allocation →
      world.program = p →
      p.WellFormed before.allocation.heap →
      ¬ before.TurnTerminal →
      ¬ before.EventualDispatch →
      p.SequentialStepWithTopLevel reifier before after →
      ActorSequentialStep p reifier actor world
        (world.advanceRunningTurn actor after replyPromise triggeringEvent)

theorem ActorSequentialStep.deterministic
    {p : Program} {reifier : ErrorReifier p}
    {actor : ActorId} {before after₁ after₂ : ActorWorld}
    (first : ActorSequentialStep p reifier actor before after₁)
    (second : ActorSequentialStep p reifier actor before after₂) :
    after₁ = after₂ := by
  cases first with
  | @advance config₁ result₁ reply₁ event₁ run₁ allocation₁ program₁
      wf₁ nonterminal₁ nonEventual₁ step₁ =>
    cases second with
    | @advance config₂ result₂ reply₂ event₂ run₂ allocation₂ program₂
        wf₂ nonterminal₂ nonEventual₂ step₂ =>
      have runEqual := Option.some.inj (run₁.symm.trans run₂)
      have parts := ActorRunState.runningTurn.inj runEqual
      rcases parts with ⟨configEqual, replyEqual, eventEqual⟩
      subst config₂
      subst reply₂
      subst event₂
      have resultEqual := Program.sequentialStepWithTopLevel_deterministic
        wf₁ step₁ step₂
      subst result₂
      rfl

end Newspeak
