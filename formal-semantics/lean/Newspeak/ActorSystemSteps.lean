import Newspeak.ActorEventualSends

namespace Newspeak
namespace ActorWorld

/-- Remove a known FIFO head and merge both its causal history and identity.
    `additionalHistory` is used by wake packets to merge the history retained
    when the dependent send was registered. -/
def consumeHeadPacket (world : ActorWorld) (actor : ActorId)
    (packet : ActorPacket) (remaining : List ActorPacket)
    (additionalHistory : List EventId) :
    ActorWorld :=
  let merged := mergeEventSets (world.causalHistory actor)
    packet.causalHistory
  let merged := mergeEventSets merged additionalHistory
  let merged := addEventToSet merged packet.identity
  { world with
    mailboxes := world.mailboxes.install actor remaining
    histories := world.histories.install actor merged }

@[simp] theorem consumeHeadPacket_mailbox (world : ActorWorld)
    (actor : ActorId) (packet : ActorPacket) (remaining : List ActorPacket)
    (additionalHistory : List EventId) :
    (world.consumeHeadPacket actor packet remaining additionalHistory).mailbox
      actor = remaining := by
  simp [consumeHeadPacket, mailbox]

@[simp] theorem consumeHeadPacket_runStates (world : ActorWorld)
    (actor : ActorId) (packet : ActorPacket) (remaining : List ActorPacket)
    (additionalHistory : List EventId) :
    (world.consumeHeadPacket actor packet remaining additionalHistory).runStates =
      world.runStates := by
  rfl

def finishRunningTurn (world : ActorWorld) (actor : ActorId)
    (allocation : AllocationState) : ActorWorld :=
  { world with
    actorAllocations := world.actorAllocations.install actor allocation
    runStates := world.runStates.install actor .idle }

@[simp] theorem finishRunningTurn_state (world : ActorWorld)
    (actor : ActorId) (allocation : AllocationState) :
    (world.finishRunningTurn actor allocation).runStates actor = some .idle := by
  simp [finishRunningTurn]

@[simp] theorem finishRunningTurn_allocation (world : ActorWorld)
    (actor : ActorId) (allocation : AllocationState) :
    (world.finishRunningTurn actor allocation).actorAllocations actor =
      some allocation := by
  simp [finishRunningTurn]

end ActorWorld

/-- Normal or exceptional termination of a selected actor turn.  A locally
    owned reply promise settles immediately; a remotely owned promise receives
    a causal settlement packet. -/
inductive ActorTurnCompletionStep
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | local {world settled : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId}
      {disposition : SettlementDisposition} {value : ObjRef}
      {waiters : List PromiseWaiter} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      config.stack = .empty →
      config.control = SequentialConfig.turnCompletionControl disposition value →
      world.promises replyPromise = some (.pending actor waiters) →
      PromiseSettlement isValue valueTransfer world replyPromise disposition
        actor (.near value) (world.causalHistory actor) settled →
      ActorTurnCompletionStep isValue valueTransfer actor world
        (settled.finishRunningTurn actor config.allocation)
  | remote {world : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId}
      {disposition : SettlementDisposition} {value : ObjRef}
      {owner : ActorId} {waiters : List PromiseWaiter} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      config.stack = .empty →
      config.control = SequentialConfig.turnCompletionControl disposition value →
      world.promises replyPromise = some (.pending owner waiters) →
      owner ≠ actor →
      ActorTurnCompletionStep isValue valueTransfer actor world
        ((world.emitPacket actor owner
          (.settlement replyPromise disposition (.near value))).finishRunningTurn
            actor config.allocation)

/-- An idle promise owner consumes a settlement packet and applies the single
    settlement operation after merging the packet's causal history. -/
inductive SettlementPacketDequeueStep
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | dequeue {world consumed after : ActorWorld} {packet : ActorPacket}
      {remaining : List ActorPacket} {promise : PromiseId}
      {disposition : SettlementDisposition} {result : EventualRef} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      packet.payload = .settlement promise disposition result →
      consumed = world.consumeHeadPacket actor packet remaining [] →
      PromiseSettlement isValue valueTransfer consumed promise disposition
        packet.source result (consumed.causalHistory actor) after →
      SettlementPacketDequeueStep isValue valueTransfer actor world after

/-- Wake packets are system work between user turns.  Fulfillment resumes the
    stored routing operation; breakage settles the dependent promise directly. -/
inductive WakePacketDequeueStep
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | fulfilled {world consumed representedWorld after : ActorWorld}
      {packet : ActorPacket} {remaining : List ActorPacket}
      {settledPromise resultPromise : PromiseId}
      {result represented : EventualRef}
      {message : EventualMessage} {waiterHistory : List EventId} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      packet.payload = .wake settledPromise resultPromise .fulfilled result message
        waiterHistory →
      consumed = world.consumeHeadPacket actor packet remaining waiterHistory →
      RemoteRepresentation isValue valueTransfer consumed packet.source actor
        result representedWorld represented →
      RouteEventualMessage isValue valueTransfer representedWorld actor
        represented message resultPromise (representedWorld.causalHistory actor)
        after →
      WakePacketDequeueStep isValue valueTransfer actor world after
  | broken {world consumed after : ActorWorld} {packet : ActorPacket}
      {remaining : List ActorPacket}
      {settledPromise resultPromise : PromiseId}
      {result : EventualRef} {message : EventualMessage}
      {waiterHistory : List EventId} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      packet.payload = .wake settledPromise resultPromise .broken result message waiterHistory →
      consumed = world.consumeHeadPacket actor packet remaining waiterHistory →
      PromiseSettlement isValue valueTransfer consumed resultPromise .broken
        packet.source result (consumed.causalHistory actor) after →
      WakePacketDequeueStep isValue valueTransfer actor world after

/-- All computation selected for one actor, excluding globally selected
    network arrival.  Constructor shapes make idle system work disjoint from
    running-turn work and give paused actors no executable constructor. -/
inductive SelectedActorStep (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | start {before after : ActorWorld} :
      ActorTurnStartStep materialize actor before after →
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor
        before after
  | sequential {before after : ActorWorld} :
      ActorSequentialStep p reifier actor before after →
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor
        before after
  | eventual {before after : ActorWorld} :
      ActorEventualSendStep interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer actor before after →
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor
        before after
  | complete {before after : ActorWorld} :
      ActorTurnCompletionStep isValue valueTransfer actor before after →
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor
        before after
  | settlement {before after : ActorWorld} :
      SettlementPacketDequeueStep isValue valueTransfer actor before after →
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor
        before after
  | wake {before after : ActorWorld} :
      WakePacketDequeueStep isValue valueTransfer actor before after →
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor
        before after

theorem SelectedActorStep.paused_actor_cannot_step
    {p : Program} {reifier : ErrorReifier p}
    {materialize interpretReference interpretMessage installPromiseHandle
      isValue valueTransfer actor before after config reply event token reason}
    (paused : before.runStates actor =
      some (.pausedTurn config reply event token reason))
    (step : SelectedActorStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer actor before
      after) : False := by
  cases step with
  | start start => cases start; simp_all
  | sequential sequential => cases sequential; simp_all
  | eventual eventual => cases eventual; simp_all
  | complete complete => cases complete <;> simp_all
  | settlement settlement => cases settlement; simp_all
  | wake wake => cases wake <;> simp_all

end Newspeak
