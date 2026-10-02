import Newspeak.ActorSemantics

namespace Newspeak
namespace ActorWorld

/-- Allocate an unresolved promise owned by `owner`, using the monotone global
    promise frontier. -/
def allocatePendingPromise (world : ActorWorld) (owner : ActorId) :
    ActorWorld × PromiseId :=
  let identity : PromiseId := ⟨world.nextPromise⟩
  ({ world with
      promises := world.promises.install identity (.pending owner [])
      nextPromise := world.nextPromise + 1 }, identity)

@[simp] theorem allocatePendingPromise_identity (world : ActorWorld)
    (owner : ActorId) :
    (world.allocatePendingPromise owner).2 = ⟨world.nextPromise⟩ := by
  rfl

@[simp] theorem allocatePendingPromise_lookup (world : ActorWorld)
    (owner : ActorId) :
    (world.allocatePendingPromise owner).1.promises
      (world.allocatePendingPromise owner).2 = some (.pending owner []) := by
  simp [allocatePendingPromise]

theorem allocatePendingPromise_preserves_frontierFresh (world : ActorWorld)
    (fresh : world.PromiseFrontierFresh) (owner : ActorId) :
    (world.allocatePendingPromise owner).1.PromiseFrontierFresh := by
  unfold PromiseFrontierFresh
  intro promise member
  have installedMember : promise ∈
      (world.promises.install ⟨world.nextPromise⟩ (.pending owner [])).domain := by
    simpa [allocatePendingPromise] using member
  rcases (FiniteStore.mem_install_domain_iff _ _ _ _).mp installedMember with
    atNew | old
  · subst promise
    simp [allocatePendingPromise]
  · simpa [allocatePendingPromise] using
      Nat.lt_succ_of_lt (fresh promise old)

/-- Accept an already eligible cross-actor packet.  `List.erase` consumes one
    occurrence; event-identity uniqueness will later imply there can be only
    one. -/
def acceptNetworkPacket (world : ActorWorld) (packet : ActorPacket) :
    ActorWorld :=
  { world with
    network := world.network.erase packet
    mailboxes := world.mailboxes.install packet.destination
      (world.mailbox packet.destination ++ [packet])
    deliveredEvents := world.deliveredEvents.install packet.destination
      (world.deliveredTo packet.destination ++ [packet.identity]) }

@[simp] theorem acceptNetworkPacket_mailbox (world : ActorWorld)
    (packet : ActorPacket) :
    (world.acceptNetworkPacket packet).mailbox packet.destination =
      world.mailbox packet.destination ++ [packet] := by
  simp [acceptNetworkPacket, mailbox]

@[simp] theorem acceptNetworkPacket_delivered (world : ActorWorld)
    (packet : ActorPacket) :
    (world.acceptNetworkPacket packet).deliveredTo packet.destination =
      world.deliveredTo packet.destination ++ [packet.identity] := by
  simp [acceptNetworkPacket, deliveredTo]

@[simp] theorem acceptNetworkPacket_preserves_program (world : ActorWorld)
    (packet : ActorPacket) :
    (world.acceptNetworkPacket packet).program = world.program := by
  rfl

@[simp] theorem acceptNetworkPacket_preserves_actorAllocations (world : ActorWorld)
    (packet : ActorPacket) :
    (world.acceptNetworkPacket packet).actorAllocations =
      world.actorAllocations := by
  rfl

@[simp] theorem acceptNetworkPacket_preserves_runStates (world : ActorWorld)
    (packet : ActorPacket) :
    (world.acceptNetworkPacket packet).runStates = world.runStates := by
  rfl

@[simp] theorem acceptNetworkPacket_preserves_promises (world : ActorWorld)
    (packet : ActorPacket) :
    (world.acceptNetworkPacket packet).promises = world.promises := by
  rfl

/-- Emit wake packets in registration order. -/
def wakeAllWaiters (world : ActorWorld) (owner : ActorId)
    (settledPromise : PromiseId)
    (disposition : SettlementDisposition) (result : EventualRef) :
    List PromiseWaiter → ActorWorld
  | [] => world
  | waiter :: remaining =>
      let emitted := world.emitPacket owner waiter.actor
        (.wake settledPromise waiter.resultPromise disposition result waiter.message
          waiter.causalHistory)
      wakeAllWaiters emitted owner settledPromise disposition result remaining

@[simp] theorem wakeAllWaiters_nil (world : ActorWorld) (owner : ActorId)
    (settledPromise : PromiseId)
    (disposition : SettlementDisposition) (result : EventualRef) :
    world.wakeAllWaiters owner settledPromise disposition result [] = world := by
  rfl

theorem wakeAllWaiters_preserves_promises (world : ActorWorld)
    (owner : ActorId) (settledPromise : PromiseId)
    (disposition : SettlementDisposition)
    (result : EventualRef) (waiters : List PromiseWaiter) :
    (world.wakeAllWaiters owner settledPromise disposition result waiters).promises =
      world.promises := by
  induction waiters generalizing world with
  | nil => rfl
  | cons waiter remaining ih =>
      simp only [wakeAllWaiters]
      rw [ih]
      by_cases same : owner = waiter.actor <;>
        simp [emitPacket, same]

theorem wakeAllWaiters_preserves_eventFrontierFresh (world : ActorWorld)
    (fresh : world.EventFrontierFresh) (owner : ActorId)
    (settledPromise : PromiseId)
    (disposition : SettlementDisposition) (result : EventualRef)
    (waiters : List PromiseWaiter) :
    ActorWorld.EventFrontierFresh
      (world.wakeAllWaiters owner settledPromise disposition result waiters) := by
  induction waiters generalizing world with
  | nil => exact fresh
  | cons waiter remaining ih =>
      apply ih
      exact world.emitPacket_preserves_eventFrontierFresh fresh owner
        waiter.actor (.wake settledPromise waiter.resultPromise disposition result
          waiter.message waiter.causalHistory)

end ActorWorld

def commitPromiseSettlement (world : ActorWorld) (promise : PromiseId)
    (owner : ActorId) (disposition : SettlementDisposition)
    (represented : EventualRef) (waiters : List PromiseWaiter) : ActorWorld :=
  let terminal := match disposition with
    | .fulfilled => PromiseState.fulfilled owner represented
    | .broken => PromiseState.broken owner represented
  let committed := { world with
    promises := world.promises.install promise terminal }
  committed.wakeAllWaiters owner promise disposition represented waiters

/-- The sole network-arrival rule.  Eligibility is checked before appending
    the packet and its permanent delivered/retired ledger position. -/
inductive ActorNetworkDeliveryStep : ActorWorld → ActorWorld → Prop where
  | deliver {world : ActorWorld} {packet : ActorPacket} :
      packet ∈ world.network →
      world.PacketEligible packet →
      ActorNetworkDeliveryStep world (world.acceptNetworkPacket packet)

theorem ActorNetworkDeliveryStep.preserves_program_and_heaps
    {before after : ActorWorld}
    (step : ActorNetworkDeliveryStep before after) :
    after.program = before.program ∧
      after.actorAllocations = before.actorAllocations ∧
      after.runStates = before.runStates := by
  cases step
  exact ⟨rfl, rfl, rfl⟩

theorem ActorNetworkDeliveryStep.records_arrival
    {before after : ActorWorld} {packet : ActorPacket}
    (step : ActorNetworkDeliveryStep before after)
    (sameResult : after = before.acceptNetworkPacket packet) :
    packet.identity ∈ after.deliveredTo packet.destination := by
  subst after
  simp

/-- Promise settlement first represents the result in the promise owner's
    actor, commits exactly one terminal state, and then emits wakes in waiter
    registration order.  There is intentionally no constructor for an
    already settled promise. -/
inductive PromiseSettlement
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → PromiseId → SettlementDisposition →
      ActorId → EventualRef → List EventId → ActorWorld → Prop where
  | settle {world representedWorld after : ActorWorld}
      {promise : PromiseId} {owner source : ActorId}
      {waiters : List PromiseWaiter} {disposition : SettlementDisposition}
      {result represented : EventualRef} {history : List EventId} :
      world.promises promise = some (.pending owner waiters) →
      (∀ event, event ∈ history → event ∈ world.causalHistory owner) →
      RemoteRepresentation isValue valueTransfer world source owner result
        representedWorld represented →
      after = commitPromiseSettlement representedWorld promise owner disposition
        represented waiters →
      PromiseSettlement isValue valueTransfer world promise disposition source
        result history after

/-- Any successful settlement leaves the designated promise terminal after
    all wake emissions. -/
theorem PromiseSettlement.result_is_terminal
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world : ActorWorld}
    {promise : PromiseId} {disposition : SettlementDisposition}
    {source : ActorId} {result : EventualRef} {history : List EventId}
    {after : ActorWorld}
    (settlement : PromiseSettlement isValue valueTransfer world promise
      disposition source result history after) :
    ∃ owner represented,
      after.promises promise = some (match disposition with
        | .fulfilled => PromiseState.fulfilled owner represented
        | .broken => PromiseState.broken owner represented) := by
  cases settlement with
  | @settle world representedWorld promise owner source waiters disposition
      result represented history pending subset representation resultAfter =>
      subst after
      refine ⟨owner, represented, ?_⟩
      simp [commitPromiseSettlement,
        ActorWorld.wakeAllWaiters_preserves_promises]

theorem PromiseSettlement.cannot_remain_pending
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world : ActorWorld}
    {promise : PromiseId} {disposition : SettlementDisposition}
    {source : ActorId} {result : EventualRef} {history : List EventId}
    {after : ActorWorld}
    (settlement : PromiseSettlement isValue valueTransfer world promise
      disposition source result history after) :
    ¬∃ owner waiters,
      after.promises promise = some (PromiseState.pending owner waiters) := by
  intro pending
  rcases settlement.result_is_terminal with ⟨owner, represented, terminal⟩
  rcases pending with ⟨pendingOwner, waiters, pendingLookup⟩
  rw [terminal] at pendingLookup
  cases disposition <;> simp at pendingLookup

end Newspeak
