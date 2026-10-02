import Newspeak.CollectingExecution

namespace Newspeak

/-- Actor-visible references are deliberately distinct from sequential
    `ObjRef`s.  A near reference is meaningful in one actor heap; promise and
    far-reference identities are global eventual capabilities. -/
inductive EventualRef where
  | near (object : ObjRef)
  | promise (identity : PromiseId)
  | far (identity : FarRefId)
deriving Repr, DecidableEq, BEq

structure EventualMessage where
  selector : Selector
  arguments : List EventualRef
deriving Repr, DecidableEq, BEq

structure PromiseWaiter where
  actor : ActorId
  message : EventualMessage
  resultPromise : PromiseId
  causalHistory : List EventId
deriving Repr, DecidableEq, BEq

inductive SettlementDisposition where
  | fulfilled
  | broken
deriving Repr, DecidableEq, BEq

inductive PromiseState where
  | pending (owner : ActorId) (waiters : List PromiseWaiter)
  | fulfilled (owner : ActorId) (result : EventualRef)
  | broken (owner : ActorId) (exception : EventualRef)
deriving Repr, DecidableEq, BEq

structure FarReferenceTarget where
  actor : ActorId
  object : ObjRef
deriving Repr, DecidableEq, BEq

structure EventRecord where
  source : ActorId
  destination : ActorId
  causalHistory : List EventId
deriving Repr, DecidableEq, BEq

/-- The variant-specific portion of a causal packet.  Common routing fields
    live in `ActorPacket`, preventing malformed packets whose constructor
    fields disagree with generic source/destination projections. -/
inductive ActorPacketPayload where
  | application (receiver : ObjRef) (message : EventualMessage)
      (replyPromise : PromiseId)
  | settlement (promise : PromiseId)
      (disposition : SettlementDisposition) (result : EventualRef)
  | wake (settledPromise resultPromise : PromiseId)
      (disposition : SettlementDisposition) (result : EventualRef)
      (message : EventualMessage) (waiterHistory : List EventId)
deriving Repr, DecidableEq, BEq

structure ActorPacket where
  identity : EventId
  source : ActorId
  destination : ActorId
  causalHistory : List EventId
  payload : ActorPacketPayload
deriving Repr, DecidableEq, BEq

inductive ControlLocation where
  | sourcePoint (site : SiteId)
  | machinePoint (image : CodeImageId) (programCounter : Nat)
deriving Repr, DecidableEq, BEq

inductive DebuggerStopReason where
  | exceptionStop (exception : ObjRef)
  | breakpointStop (location : ControlLocation)
  | requestedStop (request : ObjRef)
deriving Repr, DecidableEq, BEq

inductive ActorRunState where
  | idle
  | runningTurn (config : SequentialConfig)
      (replyPromise : PromiseId) (triggeringEvent : EventId)
  | pausedTurn (config : SequentialConfig)
      (replyPromise : PromiseId) (triggeringEvent : EventId)
      (pauseToken : PauseTokenId) (reason : DebuggerStopReason)

/-- One VM cohort.  Private heaps, run states, mailboxes, and causal histories
    all have exact finite domains.  The monotone identity frontiers turn the
    prose freshness side conditions into executable allocation choices. -/
structure ActorWorld where
  program : Program
  valueHeap : Heap
  actorAllocations : FiniteStore ActorId AllocationState
  runStates : FiniteStore ActorId ActorRunState
  mailboxes : FiniteStore ActorId (List ActorPacket)
  network : List ActorPacket
  promises : FiniteStore PromiseId PromiseState
  farReferences : FiniteStore FarRefId FarReferenceTarget
  histories : FiniteStore ActorId (List EventId)
  eventLedger : FiniteStore EventId EventRecord
  deliveredEvents : FiniteStore ActorId (List EventId)
  vm : VMId
  programVersion : Nat
  nextActor : Nat
  nextPromise : Nat
  nextFarReference : Nat
  nextEvent : Nat
  nextPauseToken : Nat

namespace ActorWorld

def mailbox (world : ActorWorld) (actor : ActorId) : List ActorPacket :=
  (world.mailboxes actor).getD []

def causalHistory (world : ActorWorld) (actor : ActorId) : List EventId :=
  (world.histories actor).getD []

def deliveredTo (world : ActorWorld) (actor : ActorId) : List EventId :=
  (world.deliveredEvents actor).getD []

def ownsNearReference (world : ActorWorld) (actor : ActorId)
    (object : ObjRef) : Prop :=
  ∃ allocation, world.actorAllocations actor = some allocation ∧
    allocation.heap.IsLiveObject object

/-- Pairwise actor-heap isolation from Equation (10.2), stated directly over
    the exact finite object domains. -/
def PrivateHeapsDisjoint (world : ActorWorld) : Prop :=
  ∀ actor₁ actor₂ allocation₁ allocation₂,
    world.actorAllocations actor₁ = some allocation₁ →
    world.actorAllocations actor₂ = some allocation₂ →
    actor₁ ≠ actor₂ →
    ∀ object, allocation₁.heap.IsLiveObject object →
      ¬allocation₂.heap.IsLiveObject object

/-- The shared value heap is disjoint from every actor-private heap. -/
def ValueHeapDisjoint (world : ActorWorld) : Prop :=
  ∀ actor allocation, world.actorAllocations actor = some allocation →
    ∀ object, world.valueHeap.IsLiveObject object →
      ¬allocation.heap.IsLiveObject object

def EventFrontierFresh (world : ActorWorld) : Prop :=
  ∀ event, event ∈ world.eventLedger.domain → event.index < world.nextEvent

def FarReferenceFrontierFresh (world : ActorWorld) : Prop :=
  ∀ reference, reference ∈ world.farReferences.domain →
    reference.index < world.nextFarReference

def PromiseFrontierFresh (world : ActorWorld) : Prop :=
  ∀ promise, promise ∈ world.promises.domain →
    promise.index < world.nextPromise

def ActorFrontierFresh (world : ActorWorld) : Prop :=
  ∀ actor, actor ∈ world.actorAllocations.domain →
    actor.index < world.nextActor

def addEventToSet (history : List EventId) (event : EventId) : List EventId :=
  FiniteStore.deduplicated (history ++ [event])

def mergeEventSets (left right : List EventId) : List EventId :=
  FiniteStore.deduplicated (left ++ right)

/-- Constructive E-order eligibility.  Every causal predecessor addressed to
    the packet's destination must already occupy a delivered/retired position
    there.  A history mentioning an absent ledger event is malformed and is
    therefore ineligible. -/
def PacketEligible (world : ActorWorld) (packet : ActorPacket) : Prop :=
  ∀ predecessor, predecessor ∈ packet.causalHistory →
    ∃ record, world.eventLedger predecessor = some record ∧
      (record.destination = packet.destination →
        predecessor ∈ world.deliveredTo packet.destination)

/-- The common packet-emission operation from Equation (10.8). -/
def emitPacket (world : ActorWorld) (source destination : ActorId)
    (payload : ActorPacketPayload) : ActorWorld :=
  let event : EventId := ⟨world.nextEvent⟩
  let history := world.causalHistory source
  let packet : ActorPacket := ⟨event, source, destination, history, payload⟩
  let ledger := world.eventLedger.install event ⟨source, destination, history⟩
  let histories := world.histories.install source (addEventToSet history event)
  if source = destination then
    { world with
      mailboxes := world.mailboxes.install destination
        (world.mailbox destination ++ [packet])
      deliveredEvents := world.deliveredEvents.install destination
        (world.deliveredTo destination ++ [event])
      eventLedger := ledger
      histories := histories
      nextEvent := world.nextEvent + 1 }
  else
    { world with
      network := world.network ++ [packet]
      eventLedger := ledger
      histories := histories
      nextEvent := world.nextEvent + 1 }

@[simp] theorem emitPacket_nextEvent (world : ActorWorld)
    (source destination : ActorId) (payload : ActorPacketPayload) :
    (world.emitPacket source destination payload).nextEvent =
      world.nextEvent + 1 := by
  by_cases same : source = destination <;> simp [emitPacket, same]

@[simp] theorem emitPacket_eventLedger (world : ActorWorld)
    (source destination : ActorId) (payload : ActorPacketPayload) :
    (world.emitPacket source destination payload).eventLedger
      ⟨world.nextEvent⟩ =
        some ⟨source, destination, world.causalHistory source⟩ := by
  by_cases same : source = destination <;> simp [emitPacket, same]

@[simp] theorem emitPacket_sourceHistory_contains_event (world : ActorWorld)
    (source destination : ActorId) (payload : ActorPacketPayload) :
    (⟨world.nextEvent⟩ : EventId) ∈
      (world.emitPacket source destination payload).causalHistory source := by
  by_cases same : source = destination <;>
    simp [emitPacket, same, causalHistory, addEventToSet]

theorem emitPacket_preserves_eventFrontierFresh (world : ActorWorld)
    (fresh : world.EventFrontierFresh) (source destination : ActorId)
    (payload : ActorPacketPayload) :
    (world.emitPacket source destination payload).EventFrontierFresh := by
  unfold EventFrontierFresh
  intro event member
  rw [emitPacket_nextEvent]
  have installedMember : event ∈
      (world.eventLedger.install ⟨world.nextEvent⟩
        ⟨source, destination, world.causalHistory source⟩).domain := by
    by_cases same : source = destination <;>
      simpa [emitPacket, same] using member
  have domainMember : event = ⟨world.nextEvent⟩ ∨
      event ∈ world.eventLedger.domain := by
    exact (FiniteStore.mem_install_domain_iff _ _ _ _).mp installedMember
  rcases domainMember with atNew | old
  · subst event
    simp
  · exact Nat.lt_succ_of_lt (fresh event old)

/-- Install the uniquely chosen next far-reference identity. -/
def installNextFarReference (world : ActorWorld) (actor : ActorId)
    (object : ObjRef) : ActorWorld × FarRefId :=
  let identity : FarRefId := ⟨world.nextFarReference⟩
  ({ world with
      farReferences := world.farReferences.install identity ⟨actor, object⟩
      nextFarReference := world.nextFarReference + 1 }, identity)

@[simp] theorem installNextFarReference_identity (world : ActorWorld)
    (actor : ActorId) (object : ObjRef) :
    (world.installNextFarReference actor object).2 =
      ⟨world.nextFarReference⟩ := by
  rfl

@[simp] theorem installNextFarReference_lookup (world : ActorWorld)
    (actor : ActorId) (object : ObjRef) :
    (world.installNextFarReference actor object).1.farReferences
      (world.installNextFarReference actor object).2 = some ⟨actor, object⟩ := by
  simp [installNextFarReference]

theorem installNextFarReference_preserves_frontierFresh (world : ActorWorld)
    (fresh : world.FarReferenceFrontierFresh) (actor : ActorId)
    (object : ObjRef) :
    (world.installNextFarReference actor object).1.FarReferenceFrontierFresh := by
  unfold FarReferenceFrontierFresh
  intro reference member
  have domainMember : reference = ⟨world.nextFarReference⟩ ∨
      reference ∈ world.farReferences.domain := by
    exact (FiniteStore.mem_install_domain_iff _ _ _ _).mp (by
      simpa [installNextFarReference] using member)
  rcases domainMember with atNew | old
  · subst reference
    simp [installNextFarReference]
  · simpa [installNextFarReference] using Nat.lt_succ_of_lt (fresh reference old)

end ActorWorld

/-- Platform contract for transferring a deeply immutable value between actor
    heaps.  Sharing and copying are both admitted implementations. -/
abbrev ValueTransferRelation :=
  ActorWorld → ActorId → ActorId → ObjRef → ActorWorld → ObjRef → Prop

/-- Actor-relative remote representation, directly mirroring RR-Same,
    RR-Value, RR-Far-Home, RR-Far-Pass, RR-Promise, and RR-Near-Far. -/
inductive RemoteRepresentation (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → ActorId → ActorId → EventualRef →
      ActorWorld → EventualRef → Prop where
  | same {world source reference} :
      RemoteRepresentation isValue valueTransfer world source source reference
        world reference
  | value {world after source destination object represented} :
      source ≠ destination →
      isValue world source object →
      valueTransfer world source destination object after represented →
      RemoteRepresentation isValue valueTransfer world source destination
        (.near object) after (.near represented)
  | farHome {world source destination identity object} :
      source ≠ destination →
      world.farReferences identity = some ⟨destination, object⟩ →
      RemoteRepresentation isValue valueTransfer world source destination
        (.far identity) world (.near object)
  | farPass {world source destination identity targetActor object} :
      source ≠ destination →
      world.farReferences identity = some ⟨targetActor, object⟩ →
      targetActor ≠ destination →
      RemoteRepresentation isValue valueTransfer world source destination
        (.far identity) world (.far identity)
  | promise {world source destination identity state} :
      source ≠ destination →
      world.promises identity = some state →
      RemoteRepresentation isValue valueTransfer world source destination
        (.promise identity) world (.promise identity)
  | nearFar {world source destination object} :
      source ≠ destination →
      world.ownsNearReference source object →
      ¬isValue world source object →
      RemoteRepresentation isValue valueTransfer world source destination
        (.near object) (world.installNextFarReference source object).1
        (.far (world.installNextFarReference source object).2)

theorem RemoteRepresentation.same_exact {isValue} {valueTransfer}
    {world : ActorWorld} {actor : ActorId} {reference : EventualRef}
    {after : ActorWorld} {represented : EventualRef}
    (relation : RemoteRepresentation isValue valueTransfer world actor actor
      reference after represented) :
    after = world ∧ represented = reference := by
  cases relation with
  | same => exact ⟨rfl, rfl⟩
  | value different _ _ | farHome different _ | farPass different _ _
  | promise different _ | nearFar different _ _ => exact (different rfl).elim

/-- For distinct actors, the five cross-actor constructors are exhaustive:
    values are transferred as near references, a far reference either comes
    home or keeps its identity, promises keep their identity, and a mutable
    near reference becomes one freshly allocated far reference. -/
theorem RemoteRepresentation.cross_actor_classification
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    {world after : ActorWorld} {source destination : ActorId}
    {reference represented : EventualRef}
    (different : source ≠ destination)
    (relation : RemoteRepresentation isValue valueTransfer world source
      destination reference after represented) :
    (∃ original copied,
      reference = .near original ∧ represented = .near copied ∧
      isValue world source original ∧
      valueTransfer world source destination original after copied) ∨
    (∃ identity object,
      reference = .far identity ∧ represented = .near object ∧
      after = world ∧
      world.farReferences identity = some ⟨destination, object⟩) ∨
    (∃ identity state,
      reference = .promise identity ∧ represented = .promise identity ∧
      after = world ∧ world.promises identity = some state) ∨
    (∃ identity targetActor object,
      reference = .far identity ∧ represented = .far identity ∧
      after = world ∧
      world.farReferences identity = some ⟨targetActor, object⟩ ∧
      targetActor ≠ destination) ∨
    (∃ object,
      reference = .near object ∧
      represented = .far (world.installNextFarReference source object).2 ∧
      after = (world.installNextFarReference source object).1 ∧
      world.ownsNearReference source object ∧
      ¬isValue world source object) := by
  cases relation with
  | same => exact (different rfl).elim
  | value actorsDifferent value transfer =>
      exact .inl ⟨_, _, rfl, rfl, value, transfer⟩
  | farHome actorsDifferent target =>
      exact .inr (.inl ⟨_, _, rfl, rfl, rfl, target⟩)
  | farPass actorsDifferent target notHome =>
      exact .inr (.inr (.inr (.inl
        ⟨_, _, _, rfl, rfl, rfl, target, notHome⟩)))
  | promise actorsDifferent present =>
      exact .inr (.inr (.inl ⟨_, _, rfl, rfl, rfl, present⟩))
  | nearFar actorsDifferent owned mutable =>
      exact .inr (.inr (.inr (.inr
        ⟨_, rfl, rfl, rfl, owned, mutable⟩)))

theorem RemoteRepresentation.far_home_normalizes {isValue} {valueTransfer}
    {world after : ActorWorld} {source destination : ActorId}
    {identity : FarRefId} {object : ObjRef} {represented : EventualRef}
    (different : source ≠ destination)
    (target : world.farReferences identity = some ⟨destination, object⟩)
    (relation : RemoteRepresentation isValue valueTransfer world source
      destination (.far identity) after represented) :
    after = world ∧ represented = .near object := by
  cases relation with
  | same => exact (different rfl).elim
  | farHome _ lookup =>
      have equal := Option.some.inj (lookup.symm.trans target)
      cases equal
      exact ⟨rfl, rfl⟩
  | farPass _ lookup notHome =>
      have equal := Option.some.inj (lookup.symm.trans target)
      exact (notHome (FarReferenceTarget.mk.inj equal).1).elim

theorem RemoteRepresentation.far_third_party_preserves_identity
    {isValue} {valueTransfer} {world after : ActorWorld}
    {source destination targetActor : ActorId}
    {identity : FarRefId} {object : ObjRef} {represented : EventualRef}
    (different : source ≠ destination)
    (target : world.farReferences identity = some ⟨targetActor, object⟩)
    (notHome : targetActor ≠ destination)
    (relation : RemoteRepresentation isValue valueTransfer world source
      destination (.far identity) after represented) :
    after = world ∧ represented = .far identity := by
  cases relation with
  | same => exact (different rfl).elim
  | farHome _ lookup =>
      have equal := Option.some.inj (lookup.symm.trans target)
      exact (notHome (FarReferenceTarget.mk.inj equal).1.symm).elim
  | farPass => exact ⟨rfl, rfl⟩

/-- Componentwise message transport.  The intermediate world makes fresh far
    references allocated by earlier arguments visible to later arguments. -/
inductive RemoteArgumentListRepresentation
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (source destination : ActorId) :
    ActorWorld → List EventualRef → ActorWorld → List EventualRef → Prop where
  | nil (world : ActorWorld) :
      RemoteArgumentListRepresentation isValue valueTransfer source destination
        world [] world []
  | cons {world middle after : ActorWorld} {argument represented : EventualRef}
      {arguments representedArguments : List EventualRef} :
      RemoteRepresentation isValue valueTransfer world source destination
        argument middle represented →
      RemoteArgumentListRepresentation isValue valueTransfer source destination
        middle arguments after representedArguments →
      RemoteArgumentListRepresentation isValue valueTransfer source destination
        world (argument :: arguments) after (represented :: representedArguments)

inductive RemoteMessageRepresentation
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (source destination : ActorId) :
    ActorWorld → EventualMessage → ActorWorld → EventualMessage → Prop where
  | message {world after : ActorWorld} {selector : Selector}
      {arguments representedArguments : List EventualRef} :
      RemoteArgumentListRepresentation isValue valueTransfer source destination
        world arguments after representedArguments →
      RemoteMessageRepresentation isValue valueTransfer source destination
        world ⟨selector, arguments⟩ after ⟨selector, representedArguments⟩

theorem RemoteArgumentListRepresentation.preserves_length
    {isValue valueTransfer source destination world arguments after represented}
    (relation : RemoteArgumentListRepresentation isValue valueTransfer
      source destination world arguments after represented) :
    represented.length = arguments.length := by
  induction relation with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RemoteMessageRepresentation.preserves_selector_and_arity
    {isValue valueTransfer source destination world message after represented}
    (relation : RemoteMessageRepresentation isValue valueTransfer source
      destination world message after represented) :
    represented.selector = message.selector ∧
      represented.arguments.length = message.arguments.length := by
  cases relation with
  | message arguments => exact ⟨rfl, arguments.preserves_length⟩

end Newspeak
