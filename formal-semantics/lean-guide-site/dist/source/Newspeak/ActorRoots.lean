import Newspeak.ActorTransitions

namespace Newspeak

inductive HeapLocation where
  | shared
  | actor (identity : ActorId)
deriving Repr, DecidableEq, BEq

structure LocatedObjectReference where
  location : HeapLocation
  object : ObjRef
deriving Repr, DecidableEq, BEq

def visibleObjectRootReferences (actor : ActorId) (object : ObjRef) :
    List LocatedObjectReference :=
  [⟨.actor actor, object⟩, ⟨.shared, object⟩]

def actorPrivateObjectRootReference (actor : ActorId) (object : ObjRef) :
    LocatedObjectReference :=
  ⟨.actor actor, object⟩

def eventualReferenceObjectRoots (actor : ActorId) :
    EventualRef → List LocatedObjectReference
  | .near object => visibleObjectRootReferences actor object
  | .promise _ | .far _ => []

def eventualMessageObjectRoots (actor : ActorId)
    (message : EventualMessage) : List LocatedObjectReference :=
  message.arguments.flatMap (eventualReferenceObjectRoots actor)

def promiseWaiterObjectRoots (waiter : PromiseWaiter) :
    List LocatedObjectReference :=
  eventualMessageObjectRoots waiter.actor waiter.message

def promiseStateObjectRoots : PromiseState → List LocatedObjectReference
  | .pending _ waiters => waiters.flatMap promiseWaiterObjectRoots
  | .fulfilled owner result | .broken owner result =>
      eventualReferenceObjectRoots owner result

/-- Packet payloads are not all represented in the same heap.  Application
    receivers and arguments have already been represented for the destination;
    settlement and wake results remain represented in the source until
    dequeue.  A wake's suspended message remains relative to its destination. -/
def actorPacketObjectRoots (packet : ActorPacket) :
    List LocatedObjectReference :=
  match packet.payload with
  | .application receiver message _ =>
      actorPrivateObjectRootReference packet.destination receiver ::
        eventualMessageObjectRoots packet.destination message
  | .settlement _ _ result =>
      eventualReferenceObjectRoots packet.source result
  | .wake _ _ _ result message _ =>
      eventualReferenceObjectRoots packet.source result ++
        eventualMessageObjectRoots packet.destination message

def externalObjectsForActor (externalRoots : List LocatedObjectReference)
    (actor : ActorId) : List ObjRef :=
  externalRoots.filterMap fun root =>
    match root.location with
    | .actor owner => if owner = actor then some root.object else none
    | .shared => none

def sequentialConfigurationLocatedRoots (p : Program) (actor : ActorId)
    (config : SequentialConfig) (externalRoots : List LocatedObjectReference) :
    List LocatedObjectReference :=
  (sequentialRuntimeRootReferences p config
    (externalObjectsForActor externalRoots actor)).flatMap
      (visibleObjectRootReferences actor)

def actorRunStateObjectRoots (p : Program) (actor : ActorId)
    (externalRoots : List LocatedObjectReference) :
    ActorRunState → List LocatedObjectReference
  | .idle => []
  | .runningTurn config _ _ | .pausedTurn config _ _ _ _ =>
      sequentialConfigurationLocatedRoots p actor config externalRoots

namespace ActorWorld

def runStateObjectRoots (world : ActorWorld)
    (externalRoots : List LocatedObjectReference) :
    List LocatedObjectReference :=
  world.runStates.domain.flatMap fun actor =>
    match world.runStates actor with
    | none => []
    | some state =>
        actorRunStateObjectRoots world.program actor externalRoots state

def mailboxObjectRoots (world : ActorWorld) : List LocatedObjectReference :=
  world.mailboxes.values.flatMap fun mailbox =>
    mailbox.flatMap actorPacketObjectRoots

def networkObjectRoots (world : ActorWorld) : List LocatedObjectReference :=
  world.network.flatMap actorPacketObjectRoots

def promiseObjectRoots (world : ActorWorld) : List LocatedObjectReference :=
  world.promises.values.flatMap promiseStateObjectRoots

def farReferenceObjectRoots (world : ActorWorld) :
    List LocatedObjectReference :=
  world.farReferences.values.map fun target =>
    actorPrivateObjectRootReference target.actor target.object

/-- All roots held by the actor scheduler and eventual-reference substrate.
    External roots retain their explicit heap location.  Duplicates from
    overlapping suspended state are removed at the boundary. -/
def runtimeObjectRoots (world : ActorWorld)
    (externalRoots : List LocatedObjectReference) :
    List LocatedObjectReference :=
  FiniteStore.deduplicated
    (externalRoots ++
      world.runStateObjectRoots externalRoots ++
      world.mailboxObjectRoots ++
      world.networkObjectRoots ++
      world.promiseObjectRoots ++
      world.farReferenceObjectRoots)

theorem runtimeObjectRoots_nodup (world : ActorWorld)
    (externalRoots : List LocatedObjectReference) :
    (world.runtimeObjectRoots externalRoots).Nodup :=
  FiniteStore.deduplicated_nodup _

theorem externalRoot_mem_runtimeObjectRoots (world : ActorWorld)
    (externalRoots : List LocatedObjectReference)
    (root : LocatedObjectReference) (member : root ∈ externalRoots) :
    root ∈ world.runtimeObjectRoots externalRoots := by
  simp [runtimeObjectRoots, FiniteStore.mem_deduplicated, member]

def objectReferencesAtLocation (roots : List LocatedObjectReference)
    (location : HeapLocation) : List ObjRef :=
  roots.filterMap fun root =>
    if root.location = location then some root.object else none

@[simp] theorem mem_objectReferencesAtLocation_iff
    (roots : List LocatedObjectReference) (location : HeapLocation)
    (object : ObjRef) :
    object ∈ objectReferencesAtLocation roots location ↔
      ⟨location, object⟩ ∈ roots := by
  simp only [objectReferencesAtLocation, List.mem_filterMap]
  constructor
  · rintro ⟨⟨rootLocation, rootObject⟩, member, selected⟩
    by_cases atLocation : rootLocation = location
    · simp [atLocation] at selected
      subst rootObject
      subst rootLocation
      exact member
    · simp [atLocation] at selected
  · intro member
    exact ⟨⟨location, object⟩, member, by simp⟩

theorem objectReferencesAtLocation_nodup
    (roots : List LocatedObjectReference) (location : HeapLocation)
    (unique : roots.Nodup) :
    (objectReferencesAtLocation roots location).Nodup := by
  induction roots with
  | nil => simp [objectReferencesAtLocation]
  | cons root remaining ih =>
      cases unique with
      | cons notMember tailUnique =>
          simp only [objectReferencesAtLocation, List.filterMap_cons]
          by_cases atLocation : root.location = location
          · simp [atLocation]
            constructor
            · intro candidate candidateMember candidateLocation objectEqual
              apply notMember candidate candidateMember
              cases root
              cases candidate
              simp_all
            · exact ih tailUnique
          · simp [atLocation]
            exact ih tailUnique

def rootsAtLocation (world : ActorWorld)
    (externalRoots : List LocatedObjectReference) (location : HeapLocation) :
    List ObjRef :=
  objectReferencesAtLocation (world.runtimeObjectRoots externalRoots) location

@[simp] theorem mem_rootsAtLocation_iff (world : ActorWorld)
    (externalRoots : List LocatedObjectReference) (location : HeapLocation)
    (object : ObjRef) :
    object ∈ world.rootsAtLocation externalRoots location ↔
      ⟨location, object⟩ ∈ world.runtimeObjectRoots externalRoots := by
  exact mem_objectReferencesAtLocation_iff _ _ _

theorem rootsAtLocation_nodup (world : ActorWorld)
    (externalRoots : List LocatedObjectReference) (location : HeapLocation) :
    (world.rootsAtLocation externalRoots location).Nodup := by
  exact objectReferencesAtLocation_nodup _ _
    (world.runtimeObjectRoots_nodup externalRoots)

end ActorWorld
end Newspeak
