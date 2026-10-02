import Newspeak.ActorRoots

namespace Newspeak

/-- Resolution of a non-promise eventual receiver.  Near references target
    the current actor; far references target the actor/object pair recorded in
    the global table. -/
inductive EventualTarget (world : ActorWorld) (current : ActorId) :
    EventualRef → ActorId → ObjRef → Prop where
  | nearPrivate {object : ObjRef} :
      world.ownsNearReference current object →
      EventualTarget world current (.near object) current object
  | nearShared {object : ObjRef} :
      world.valueHeap.IsLiveObject object →
      EventualTarget world current (.near object) current object
  | far {identity : FarRefId} {target : FarReferenceTarget} :
      world.farReferences identity = some target →
      EventualTarget world current (.far identity) target.actor target.object

theorem EventualTarget.unique_actor_and_object
    {world : ActorWorld} {current : ActorId} {receiver : EventualRef}
    {actor₁ actor₂ : ActorId} {object₁ object₂ : ObjRef}
    (first : EventualTarget world current receiver actor₁ object₁)
    (second : EventualTarget world current receiver actor₂ object₂) :
    actor₁ = actor₂ ∧ object₁ = object₂ := by
  cases first <;> cases second <;> simp_all

def ActorWorld.registerPromiseWaiter (world : ActorWorld)
    (promise : PromiseId) (owner : ActorId) (waiters : List PromiseWaiter)
    (waiter : PromiseWaiter) : ActorWorld :=
  { world with
    promises := world.promises.install promise
      (.pending owner (waiters ++ [waiter])) }

@[simp] theorem ActorWorld.registerPromiseWaiter_lookup (world : ActorWorld)
    (promise : PromiseId) (owner : ActorId) (waiters : List PromiseWaiter)
    (waiter : PromiseWaiter) :
    (world.registerPromiseWaiter promise owner waiters waiter).promises promise =
      some (.pending owner (waiters ++ [waiter])) := by
  simp [ActorWorld.registerPromiseWaiter]

/-- Eventual routing for known targets, unresolved promises, fulfilled
    promises, and broken promises.  Fulfilled routing may recurse but creates
    no proxy chain because remote representation normalizes the result first. -/
inductive RouteEventualMessage
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → ActorId → EventualRef → EventualMessage →
      PromiseId → List EventId → ActorWorld → Prop where
  | target {world representedWorld after : ActorWorld}
      {requester targetActor : ActorId} {receiver : EventualRef}
      {targetObject : ObjRef} {message representedMessage : EventualMessage}
      {resultPromise : PromiseId} {history : List EventId} :
      EventualTarget world requester receiver targetActor targetObject →
      RemoteMessageRepresentation isValue valueTransfer requester targetActor
        world message representedWorld representedMessage →
      after = representedWorld.emitPacket requester targetActor
        (.application targetObject representedMessage resultPromise) →
      RouteEventualMessage isValue valueTransfer world requester receiver
        message resultPromise history after
  | pending {world : ActorWorld} {requester owner : ActorId}
      {promise resultPromise : PromiseId} {waiters : List PromiseWaiter}
      {message : EventualMessage} {history : List EventId} :
      world.promises promise = some (.pending owner waiters) →
      RouteEventualMessage isValue valueTransfer world requester
        (.promise promise) message resultPromise history
        (world.registerPromiseWaiter promise owner waiters
          ⟨requester, message, resultPromise, history⟩)
  | fulfilled {world representedWorld after : ActorWorld}
      {requester owner : ActorId} {promise resultPromise : PromiseId}
      {result represented : EventualRef} {message : EventualMessage}
      {history : List EventId} :
      world.promises promise = some (.fulfilled owner result) →
      RemoteRepresentation isValue valueTransfer world owner requester result
        representedWorld represented →
      RouteEventualMessage isValue valueTransfer representedWorld requester
        represented message resultPromise history after →
      RouteEventualMessage isValue valueTransfer world requester
        (.promise promise) message resultPromise history after
  | broken {world representedWorld after : ActorWorld}
      {requester owner : ActorId} {promise resultPromise : PromiseId}
      {exception represented : EventualRef} {message : EventualMessage}
      {history : List EventId} :
      world.promises promise = some (.broken owner exception) →
      RemoteRepresentation isValue valueTransfer world owner requester exception
        representedWorld represented →
      PromiseSettlement isValue valueTransfer representedWorld resultPromise
        .broken requester represented history after →
      RouteEventualMessage isValue valueTransfer world requester
        (.promise promise) message resultPromise history after

theorem RouteEventualMessage.pending_registers_at_tail
    {isValue valueTransfer world requester promise message resultPromise
      history after owner waiters}
    (pending : world.promises promise = some (.pending owner waiters))
    (route : RouteEventualMessage isValue valueTransfer world requester
      (.promise promise) message resultPromise history after) :
    after = world.registerPromiseWaiter promise owner waiters
      ⟨requester, message, resultPromise, history⟩ := by
  cases route with
  | target target _ _ => cases target
  | pending routePending =>
      rw [pending] at routePending
      cases routePending
      rfl
  | fulfilled fulfilled _ _ =>
      rw [pending] at fulfilled
      simp at fulfilled
  | broken broken _ _ =>
      rw [pending] at broken
      simp at broken

/-- Actor-level evaluation of an asynchronous send: allocate its result
    promise first, route against that new capability, and return it immediately
    to the running expression. -/
inductive AsynchronousSend
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → ActorId → EventualRef → EventualMessage →
      List EventId → ActorWorld → PromiseId → Prop where
  | send {world allocated after : ActorWorld} {actor : ActorId}
      {receiver : EventualRef} {message : EventualMessage}
      {history : List EventId} :
      allocated = (world.allocatePendingPromise actor).1 →
      RouteEventualMessage isValue valueTransfer allocated actor receiver message
        (world.allocatePendingPromise actor).2 history after →
      AsynchronousSend isValue valueTransfer world actor receiver message history
        after (world.allocatePendingPromise actor).2

theorem AsynchronousSend.resultPromise_is_fresh_frontier
    {isValue valueTransfer world actor receiver message history after promise}
    (send : AsynchronousSend isValue valueTransfer world actor receiver message
      history after promise) :
    promise = ⟨world.nextPromise⟩ := by
  cases send
  rfl

end Newspeak
