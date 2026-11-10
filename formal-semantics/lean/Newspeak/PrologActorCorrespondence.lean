import Newspeak.ActorExecution
import Newspeak.PrologLookupCorrespondence

/-!
# Correspondence with the actor-turn Prolog bridge

This file continues the shallow, clause-for-constructor correspondence of
`PrologLookupCorrespondence` across the sequential/actor boundary.  Abstract
platform operations remain explicit proof-carrying application graphs; the
language-defined turn transitions are related bidirectionally to their named
Lean judgments.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologLocalMessageMaterialization
    (materialize : LocalMessageMaterialization) (world : ActorWorld)
    (actor : ActorId) (eventual : EventualMessage) : Message → Prop where
  | application {message : Message} :
      materialize world actor eventual message →
      PrologLocalMessageMaterialization materialize world actor eventual message

theorem prologLocalMessageMaterialization_iff
    {materialize : LocalMessageMaterialization} {world : ActorWorld}
    {actor : ActorId} {eventual : EventualMessage} {message : Message} :
    PrologLocalMessageMaterialization materialize world actor eventual message ↔
      materialize world actor eventual message := by
  constructor
  · intro derivation
    cases derivation with
    | application premise => exact premise
  · exact PrologLocalMessageMaterialization.application

inductive PrologApplicationTurnConfiguration (p : Program)
    (state : AllocationState) (receiver : ObjRef) (message : Message) :
    SequentialConfig → Prop where
  | application : PrologApplicationTurnConfiguration p state receiver message
      (p.applicationTurnConfiguration state receiver message)

theorem prologApplicationTurnConfiguration_iff
    {p : Program} {state : AllocationState} {receiver : ObjRef}
    {message : Message} {configuration : SequentialConfig} :
    PrologApplicationTurnConfiguration p state receiver message configuration ↔
      p.applicationTurnConfiguration state receiver message = configuration := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

inductive PrologStartApplicationTurn (world : ActorWorld) (actor : ActorId)
    (state : AllocationState) (packet : ActorPacket)
    (remaining : List ActorPacket) (receiver : ObjRef) (message : Message)
    (replyPromise : PromiseId) : ActorWorld → Prop where
  | application : PrologStartApplicationTurn world actor state packet remaining
      receiver message replyPromise
      (world.startApplicationTurn actor state packet remaining receiver message
        replyPromise)

theorem prologStartApplicationTurn_iff
    {world after : ActorWorld} {actor : ActorId} {state : AllocationState}
    {packet : ActorPacket} {remaining : List ActorPacket} {receiver : ObjRef}
    {message : Message} {replyPromise : PromiseId} :
    PrologStartApplicationTurn world actor state packet remaining receiver
      message replyPromise after ↔
      world.startApplicationTurn actor state packet remaining receiver message
        replyPromise = after := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

inductive PrologActorTurnStartStep
    (materialize : LocalMessageMaterialization) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | application {world after : ActorWorld} {state : AllocationState}
      {packet : ActorPacket} {remaining : List ActorPacket}
      {receiver : ObjRef} {eventualMessage : EventualMessage}
      {message : Message} {replyPromise : PromiseId} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      world.actorAllocations actor = some state →
      packet.payload = .application receiver eventualMessage replyPromise →
      PrologLocalMessageMaterialization materialize world actor eventualMessage
        message →
      PrologStartApplicationTurn world actor state packet remaining receiver
        message replyPromise after →
      PrologActorTurnStartStep materialize actor world after

theorem prologActorTurnStartStep_iff
    {materialize : LocalMessageMaterialization} {actor : ActorId}
    {before after : ActorWorld} :
    PrologActorTurnStartStep materialize actor before after ↔
      ActorTurnStartStep materialize actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | application idle mailbox allocation payload materialized started =>
        have startEqual := prologStartApplicationTurn_iff.mp started
        subst after
        exact .application idle mailbox allocation payload
          (prologLocalMessageMaterialization_iff.mp materialized)
  · intro derivation
    cases derivation with
    | application idle mailbox allocation payload materialized =>
        exact .application idle mailbox allocation payload
          (prologLocalMessageMaterialization_iff.mpr materialized) .application

inductive PrologActorHeapWellFormed (p : Program) (heap : Heap) : Prop where
  | witness : p.WellFormed heap → PrologActorHeapWellFormed p heap

theorem prologActorHeapWellFormed_iff {p : Program} {heap : Heap} :
    PrologActorHeapWellFormed p heap ↔ p.WellFormed heap := by
  constructor
  · intro derivation
    cases derivation with
    | witness premise => exact premise
  · exact PrologActorHeapWellFormed.witness

inductive PrologNonTurnTerminal (config : SequentialConfig) : Prop where
  | witness : ¬config.TurnTerminal → PrologNonTurnTerminal config

theorem prologNonTurnTerminal_iff {config : SequentialConfig} :
    PrologNonTurnTerminal config ↔ ¬config.TurnTerminal := by
  constructor
  · intro derivation
    cases derivation with
    | witness premise => exact premise
  · exact PrologNonTurnTerminal.witness

inductive PrologNonEventualDispatch (config : SequentialConfig) : Prop where
  | witness : ¬config.EventualDispatch → PrologNonEventualDispatch config

theorem prologNonEventualDispatch_iff {config : SequentialConfig} :
    PrologNonEventualDispatch config ↔ ¬config.EventualDispatch := by
  constructor
  · intro derivation
    cases derivation with
    | witness premise => exact premise
  · exact PrologNonEventualDispatch.witness

inductive PrologAdvanceRunningTurn (world : ActorWorld) (actor : ActorId)
    (after : SequentialConfig) (replyPromise : PromiseId)
    (triggeringEvent : EventId) : ActorWorld → Prop where
  | application : PrologAdvanceRunningTurn world actor after replyPromise
      triggeringEvent
      (world.advanceRunningTurn actor after replyPromise triggeringEvent)

theorem prologAdvanceRunningTurn_iff
    {world result : ActorWorld} {actor : ActorId} {after : SequentialConfig}
    {replyPromise : PromiseId} {triggeringEvent : EventId} :
    PrologAdvanceRunningTurn world actor after replyPromise triggeringEvent
      result ↔
      world.advanceRunningTurn actor after replyPromise triggeringEvent = result := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

/-- The admissible sequential premise is the same narrow certificate boundary
    already exposed by `prologSequentialStepWithTopLevel_iff`: raw Horn class
    allocation clauses omit Lean's post-allocation global-coherence proof. -/
inductive PrologActorSequentialStep (p : Program) (reifier : ErrorReifier p)
    (actor : ActorId) : ActorWorld → ActorWorld → Prop where
  | advance {world result : ActorWorld} {before after : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId} :
      world.runStates actor =
        some (.runningTurn before replyPromise triggeringEvent) →
      world.actorAllocations actor = some before.allocation →
      world.program = p →
      PrologActorHeapWellFormed p before.allocation.heap →
      PrologNonTurnTerminal before →
      PrologNonEventualDispatch before →
      PrologSequentialStepWithTopLevelAdmissible p reifier before after →
      PrologAdvanceRunningTurn world actor after replyPromise triggeringEvent
        result →
      PrologActorSequentialStep p reifier actor world result

theorem prologActorSequentialStep_iff
    {p : Program} {reifier : ErrorReifier p} {actor : ActorId}
    {before after : ActorWorld} :
    PrologActorSequentialStep p reifier actor before after ↔
      ActorSequentialStep p reifier actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | advance running allocation program wellFormed nonterminal nonEventual
        sequential advanced =>
        have advanceEqual := prologAdvanceRunningTurn_iff.mp advanced
        subst after
        exact .advance running allocation program
          (prologActorHeapWellFormed_iff.mp wellFormed)
          (prologNonTurnTerminal_iff.mp nonterminal)
          (prologNonEventualDispatch_iff.mp nonEventual)
          (prologSequentialStepWithTopLevel_iff.mp sequential)
  · intro derivation
    cases derivation with
    | advance running allocation program wellFormed nonterminal nonEventual
        sequential =>
        exact .advance running allocation program
          (prologActorHeapWellFormed_iff.mpr wellFormed)
          (prologNonTurnTerminal_iff.mpr nonterminal)
          (prologNonEventualDispatch_iff.mpr nonEventual)
          (prologSequentialStepWithTopLevel_iff.mpr sequential) .application

/-! ## Remote representation -/

inductive PrologActorIsValue
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (world : ActorWorld) (actor : ActorId) (object : ObjRef) : Prop where
  | witness : isValue world actor object →
      PrologActorIsValue isValue world actor object

inductive PrologActorIsNotValue
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (world : ActorWorld) (actor : ActorId) (object : ObjRef) : Prop where
  | witness : ¬isValue world actor object →
      PrologActorIsNotValue isValue world actor object

inductive PrologActorValueTransfer (valueTransfer : ValueTransferRelation)
    (world : ActorWorld) (source destination : ActorId) (object : ObjRef) :
    ActorWorld → ObjRef → Prop where
  | witness {after : ActorWorld} {represented : ObjRef} :
      valueTransfer world source destination object after represented →
      PrologActorValueTransfer valueTransfer world source destination object
        after represented

inductive PrologActorOwnsNearReference (world : ActorWorld) (actor : ActorId)
    (object : ObjRef) : Prop where
  | witness : world.ownsNearReference actor object →
      PrologActorOwnsNearReference world actor object

inductive PrologActorSharedLiveObject (world : ActorWorld)
    (object : ObjRef) : Prop where
  | witness : world.valueHeap.IsLiveObject object →
      PrologActorSharedLiveObject world object

theorem prologActorIsValue_iff {isValue world actor object} :
    PrologActorIsValue isValue world actor object ↔
      isValue world actor object := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologActorIsNotValue_iff {isValue world actor object} :
    PrologActorIsNotValue isValue world actor object ↔
      ¬isValue world actor object := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologActorValueTransfer_iff
    {valueTransfer world source destination object after represented} :
    PrologActorValueTransfer valueTransfer world source destination object after
      represented ↔
      valueTransfer world source destination object after represented := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologActorOwnsNearReference_iff {world actor object} :
    PrologActorOwnsNearReference world actor object ↔
      ActorWorld.ownsNearReference world actor object := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologActorSharedLiveObject_iff {world object} :
    PrologActorSharedLiveObject world object ↔
      world.valueHeap.IsLiveObject object := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologRemoteRepresentation
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → ActorId → ActorId → EventualRef →
      ActorWorld → EventualRef → Prop where
  | same {world source reference} :
      PrologRemoteRepresentation isValue valueTransfer world source source
        reference world reference
  | value {world after source destination object represented} :
      source ≠ destination →
      PrologActorIsValue isValue world source object →
      PrologActorValueTransfer valueTransfer world source destination object
        after represented →
      PrologRemoteRepresentation isValue valueTransfer world source destination
        (.near object) after (.near represented)
  | farHome {world source destination identity object} :
      source ≠ destination →
      world.farReferences identity = some ⟨destination, object⟩ →
      PrologRemoteRepresentation isValue valueTransfer world source destination
        (.far identity) world (.near object)
  | farPass {world source destination identity targetActor object} :
      source ≠ destination →
      world.farReferences identity = some ⟨targetActor, object⟩ →
      targetActor ≠ destination →
      PrologRemoteRepresentation isValue valueTransfer world source destination
        (.far identity) world (.far identity)
  | promise {world source destination identity state} :
      source ≠ destination →
      world.promises identity = some state →
      PrologRemoteRepresentation isValue valueTransfer world source destination
        (.promise identity) world (.promise identity)
  | nearFar {world source destination object} :
      source ≠ destination →
      PrologActorOwnsNearReference world source object →
      PrologActorIsNotValue isValue world source object →
      PrologRemoteRepresentation isValue valueTransfer world source destination
        (.near object) (world.installNextFarReference source object).1
        (.far (world.installNextFarReference source object).2)

theorem prologRemoteRepresentation_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {source destination : ActorId} {reference represented : EventualRef} :
    PrologRemoteRepresentation isValue valueTransfer world source destination
      reference after represented ↔
      RemoteRepresentation isValue valueTransfer world source destination
        reference after represented := by
  constructor
  · intro derivation
    cases derivation with
    | same => exact .same
    | value different value transfer =>
        exact .value different (prologActorIsValue_iff.mp value)
          (prologActorValueTransfer_iff.mp transfer)
    | farHome different lookup => exact .farHome different lookup
    | farPass different lookup notHome =>
        exact .farPass different lookup notHome
    | promise different lookup => exact .promise different lookup
    | nearFar different owns notValue =>
        exact .nearFar different (prologActorOwnsNearReference_iff.mp owns)
          (prologActorIsNotValue_iff.mp notValue)
  · intro derivation
    cases derivation with
    | same => exact .same
    | value different value transfer =>
        exact .value different (prologActorIsValue_iff.mpr value)
          (prologActorValueTransfer_iff.mpr transfer)
    | farHome different lookup => exact .farHome different lookup
    | farPass different lookup notHome =>
        exact .farPass different lookup notHome
    | promise different lookup => exact .promise different lookup
    | nearFar different owns notValue =>
        exact .nearFar different (prologActorOwnsNearReference_iff.mpr owns)
          (prologActorIsNotValue_iff.mpr notValue)

inductive PrologRemoteArgumentListRepresentation
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (source destination : ActorId) :
    ActorWorld → List EventualRef → ActorWorld → List EventualRef → Prop where
  | nil (world : ActorWorld) :
      PrologRemoteArgumentListRepresentation isValue valueTransfer source
        destination world [] world []
  | cons {world middle after : ActorWorld} {argument represented : EventualRef}
      {arguments representedArguments : List EventualRef} :
      PrologRemoteRepresentation isValue valueTransfer world source destination
        argument middle represented →
      PrologRemoteArgumentListRepresentation isValue valueTransfer source
        destination middle arguments after representedArguments →
      PrologRemoteArgumentListRepresentation isValue valueTransfer source
        destination world (argument :: arguments) after
        (represented :: representedArguments)

theorem prologRemoteArgumentListRepresentation_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {source destination : ActorId}
    {world after : ActorWorld} {arguments represented : List EventualRef} :
    PrologRemoteArgumentListRepresentation isValue valueTransfer source
      destination world arguments after represented ↔
      RemoteArgumentListRepresentation isValue valueTransfer source destination
        world arguments after represented := by
  constructor
  · intro derivation
    induction derivation with
    | nil => exact .nil _
    | cons representation _ ih =>
        exact .cons (prologRemoteRepresentation_iff.mp representation) ih
  · intro derivation
    induction derivation with
    | nil => exact .nil _
    | cons representation _ ih =>
        exact .cons (prologRemoteRepresentation_iff.mpr representation) ih

inductive PrologRemoteMessageRepresentation
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (source destination : ActorId) :
    ActorWorld → EventualMessage → ActorWorld → EventualMessage → Prop where
  | message {world after : ActorWorld} {selector : Selector}
      {arguments representedArguments : List EventualRef} :
      PrologRemoteArgumentListRepresentation isValue valueTransfer source
        destination world arguments after representedArguments →
      PrologRemoteMessageRepresentation isValue valueTransfer source destination
        world ⟨selector, arguments⟩ after ⟨selector, representedArguments⟩

theorem prologRemoteMessageRepresentation_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {source destination : ActorId}
    {world after : ActorWorld} {message represented : EventualMessage} :
    PrologRemoteMessageRepresentation isValue valueTransfer source destination
      world message after represented ↔
      RemoteMessageRepresentation isValue valueTransfer source destination
        world message after represented := by
  constructor
  · intro derivation
    cases derivation with
    | message arguments =>
        exact .message (prologRemoteArgumentListRepresentation_iff.mp arguments)
  · intro derivation
    cases derivation with
    | message arguments =>
        exact .message (prologRemoteArgumentListRepresentation_iff.mpr arguments)

/-! ## Routing and asynchronous return -/

inductive PrologEventualTarget (world : ActorWorld) (current : ActorId) :
    EventualRef → ActorId → ObjRef → Prop where
  | nearPrivate {object : ObjRef} :
      PrologActorOwnsNearReference world current object →
      PrologEventualTarget world current (.near object) current object
  | nearShared {object : ObjRef} :
      PrologActorSharedLiveObject world object →
      PrologEventualTarget world current (.near object) current object
  | far {identity : FarRefId} {target : FarReferenceTarget} :
      world.farReferences identity = some target →
      PrologEventualTarget world current (.far identity) target.actor target.object

theorem prologEventualTarget_iff {world current receiver actor object} :
    PrologEventualTarget world current receiver actor object ↔
      EventualTarget world current receiver actor object := by
  constructor
  · intro derivation
    cases derivation with
    | nearPrivate owns =>
        exact .nearPrivate (prologActorOwnsNearReference_iff.mp owns)
    | nearShared live =>
        exact .nearShared (prologActorSharedLiveObject_iff.mp live)
    | far lookup => exact .far lookup
  · intro derivation
    cases derivation with
    | nearPrivate owns =>
        exact .nearPrivate (prologActorOwnsNearReference_iff.mpr owns)
    | nearShared live =>
        exact .nearShared (prologActorSharedLiveObject_iff.mpr live)
    | far lookup => exact .far lookup

inductive PrologPromiseSettlement
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → PromiseId → SettlementDisposition → ActorId → EventualRef →
      List EventId → ActorWorld → Prop where
  | settle {world representedWorld after : ActorWorld}
      {promise : PromiseId} {owner source : ActorId}
      {waiters : List PromiseWaiter} {disposition : SettlementDisposition}
      {result represented : EventualRef} {history : List EventId} :
      world.promises promise = some (.pending owner waiters) →
      (∀ event, event ∈ history → event ∈ world.causalHistory owner) →
      PrologRemoteRepresentation isValue valueTransfer world source owner result
        representedWorld represented →
      after = commitPromiseSettlement representedWorld promise owner disposition
        represented waiters →
      PrologPromiseSettlement isValue valueTransfer world promise disposition
        source result history after

theorem prologPromiseSettlement_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {promise : PromiseId} {disposition : SettlementDisposition}
    {source : ActorId} {result : EventualRef} {history : List EventId} :
    PrologPromiseSettlement isValue valueTransfer world promise disposition
      source result history after ↔
      PromiseSettlement isValue valueTransfer world promise disposition source
        result history after := by
  constructor
  · intro derivation
    cases derivation with
    | settle pending subset representation committed =>
        exact .settle pending subset
          (prologRemoteRepresentation_iff.mp representation) committed
  · intro derivation
    cases derivation with
    | settle pending subset representation committed =>
        exact .settle pending subset
          (prologRemoteRepresentation_iff.mpr representation) committed

inductive PrologRouteEventualMessage
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → ActorId → EventualRef → EventualMessage → PromiseId →
      List EventId → ActorWorld → Prop where
  | target {world representedWorld after : ActorWorld}
      {requester targetActor : ActorId} {receiver : EventualRef}
      {targetObject : ObjRef} {message representedMessage : EventualMessage}
      {resultPromise : PromiseId} {history : List EventId} :
      PrologEventualTarget world requester receiver targetActor targetObject →
      PrologRemoteMessageRepresentation isValue valueTransfer requester
        targetActor world message representedWorld representedMessage →
      after = representedWorld.emitPacket requester targetActor
        (.application targetObject representedMessage resultPromise) →
      PrologRouteEventualMessage isValue valueTransfer world requester receiver
        message resultPromise history after
  | pending {world : ActorWorld} {requester owner : ActorId}
      {promise resultPromise : PromiseId} {waiters : List PromiseWaiter}
      {message : EventualMessage} {history : List EventId} :
      world.promises promise = some (.pending owner waiters) →
      PrologRouteEventualMessage isValue valueTransfer world requester
        (.promise promise) message resultPromise history
        (world.registerPromiseWaiter promise owner waiters
          ⟨requester, message, resultPromise, history⟩)
  | fulfilled {world representedWorld after : ActorWorld}
      {requester owner : ActorId} {promise resultPromise : PromiseId}
      {result represented : EventualRef} {message : EventualMessage}
      {history : List EventId} :
      world.promises promise = some (.fulfilled owner result) →
      PrologRemoteRepresentation isValue valueTransfer world owner requester
        result representedWorld represented →
      PrologRouteEventualMessage isValue valueTransfer representedWorld requester
        represented message resultPromise history after →
      PrologRouteEventualMessage isValue valueTransfer world requester
        (.promise promise) message resultPromise history after
  | broken {world representedWorld after : ActorWorld}
      {requester owner : ActorId} {promise resultPromise : PromiseId}
      {exception represented : EventualRef} {message : EventualMessage}
      {history : List EventId} :
      world.promises promise = some (.broken owner exception) →
      PrologRemoteRepresentation isValue valueTransfer world owner requester
        exception representedWorld represented →
      PrologPromiseSettlement isValue valueTransfer representedWorld
        resultPromise .broken requester represented history after →
      PrologRouteEventualMessage isValue valueTransfer world requester
        (.promise promise) message resultPromise history after

theorem prologRouteEventualMessage_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {requester : ActorId} {receiver : EventualRef} {message : EventualMessage}
    {resultPromise : PromiseId} {history : List EventId} :
    PrologRouteEventualMessage isValue valueTransfer world requester receiver
      message resultPromise history after ↔
      RouteEventualMessage isValue valueTransfer world requester receiver
        message resultPromise history after := by
  constructor
  · intro derivation
    induction derivation with
    | target target message emitted =>
        exact .target (prologEventualTarget_iff.mp target)
          (prologRemoteMessageRepresentation_iff.mp message) emitted
    | pending pending => exact .pending pending
    | fulfilled fulfilled representation _ ih =>
        exact .fulfilled fulfilled
          (prologRemoteRepresentation_iff.mp representation) ih
    | broken broken representation settlement =>
        exact .broken broken (prologRemoteRepresentation_iff.mp representation)
          (prologPromiseSettlement_iff.mp settlement)
  · intro derivation
    induction derivation with
    | target target message emitted =>
        exact .target (prologEventualTarget_iff.mpr target)
          (prologRemoteMessageRepresentation_iff.mpr message) emitted
    | pending pending => exact .pending pending
    | fulfilled fulfilled representation _ ih =>
        exact .fulfilled fulfilled
          (prologRemoteRepresentation_iff.mpr representation) ih
    | broken broken representation settlement =>
        exact .broken broken (prologRemoteRepresentation_iff.mpr representation)
          (prologPromiseSettlement_iff.mpr settlement)

inductive PrologAsynchronousSend
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorWorld → ActorId → EventualRef → EventualMessage → List EventId →
      ActorWorld → PromiseId → Prop where
  | send {world allocated after : ActorWorld} {actor : ActorId}
      {receiver : EventualRef} {message : EventualMessage}
      {history : List EventId} :
      allocated = (world.allocatePendingPromise actor).1 →
      PrologRouteEventualMessage isValue valueTransfer allocated actor receiver
        message (world.allocatePendingPromise actor).2 history after →
      PrologAsynchronousSend isValue valueTransfer world actor receiver message
        history after (world.allocatePendingPromise actor).2

theorem prologAsynchronousSend_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {actor : ActorId} {receiver : EventualRef} {message : EventualMessage}
    {history : List EventId} {promise : PromiseId} :
    PrologAsynchronousSend isValue valueTransfer world actor receiver message
      history after promise ↔
      AsynchronousSend isValue valueTransfer world actor receiver message history
        after promise := by
  constructor
  · intro derivation
    cases derivation with
    | send allocated route =>
        exact .send allocated (prologRouteEventualMessage_iff.mp route)
  · intro derivation
    cases derivation with
    | send allocated route =>
        exact .send allocated (prologRouteEventualMessage_iff.mpr route)

inductive PrologLocalEventualReferenceInterpretation
    (interpret : LocalEventualReferenceInterpretation) (world : ActorWorld)
    (actor : ActorId) (object : ObjRef) : EventualRef → Prop where
  | witness {reference : EventualRef} : interpret world actor object reference →
      PrologLocalEventualReferenceInterpretation interpret world actor object
        reference

inductive PrologLocalEventualMessageInterpretation
    (interpret : LocalEventualMessageInterpretation) (world : ActorWorld)
    (actor : ActorId) (message : Message) : EventualMessage → Prop where
  | witness {eventual : EventualMessage} : interpret world actor message eventual →
      PrologLocalEventualMessageInterpretation interpret world actor message
        eventual

inductive PrologPromiseHandleInstallation
    (install : PromiseHandleInstallation) (world : ActorWorld)
    (actor : ActorId) (before : AllocationState) (promise : PromiseId) :
    AllocationState → ObjRef → Prop where
  | witness {after : AllocationState} {object : ObjRef} :
      install world actor before promise after object →
      PrologPromiseHandleInstallation install world actor before promise after
        object

theorem prologLocalEventualReferenceInterpretation_iff
    {interpret world actor object reference} :
    PrologLocalEventualReferenceInterpretation interpret world actor object
      reference ↔ interpret world actor object reference := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologLocalEventualMessageInterpretation_iff
    {interpret world actor message eventual} :
    PrologLocalEventualMessageInterpretation interpret world actor message
      eventual ↔ interpret world actor message eventual := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologPromiseHandleInstallation_iff
    {install world actor before promise after object} :
    PrologPromiseHandleInstallation install world actor before promise after
      object ↔ install world actor before promise after object := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologActorEventualSendStep
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
      PrologLocalEventualReferenceInterpretation interpretReference world actor
        receiverObject receiver →
      PrologLocalEventualMessageInterpretation interpretMessage world actor
        message eventualMessage →
      PrologAsynchronousSend isValue valueTransfer world actor receiver
        eventualMessage (world.causalHistory actor) routed resultPromise →
      PrologPromiseHandleInstallation installPromiseHandle routed actor
        config.allocation resultPromise resultAllocation promiseObject →
      PrologActorEventualSendStep interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer actor world
        (routed.advanceRunningTurn actor
          (config.returnEventualPromise resultAllocation promiseObject)
          replyPromise triggeringEvent)

theorem prologActorEventualSendStep_iff
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {actor : ActorId}
    {before after : ActorWorld} :
    PrologActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before after ↔
      ActorEventualSendStep interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | send running allocation control reference message asynchronous installed =>
        exact .send running allocation control
          (prologLocalEventualReferenceInterpretation_iff.mp reference)
          (prologLocalEventualMessageInterpretation_iff.mp message)
          (prologAsynchronousSend_iff.mp asynchronous)
          (prologPromiseHandleInstallation_iff.mp installed)
  · intro derivation
    cases derivation with
    | send running allocation control reference message asynchronous installed =>
        exact .send running allocation control
          (prologLocalEventualReferenceInterpretation_iff.mpr reference)
          (prologLocalEventualMessageInterpretation_iff.mpr message)
          (prologAsynchronousSend_iff.mpr asynchronous)
          (prologPromiseHandleInstallation_iff.mpr installed)

/-! ## Turn completion and system packets -/

inductive PrologActorTurnCompletionStep
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | fulfilledLocal {world settled : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId} {value : ObjRef}
      {waiters : List PromiseWaiter} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      config.stack = .empty →
      config.control = .halt value →
      world.promises replyPromise = some (.pending actor waiters) →
      PrologPromiseSettlement isValue valueTransfer world replyPromise
        .fulfilled actor (.near value) (world.causalHistory actor) settled →
      PrologActorTurnCompletionStep isValue valueTransfer actor world
        (settled.finishRunningTurn actor config.allocation)
  | brokenLocal {world settled : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId}
      {exception : ObjRef} {waiters : List PromiseWaiter} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      config.stack = .empty →
      config.control = .abort exception →
      world.promises replyPromise = some (.pending actor waiters) →
      PrologPromiseSettlement isValue valueTransfer world replyPromise .broken
        actor (.near exception) (world.causalHistory actor) settled →
      PrologActorTurnCompletionStep isValue valueTransfer actor world
        (settled.finishRunningTurn actor config.allocation)
  | fulfilledRemote {world : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId} {value : ObjRef}
      {owner : ActorId} {waiters : List PromiseWaiter} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      config.stack = .empty →
      config.control = .halt value →
      world.promises replyPromise = some (.pending owner waiters) →
      owner ≠ actor →
      PrologActorTurnCompletionStep isValue valueTransfer actor world
        ((world.emitPacket actor owner
          (.settlement replyPromise .fulfilled (.near value))).finishRunningTurn
            actor config.allocation)
  | brokenRemote {world : ActorWorld} {config : SequentialConfig}
      {replyPromise : PromiseId} {triggeringEvent : EventId}
      {exception : ObjRef} {owner : ActorId} {waiters : List PromiseWaiter} :
      world.runStates actor =
        some (.runningTurn config replyPromise triggeringEvent) →
      config.stack = .empty →
      config.control = .abort exception →
      world.promises replyPromise = some (.pending owner waiters) →
      owner ≠ actor →
      PrologActorTurnCompletionStep isValue valueTransfer actor world
        ((world.emitPacket actor owner
          (.settlement replyPromise .broken
            (.near exception))).finishRunningTurn actor config.allocation)

theorem prologActorTurnCompletionStep_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {actor : ActorId}
    {before after : ActorWorld} :
    PrologActorTurnCompletionStep isValue valueTransfer actor before after ↔
      ActorTurnCompletionStep isValue valueTransfer actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | fulfilledLocal running stack control pending settlement =>
        exact .local running stack
          (by simpa [SequentialConfig.turnCompletionControl] using control) pending
          (prologPromiseSettlement_iff.mp settlement)
    | brokenLocal running stack control pending settlement =>
        exact .local running stack
          (by simpa [SequentialConfig.turnCompletionControl] using control) pending
          (prologPromiseSettlement_iff.mp settlement)
    | fulfilledRemote running stack control pending different =>
        exact .remote running stack
          (by simpa [SequentialConfig.turnCompletionControl] using control) pending
          different
    | brokenRemote running stack control pending different =>
        exact .remote running stack
          (by simpa [SequentialConfig.turnCompletionControl] using control) pending
          different
  · intro derivation
    cases derivation with
    | @«local» settled config replyPromise triggeringEvent disposition value
        waiters running stack control pending settlement =>
        cases disposition with
        | fulfilled =>
            exact .fulfilledLocal running stack
              (by simpa [SequentialConfig.turnCompletionControl] using control)
              pending
              (prologPromiseSettlement_iff.mpr settlement)
        | broken =>
            exact .brokenLocal running stack
              (by simpa [SequentialConfig.turnCompletionControl] using control)
              pending
              (prologPromiseSettlement_iff.mpr settlement)
    | @remote config replyPromise triggeringEvent disposition value owner
        waiters running stack control pending different =>
        cases disposition with
        | fulfilled =>
            exact .fulfilledRemote running stack
              (by simpa [SequentialConfig.turnCompletionControl] using control)
              pending different
        | broken =>
            exact .brokenRemote running stack
              (by simpa [SequentialConfig.turnCompletionControl] using control)
              pending different

inductive PrologSettlementPacketDequeueStep
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
      PrologPromiseSettlement isValue valueTransfer consumed promise disposition
        packet.source result (consumed.causalHistory actor) after →
      PrologSettlementPacketDequeueStep isValue valueTransfer actor world after

theorem prologSettlementPacketDequeueStep_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {actor : ActorId}
    {before after : ActorWorld} :
    PrologSettlementPacketDequeueStep isValue valueTransfer actor before after ↔
      SettlementPacketDequeueStep isValue valueTransfer actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | dequeue idle mailbox payload consumed settlement =>
        exact .dequeue idle mailbox payload consumed
          (prologPromiseSettlement_iff.mp settlement)
  · intro derivation
    cases derivation with
    | dequeue idle mailbox payload consumed settlement =>
        exact .dequeue idle mailbox payload consumed
          (prologPromiseSettlement_iff.mpr settlement)

inductive PrologWakePacketDequeueStep
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | fulfilled {world consumed representedWorld after : ActorWorld}
      {packet : ActorPacket} {remaining : List ActorPacket}
      {settledPromise resultPromise : PromiseId} {result represented : EventualRef}
      {message : EventualMessage} {waiterHistory : List EventId} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      packet.payload = .wake settledPromise resultPromise .fulfilled result
        message waiterHistory →
      consumed = world.consumeHeadPacket actor packet remaining waiterHistory →
      PrologRemoteRepresentation isValue valueTransfer consumed packet.source
        actor result representedWorld represented →
      PrologRouteEventualMessage isValue valueTransfer representedWorld actor
        represented message resultPromise (representedWorld.causalHistory actor)
        after →
      PrologWakePacketDequeueStep isValue valueTransfer actor world after
  | broken {world consumed after : ActorWorld} {packet : ActorPacket}
      {remaining : List ActorPacket} {settledPromise resultPromise : PromiseId}
      {result : EventualRef} {message : EventualMessage}
      {waiterHistory : List EventId} :
      world.runStates actor = some .idle →
      world.mailbox actor = packet :: remaining →
      packet.payload = .wake settledPromise resultPromise .broken result message
        waiterHistory →
      consumed = world.consumeHeadPacket actor packet remaining waiterHistory →
      PrologPromiseSettlement isValue valueTransfer consumed resultPromise
        .broken packet.source result (consumed.causalHistory actor) after →
      PrologWakePacketDequeueStep isValue valueTransfer actor world after

theorem prologWakePacketDequeueStep_iff
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {actor : ActorId}
    {before after : ActorWorld} :
    PrologWakePacketDequeueStep isValue valueTransfer actor before after ↔
      WakePacketDequeueStep isValue valueTransfer actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | fulfilled idle mailbox payload consumed represented routed =>
        exact .fulfilled idle mailbox payload consumed
          (prologRemoteRepresentation_iff.mp represented)
          (prologRouteEventualMessage_iff.mp routed)
    | broken idle mailbox payload consumed settlement =>
        exact .broken idle mailbox payload consumed
          (prologPromiseSettlement_iff.mp settlement)
  · intro derivation
    cases derivation with
    | fulfilled idle mailbox payload consumed represented routed =>
        exact .fulfilled idle mailbox payload consumed
          (prologRemoteRepresentation_iff.mpr represented)
          (prologRouteEventualMessage_iff.mpr routed)
    | broken idle mailbox payload consumed settlement =>
        exact .broken idle mailbox payload consumed
          (prologPromiseSettlement_iff.mpr settlement)

inductive PrologPacketEligible (world : ActorWorld) (packet : ActorPacket) : Prop where
  | witness : world.PacketEligible packet → PrologPacketEligible world packet

theorem prologPacketEligible_iff {world packet} :
    PrologPacketEligible world packet ↔ world.PacketEligible packet := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologActorNetworkDeliveryStep : ActorWorld → ActorWorld → Prop where
  | deliver {world : ActorWorld} {packet : ActorPacket} :
      packet ∈ world.network →
      PrologPacketEligible world packet →
      PrologActorNetworkDeliveryStep world (world.acceptNetworkPacket packet)

theorem prologActorNetworkDeliveryStep_iff {before after : ActorWorld} :
    PrologActorNetworkDeliveryStep before after ↔
      ActorNetworkDeliveryStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | deliver member eligible =>
        exact .deliver member (prologPacketEligible_iff.mp eligible)
  · intro derivation
    cases derivation with
    | deliver member eligible =>
        exact .deliver member (prologPacketEligible_iff.mpr eligible)

/-! ## Complete actor-step unions -/

inductive PrologSelectedActorStep (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (actor : ActorId) :
    ActorWorld → ActorWorld → Prop where
  | start {before after : ActorWorld} :
      PrologActorTurnStartStep materialize actor before after →
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after
  | sequential {before after : ActorWorld} :
      PrologActorSequentialStep p reifier actor before after →
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after
  | eventual {before after : ActorWorld} :
      PrologActorEventualSendStep interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer actor before after →
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after
  | complete {before after : ActorWorld} :
      PrologActorTurnCompletionStep isValue valueTransfer actor before after →
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after
  | settlement {before after : ActorWorld} :
      PrologSettlementPacketDequeueStep isValue valueTransfer actor before after →
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after
  | wake {before after : ActorWorld} :
      PrologWakePacketDequeueStep isValue valueTransfer actor before after →
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after

theorem prologSelectedActorStep_iff
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {actor : ActorId}
    {before after : ActorWorld} :
    PrologSelectedActorStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer actor before
      after ↔
      SelectedActorStep p reifier materialize interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer actor before after := by
  constructor
  · intro derivation
    cases derivation with
    | start step => exact .start (prologActorTurnStartStep_iff.mp step)
    | sequential step => exact .sequential (prologActorSequentialStep_iff.mp step)
    | eventual step => exact .eventual (prologActorEventualSendStep_iff.mp step)
    | complete step => exact .complete (prologActorTurnCompletionStep_iff.mp step)
    | settlement step =>
        exact .settlement (prologSettlementPacketDequeueStep_iff.mp step)
    | wake step => exact .wake (prologWakePacketDequeueStep_iff.mp step)
  · intro derivation
    cases derivation with
    | start step => exact .start (prologActorTurnStartStep_iff.mpr step)
    | sequential step => exact .sequential (prologActorSequentialStep_iff.mpr step)
    | eventual step => exact .eventual (prologActorEventualSendStep_iff.mpr step)
    | complete step => exact .complete (prologActorTurnCompletionStep_iff.mpr step)
    | settlement step =>
        exact .settlement (prologSettlementPacketDequeueStep_iff.mpr step)
    | wake step => exact .wake (prologWakePacketDequeueStep_iff.mpr step)

inductive PrologActorActionStep (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorAction → ActorWorld → ActorWorld → Prop where
  | compute {actor : ActorId} {before after : ActorWorld} :
      PrologSelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after →
      PrologActorActionStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer
        (.compute actor) before after
  | deliver {packet : ActorPacket} {before : ActorWorld} :
      packet ∈ before.network →
      PrologPacketEligible before packet →
      PrologActorActionStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer
        (.deliver packet) before (before.acceptNetworkPacket packet)

theorem prologActorActionStep_iff
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {action : ActorAction}
    {before after : ActorWorld} :
    PrologActorActionStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer action before
      after ↔
      ActorActionStep p reifier materialize interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer action before after := by
  constructor
  · intro derivation
    cases derivation with
    | compute step => exact .compute (prologSelectedActorStep_iff.mp step)
    | deliver member eligible =>
        exact .deliver member (prologPacketEligible_iff.mp eligible)
  · intro derivation
    cases derivation with
    | compute step => exact .compute (prologSelectedActorStep_iff.mpr step)
    | deliver member eligible =>
        exact .deliver member (prologPacketEligible_iff.mpr eligible)

def PrologActorSystemStep (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (before after : ActorWorld) : Prop :=
  ∃ action, PrologActorActionStep p reifier materialize interpretReference
    interpretMessage installPromiseHandle isValue valueTransfer action before
    after

theorem prologActorSystemStep_iff
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {before after : ActorWorld} :
    PrologActorSystemStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer before after ↔
      ActorSystemStep p reifier materialize interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer before after := by
  constructor
  · rintro ⟨action, step⟩
    exact ⟨action, prologActorActionStep_iff.mp step⟩
  · rintro ⟨action, step⟩
    exact ⟨action, prologActorActionStep_iff.mpr step⟩

end PrologBridge
end Newspeak
