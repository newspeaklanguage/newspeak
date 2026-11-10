import Newspeak.ReflectionVMs
import Newspeak.ReflectionQueries
import Newspeak.PrologActorCorrespondence

/-!
# Correspondence with the reflective Prolog bridge

The platform/front-end functions remain parameters, exactly as in the Lean
semantics.  Proof-carrying Horn application records expose their premises;
the commit and rejection rules themselves are related bidirectionally.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologMirrorAuthorizes (world : ActorWorld) (actor : ActorId)
    (mirror : MirrorId) (target : MirrorTarget) (right : ReflectRight) : Prop where
  | witness : MirrorAuthorizes world actor mirror target right →
      PrologMirrorAuthorizes world actor mirror target right

theorem prologMirrorAuthorizes_iff {world actor mirror target right} :
    PrologMirrorAuthorizes world actor mirror target right ↔
      MirrorAuthorizes world actor mirror target right := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologReflectionQueryExecution (world : ActorWorld)
    (query : ReflectionQuery) : ReflectionQueryResult → Prop where
  | witness {result : ReflectionQueryResult} :
      query.execute world = some result →
      PrologReflectionQueryExecution world query result

theorem prologReflectionQueryExecution_iff {world query result} :
    PrologReflectionQueryExecution world query result ↔
      ReflectionQuery.execute world query = some result := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologAuthorizedReflectionRead (world : ActorWorld)
    (requester : ActorId) (query : ReflectionQuery) :
    ReflectionQueryResult → Prop where
  | inspect {result : ReflectionQueryResult} :
      PrologMirrorAuthorizes world requester query.mirror
        (query.authorizationTarget world) .inspect →
      PrologReflectionQueryExecution world query result →
      PrologAuthorizedReflectionRead world requester query result

theorem prologAuthorizedReflectionRead_iff {world requester query result} :
    PrologAuthorizedReflectionRead world requester query result ↔
      AuthorizedReflectionRead world requester query result := by
  constructor
  · intro derivation
    cases derivation with
    | inspect authorized executed =>
        exact ⟨prologMirrorAuthorizes_iff.mp authorized,
          prologReflectionQueryExecution_iff.mp executed⟩
  · intro read
    exact .inspect (prologMirrorAuthorizes_iff.mpr read.authorized)
      (prologReflectionQueryExecution_iff.mpr read.executed)

inductive PrologValidReflection {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (validate : ReflectionValidator SourceImage)
    (before : ReflectiveVM SourceImage) (requester : ActorId)
    (transaction : List ReflectionCommand) : ReflectiveVM SourceImage → Prop where
  | witness {after : ReflectiveVM SourceImage} :
      ValidReflection frontEnd prepareRuntime validate before requester
        transaction after →
      PrologValidReflection frontEnd prepareRuntime validate before requester
        transaction after

theorem prologValidReflection_iff
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand} :
    PrologValidReflection frontEnd prepareRuntime validate before requester
      transaction after ↔
      ValidReflection frontEnd prepareRuntime validate before requester
        transaction after := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologReflectionRejected {SourceImage : Type}
    (rejected : ReflectionRejected SourceImage)
    (state : ReflectiveVM SourceImage) (requester : ActorId)
    (transaction : List ReflectionCommand) (failure : ReflectionFailure) : Prop where
  | witness : rejected state requester transaction failure →
      PrologReflectionRejected rejected state requester transaction failure

theorem prologReflectionRejected_iff
    {SourceImage : Type} {rejected : ReflectionRejected SourceImage}
    {state : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand} {failure : ReflectionFailure} :
    PrologReflectionRejected rejected state requester transaction failure ↔
      rejected state requester transaction failure := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologReflectionStep {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (validate : ReflectionValidator SourceImage)
    (rejected : ReflectionRejected SourceImage) :
    ReflectiveVM SourceImage → ReflectiveVM SourceImage → Prop where
  | commit {before after requester transaction} :
      PrologValidReflection frontEnd prepareRuntime validate before requester
        transaction after →
      PrologReflectionStep frontEnd prepareRuntime validate rejected before after
  | reject {state requester transaction failure} :
      PrologReflectionRejected rejected state requester transaction failure →
      PrologReflectionStep frontEnd prepareRuntime validate rejected state state

theorem prologReflectionStep_iff
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {rejected : ReflectionRejected SourceImage}
    {before after : ReflectiveVM SourceImage} :
    PrologReflectionStep frontEnd prepareRuntime validate rejected before after ↔
      ReflectionStep frontEnd prepareRuntime validate rejected before after := by
  constructor
  · intro derivation
    cases derivation with
    | commit valid => exact .commit (prologValidReflection_iff.mp valid)
    | reject failure => exact .reject (prologReflectionRejected_iff.mp failure)
  · intro derivation
    cases derivation with
    | commit valid => exact .commit (prologValidReflection_iff.mpr valid)
    | reject failure => exact .reject (prologReflectionRejected_iff.mpr failure)

inductive PrologVMReflectionStep {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (validate : ReflectionValidator SourceImage)
    (rejected : ReflectionRejected SourceImage) :
    VMNetwork SourceImage → VMId → VMNetwork SourceImage → Prop where
  | selected {before after : VMNetwork SourceImage} {vm : VMId}
      {localBefore localAfter : ReflectiveVM SourceImage} :
      before vm = some localBefore →
      PrologReflectionStep frontEnd prepareRuntime validate rejected localBefore
        localAfter →
      after = before.install vm localAfter →
      PrologVMReflectionStep frontEnd prepareRuntime validate rejected before vm
        after

theorem prologVMReflectionStep_iff
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {rejected : ReflectionRejected SourceImage}
    {before after : VMNetwork SourceImage} {vm : VMId} :
    PrologVMReflectionStep frontEnd prepareRuntime validate rejected before vm
      after ↔
      VMReflectionStep frontEnd prepareRuntime validate rejected before vm
        after := by
  constructor
  · intro derivation
    cases derivation with
    | selected live step installed =>
        exact .selected live (prologReflectionStep_iff.mp step) installed
  · intro derivation
    cases derivation with
    | selected live step installed =>
        exact .selected live (prologReflectionStep_iff.mpr step) installed

/-! ## Mirror derivation and VM primitives -/

def allocateAuthorityMirror (state : AllocationState)
    (classId : ClassId) (authority : MirrorAuthority) :
    AllocationState × MirrorId :=
  let identity : MirrorId := ⟨state.nextMirror⟩
  ({ state with
      heap := state.heap.installMirror identity ⟨classId, .authority authority⟩
      nextMirror := state.nextMirror + 1 }, identity)

/-- Authority attenuation from Rule Mirror-Derive.  The parent mirror must be
    in the requesting actor's private heap, the target must be contained by the
    parent target, and every delegated right must already be present. -/
inductive MirrorDerivationStep :
    ActorWorld → ActorId → MirrorId → MirrorTarget → List ReflectRight →
      ActorWorld → MirrorId → Prop where
  | derive {world : ActorWorld} {actor : ActorId} {mirror : MirrorId}
      {target : MirrorTarget} {rights : List ReflectRight}
      {allocation : AllocationState} {classId : ClassId}
      {authority : MirrorAuthority} :
      world.actorAllocations actor = some allocation →
      allocation.heap.mirrors mirror =
        some ⟨classId, .authority authority⟩ →
      authority.vm = world.vm →
      .delegate ∈ authority.rights →
      MirrorTargetContained world target authority.target →
      (∀ right, right ∈ rights → right ∈ authority.rights) →
      MirrorDerivationStep world actor mirror target rights
        (world.replaceActorAllocationCoherently actor
          (allocateAuthorityMirror allocation classId
            ⟨world.vm, target, rights⟩).1)
        (allocateAuthorityMirror allocation classId
          ⟨world.vm, target, rights⟩).2

abbrev HostPrimitiveRelation :=
  ActorWorld → Selector → List ObjRef → ActorWorld → ObjRef → Prop

/-- Capability-checked application of the platform relation from VM-Primitive. -/
inductive VMPrimitiveInvocation (hostPrimitive : HostPrimitiveRelation) :
    ActorWorld → ActorId → MirrorId → Selector → List ObjRef →
      ActorWorld → ObjRef → Prop where
  | invoke {world after : ActorWorld} {actor : ActorId} {mirror : MirrorId}
      {selector : Selector} {arguments : List ObjRef} {value : ObjRef}
      {allocation : AllocationState} {classId : ClassId}
      {rights : List ReflectRight} :
      world.actorAllocations actor = some allocation →
      allocation.heap.mirrors mirror = some ⟨classId,
        .authority ⟨world.vm, .vmTarget world.vm, rights⟩⟩ →
      .primitive ∈ rights →
      hostPrimitive world selector arguments after value →
      VMPrimitiveInvocation hostPrimitive world actor mirror selector arguments
        after value

inductive PrologMirrorTargetParent (world : ActorWorld) :
    MirrorTarget → MirrorTarget → Prop where
  | cohort {target : MirrorTarget} :
      MirrorTargetOccurs world target →
      target ≠ .vmTarget world.vm →
      PrologMirrorTargetParent world target (.vmTarget world.vm)
  | mixinProgram {mixin : MixinId} :
      PrologMirrorTargetParent world (.mixinTarget mixin) .programTarget
  | methodMixin {method : MethodId} {mixin : MixinId} :
      MethodBelongsToMixin world.program method mixin →
      PrologMirrorTargetParent world (.methodTarget method) (.mixinTarget mixin)
  | classMixin {heap : Heap} {classId : ClassId} {definition : ClassDef} :
      ActorWorldHeap world heap →
      heap.classes classId = some definition →
      PrologMirrorTargetParent world (.classTarget classId)
        (.mixinTarget definition.mixin)
  | objectClass {heap : Heap} {object : ObjRef} {classId : ClassId} :
      ActorWorldHeap world heap →
      heap.classOf object = some classId →
      PrologMirrorTargetParent world (.objectTarget object) (.classTarget classId)
  | activationObject {heap : Heap} {activation : ActivationId}
      {definition : ActivationDef} :
      ActorWorldHeap world heap →
      heap.activations activation = some definition →
      PrologMirrorTargetParent world (.activationTarget activation)
        (.objectTarget definition.currentReceiver)

theorem prologMirrorTargetParent_iff {world child parent} :
    PrologMirrorTargetParent world child parent ↔
      MirrorTargetParent world child parent := by
  constructor
  · intro derivation
    cases derivation with
    | cohort occurs different => exact .cohort occurs different
    | mixinProgram => exact .mixinProgram
    | methodMixin belongs => exact .methodMixin belongs
    | classMixin participates lookup => exact .classMixin participates lookup
    | objectClass participates lookup => exact .objectClass participates lookup
    | activationObject participates lookup =>
        exact .activationObject participates lookup
  · intro derivation
    cases derivation with
    | cohort occurs different => exact .cohort occurs different
    | mixinProgram => exact .mixinProgram
    | methodMixin belongs => exact .methodMixin belongs
    | classMixin participates lookup => exact .classMixin participates lookup
    | objectClass participates lookup => exact .objectClass participates lookup
    | activationObject participates lookup =>
        exact .activationObject participates lookup

inductive PrologMirrorTargetContained (world : ActorWorld) :
    MirrorTarget → MirrorTarget → Prop where
  | refl (target : MirrorTarget) :
      PrologMirrorTargetContained world target target
  | parent {child parent ancestor : MirrorTarget} :
      PrologMirrorTargetParent world child parent →
      PrologMirrorTargetContained world parent ancestor →
      PrologMirrorTargetContained world child ancestor

theorem prologMirrorTargetContained_iff {world target ancestor} :
    PrologMirrorTargetContained world target ancestor ↔
      MirrorTargetContained world target ancestor := by
  constructor
  · intro derivation
    induction derivation with
    | refl target => exact .refl target
    | parent edge _ ih => exact .parent (prologMirrorTargetParent_iff.mp edge) ih
  · intro derivation
    induction derivation with
    | refl target => exact .refl target
    | parent edge _ ih => exact .parent (prologMirrorTargetParent_iff.mpr edge) ih

inductive PrologMirrorDerivationStep :
    ActorWorld → ActorId → MirrorId → MirrorTarget → List ReflectRight →
      ActorWorld → MirrorId → Prop where
  | derive {world : ActorWorld} {actor : ActorId} {mirror : MirrorId}
      {target : MirrorTarget} {rights : List ReflectRight}
      {allocation : AllocationState} {classId : ClassId}
      {authority : MirrorAuthority} :
      world.actorAllocations actor = some allocation →
      allocation.heap.mirrors mirror = some ⟨classId, .authority authority⟩ →
      authority.vm = world.vm →
      .delegate ∈ authority.rights →
      PrologMirrorTargetContained world target authority.target →
      (∀ right, right ∈ rights → right ∈ authority.rights) →
      PrologMirrorDerivationStep world actor mirror target rights
        (world.replaceActorAllocationCoherently actor
          (allocateAuthorityMirror allocation classId
            ⟨world.vm, target, rights⟩).1)
        (allocateAuthorityMirror allocation classId
          ⟨world.vm, target, rights⟩).2

theorem prologMirrorDerivationStep_iff
    {world after : ActorWorld} {actor : ActorId} {mirror result : MirrorId}
    {target : MirrorTarget} {rights : List ReflectRight} :
    PrologMirrorDerivationStep world actor mirror target rights after result ↔
      MirrorDerivationStep world actor mirror target rights after result := by
  constructor
  · intro derivation
    cases derivation with
    | derive allocation mirrorDefinition vm delegate contained subset =>
        exact .derive allocation mirrorDefinition vm delegate
          (prologMirrorTargetContained_iff.mp contained) subset
  · intro derivation
    cases derivation with
    | derive allocation mirrorDefinition vm delegate contained subset =>
        exact .derive allocation mirrorDefinition vm delegate
          (prologMirrorTargetContained_iff.mpr contained) subset

inductive PrologHostPrimitiveApplication
    (hostPrimitive : HostPrimitiveRelation) (world : ActorWorld)
    (selector : Selector) (arguments : List ObjRef) :
    ActorWorld → ObjRef → Prop where
  | witness {after : ActorWorld} {value : ObjRef} :
      hostPrimitive world selector arguments after value →
      PrologHostPrimitiveApplication hostPrimitive world selector arguments
        after value

inductive PrologVMPrimitiveInvocation (hostPrimitive : HostPrimitiveRelation) :
    ActorWorld → ActorId → MirrorId → Selector → List ObjRef →
      ActorWorld → ObjRef → Prop where
  | invoke {world after : ActorWorld} {actor : ActorId} {mirror : MirrorId}
      {selector : Selector} {arguments : List ObjRef} {value : ObjRef}
      {allocation : AllocationState} {classId : ClassId}
      {rights : List ReflectRight} :
      world.actorAllocations actor = some allocation →
      allocation.heap.mirrors mirror = some ⟨classId,
        .authority ⟨world.vm, .vmTarget world.vm, rights⟩⟩ →
      .primitive ∈ rights →
      PrologHostPrimitiveApplication hostPrimitive world selector arguments
        after value →
      PrologVMPrimitiveInvocation hostPrimitive world actor mirror selector
        arguments after value

theorem prologVMPrimitiveInvocation_iff
    {hostPrimitive : HostPrimitiveRelation} {world after : ActorWorld}
    {actor : ActorId} {mirror : MirrorId} {selector : Selector}
    {arguments : List ObjRef} {value : ObjRef} :
    PrologVMPrimitiveInvocation hostPrimitive world actor mirror selector
      arguments after value ↔
      VMPrimitiveInvocation hostPrimitive world actor mirror selector arguments
        after value := by
  constructor
  · intro derivation
    cases derivation with
    | invoke allocation mirrorDefinition primitive host =>
        cases host with
        | witness application =>
            exact .invoke allocation mirrorDefinition primitive application
  · intro derivation
    cases derivation with
    | invoke allocation mirrorDefinition primitive application =>
        exact .invoke allocation mirrorDefinition primitive (.witness application)

end PrologBridge
end Newspeak
