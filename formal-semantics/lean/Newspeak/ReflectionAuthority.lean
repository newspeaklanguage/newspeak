import Newspeak.ActorCreation

namespace Newspeak

/-- One heap participating in a VM cohort: the shared value heap or an
    actor-private heap. -/
inductive ActorWorldHeap (world : ActorWorld) : Heap → Prop where
  | shared : ActorWorldHeap world world.valueHeap
  | privateHeap {actor : ActorId} {allocation : AllocationState} :
      world.actorAllocations actor = some allocation →
      ActorWorldHeap world allocation.heap

/-- Exact owner classification used by reflective isolation checks. -/
inductive ObjectOwner (world : ActorWorld) : ObjRef → HeapLocation → Prop where
  | shared {object : ObjRef} :
      world.valueHeap.IsLiveObject object →
      ObjectOwner world object .shared
  | actor {actor : ActorId} {allocation : AllocationState} {object : ObjRef} :
      world.actorAllocations actor = some allocation →
      allocation.heap.IsLiveObject object →
      ObjectOwner world object (.actor actor)

theorem ObjectOwner.unique
    {world : ActorWorld} (privateDisjoint : world.PrivateHeapsDisjoint)
    (valueDisjoint : world.ValueHeapDisjoint)
    {object : ObjRef} {first second : HeapLocation}
    (left : ObjectOwner world object first)
    (right : ObjectOwner world object second) : first = second := by
  cases left with
  | shared live₁ =>
      cases right with
      | shared live₂ => rfl
      | actor allocation live₂ =>
          exact False.elim (valueDisjoint _ _ allocation _ live₁ live₂)
  | @actor actor₁ allocation₁ _ lookup₁ live₁ =>
      cases right with
      | shared live₂ =>
          exact False.elim (valueDisjoint actor₁ allocation₁ lookup₁ _ live₂ live₁)
      | @actor actor₂ allocation₂ _ lookup₂ live₂ =>
          by_cases same : actor₁ = actor₂
          · subst actor₂
            rfl
          · exact False.elim
              (privateDisjoint actor₁ actor₂ allocation₁ allocation₂
                lookup₁ lookup₂ same _ live₁ live₂)

theorem ObjectOwner.existsUnique_of_worldHeap
    {world : ActorWorld} (privateDisjoint : world.PrivateHeapsDisjoint)
    (valueDisjoint : world.ValueHeapDisjoint)
    {heap : Heap} (participates : ActorWorldHeap world heap)
    {object : ObjRef} (live : heap.IsLiveObject object) :
    ∃ location, ObjectOwner world object location ∧
      ∀ other, ObjectOwner world object other → other = location := by
  cases participates with
  | shared =>
      refine ⟨.shared, .shared live, ?_⟩
      intro location owner
      exact (ObjectOwner.unique privateDisjoint valueDisjoint owner
        (.shared live))
  | @privateHeap actor allocation lookup =>
      refine ⟨.actor actor, .actor lookup live, ?_⟩
      intro location owner
      exact (ObjectOwner.unique privateDisjoint valueDisjoint owner
        (.actor lookup live))

theorem ObjectOwner.privateHeap_owned_exactly_by_actor
    {world : ActorWorld} (privateDisjoint : world.PrivateHeapsDisjoint)
    (valueDisjoint : world.ValueHeapDisjoint)
    {actor : ActorId} {allocation : AllocationState}
    (allocationPresent : world.actorAllocations actor = some allocation)
    {object : ObjRef} (live : allocation.heap.IsLiveObject object) :
    ObjectOwner world object (.actor actor) ∧
      ∀ location, ObjectOwner world object location → location = .actor actor := by
  constructor
  · exact .actor allocationPresent live
  · intro location owner
    exact ObjectOwner.unique privateDisjoint valueDisjoint owner
      (.actor allocationPresent live)

theorem ObjectOwner.activation_owned_exactly_by_actor
    {world : ActorWorld} (privateDisjoint : world.PrivateHeapsDisjoint)
    (valueDisjoint : world.ValueHeapDisjoint)
    {actor : ActorId} {allocation : AllocationState}
    (allocationPresent : world.actorAllocations actor = some allocation)
    {activation : ActivationId} {definition : ActivationDef}
    (activationPresent : allocation.heap.activations activation =
      some definition) :
    ObjectOwner world (.activationObject activation) (.actor actor) ∧
      ∀ location,
        ObjectOwner world (.activationObject activation) location →
          location = .actor actor := by
  apply ObjectOwner.privateHeap_owned_exactly_by_actor privateDisjoint
    valueDisjoint allocationPresent
  exact ⟨definition.objectClass, by
    simp [Heap.classOf, activationPresent]⟩

/-- Direct finite-table characterization of method ownership. -/
def MethodBelongsToMixin (program : Program) (method : MethodId)
    (mixin : MixinId) : Prop :=
  ∃ definition selector methodDef,
    program.mixins mixin = some definition ∧
    definition.methods selector = some methodDef ∧
    methodDef.identity = method

def MirrorTargetOccurs (world : ActorWorld) : MirrorTarget → Prop
  | .vmTarget vm => vm = world.vm
  | .programTarget => True
  | .mixinTarget mixin => ∃ definition, world.program.mixins mixin = some definition
  | .methodTarget method => ∃ mixin, MethodBelongsToMixin world.program method mixin
  | .classTarget classId =>
      ∃ heap, ActorWorldHeap world heap ∧ ∃ definition, heap.classes classId = some definition
  | .objectTarget object => ∃ location, ObjectOwner world object location
  | .activationTarget activation =>
      ∃ heap, ActorWorldHeap world heap ∧
        ∃ definition, heap.activations activation = some definition
  | .actorTarget actor => ∃ allocation, world.actorAllocations actor = some allocation

/-- One immediate edge of Equation mirror-target-containment. -/
inductive MirrorTargetParent (world : ActorWorld) :
    MirrorTarget → MirrorTarget → Prop where
  | cohort {target : MirrorTarget} :
      MirrorTargetOccurs world target →
      target ≠ .vmTarget world.vm →
      MirrorTargetParent world target (.vmTarget world.vm)
  | mixinProgram {mixin : MixinId} :
      MirrorTargetParent world (.mixinTarget mixin) .programTarget
  | methodMixin {method : MethodId} {mixin : MixinId} :
      MethodBelongsToMixin world.program method mixin →
      MirrorTargetParent world (.methodTarget method) (.mixinTarget mixin)
  | classMixin {heap : Heap} {classId : ClassId} {definition : ClassDef} :
      ActorWorldHeap world heap →
      heap.classes classId = some definition →
      MirrorTargetParent world (.classTarget classId)
        (.mixinTarget definition.mixin)
  | objectClass {heap : Heap} {object : ObjRef} {classId : ClassId} :
      ActorWorldHeap world heap →
      heap.classOf object = some classId →
      MirrorTargetParent world (.objectTarget object) (.classTarget classId)
  | activationObject {heap : Heap} {activation : ActivationId}
      {definition : ActivationDef} :
      ActorWorldHeap world heap →
      heap.activations activation = some definition →
      MirrorTargetParent world (.activationTarget activation)
        (.objectTarget definition.currentReceiver)

/-- Least reflexive/transitive containment generated by immediate target
    parents. -/
inductive MirrorTargetContained (world : ActorWorld) :
    MirrorTarget → MirrorTarget → Prop where
  | refl (target : MirrorTarget) : MirrorTargetContained world target target
  | parent {child parent ancestor : MirrorTarget} :
      MirrorTargetParent world child parent →
      MirrorTargetContained world parent ancestor →
      MirrorTargetContained world child ancestor

/-- Lookup of an authority-bearing mirror in the requesting actor's private
    heap. -/
def ActorWorld.mirrorAuthority (world : ActorWorld) (actor : ActorId)
    (mirror : MirrorId) : Option MirrorAuthority := do
  let allocation ← world.actorAllocations actor
  let definition ← allocation.heap.mirrors mirror
  match definition.payload with
  | .authority authority => some authority
  | .message _ | .opaque => none

def MirrorAuthorizes (world : ActorWorld) (actor : ActorId)
    (mirror : MirrorId) (target : MirrorTarget) (right : ReflectRight) : Prop :=
  ∃ authority,
    world.mirrorAuthority actor mirror = some authority ∧
    authority.vm = world.vm ∧
    right ∈ authority.rights ∧
    MirrorTargetContained world target authority.target

end Newspeak
