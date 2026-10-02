import Newspeak.ReflectionRuntimePreparation

namespace Newspeak

def ActorWorld.AllHeapsSatisfy (world : ActorWorld) (property : Heap → Prop) : Prop :=
  ∀ heap, ActorWorldHeap world heap → property heap

def ReflectionClassGraphsOK (world : ActorWorld) : Prop :=
  world.AllHeapsSatisfy fun heap => world.program.LookupWellFormed heap

def Heap.ReflectionObjectLayoutsOK (program : Program) (heap : Heap) : Prop :=
  ∀ object definition, heap.objects object = some definition →
    ∃ layout,
      program.instanceLayout? heap definition.classId = some layout ∧
      definition.slots.domain = FiniteStore.deduplicated layout

def Heap.ReflectionNestedCachesOK (program : Program) (heap : Heap) : Prop :=
  ∀ object definition, heap.objects object = some definition →
    ∃ keys,
      program.nestedKeys? heap definition.classId = some keys ∧
      ∀ key, key ∈ definition.nestedClasses.domain → key ∈ keys

def ReflectionObjectStoresOK (world : ActorWorld) : Prop :=
  world.AllHeapsSatisfy fun heap =>
    world.program.WellFormed heap ∧
    heap.ReflectionObjectLayoutsOK world.program ∧
    heap.ReflectionNestedCachesOK world.program

def ActorWorld.RunStateAllocationCoherent (world : ActorWorld) : Prop :=
  world.runStates.domain = world.actorAllocations.domain ∧
    ∀ actor allocation, world.actorAllocations actor = some allocation →
      match world.runStates actor with
      | some .idle => True
      | some (.runningTurn config _ _) =>
          config.allocation = allocation ∧
          world.program.SequentialWellFormed config
      | some (.pausedTurn config _ _ _ _) =>
          config.allocation = allocation ∧
          world.program.SequentialWellFormed config
      | none => False

theorem ActorWorld.RunStateAllocationCoherent.allocation_present_of_runState
    {world : ActorWorld} (coherent : world.RunStateAllocationCoherent)
    {actor : ActorId} {state : ActorRunState}
    (present : world.runStates actor = some state) :
    ∃ allocation, world.actorAllocations actor = some allocation := by
  have runMember := world.runStates.mem_domain_of_lookup_eq_some present
  have allocationMember : actor ∈ world.actorAllocations.domain := by
    rw [← coherent.1]
    exact runMember
  exact world.actorAllocations.exists_value_of_mem_domain allocationMember

def ReflectionLiveActivationsOK (world : ActorWorld) : Prop :=
  world.RunStateAllocationCoherent

def Heap.ContinuationPrecedes (heap : Heap)
    (child parent : ActivationId) : Prop :=
  ∃ definition,
    heap.activations child = some definition ∧
    definition.continuation = some parent

def Heap.ActivationContinuationsOK (heap : Heap) : Prop :=
  (∀ child definition parent,
      heap.activations child = some definition →
      definition.continuation = some parent →
      ∃ parentDefinition, heap.activations parent = some parentDefinition) ∧
    WellFounded heap.ContinuationPrecedes

def Heap.ActivationCurrentClassesAdmissible (program : Program)
    (heap : Heap) : Prop :=
  ∀ activation definition currentClass,
    heap.activations activation = some definition →
    definition.currentClass = some currentClass →
    ∃ receiverClass chain,
      heap.classOf definition.currentReceiver = some receiverClass ∧
      program.ClassChain heap receiverClass chain ∧
      currentClass ∈ chain

def ReflectionActivationEditsOK (world : ActorWorld) : Prop :=
  world.AllHeapsSatisfy fun heap =>
    heap.ActivationContinuationsOK ∧
    heap.ActivationCurrentClassesAdmissible world.program

def ReflectionActorIsolationOK (world : ActorWorld) : Prop :=
  world.PrivateHeapsDisjoint ∧ world.ValueHeapDisjoint

def concreteReflectionValidator {SourceImage : Type} :
    ReflectionValidator SourceImage :=
  fun _before _transaction after =>
    { classGraphCheck := ReflectionClassGraphsOK after.world
      objectStoreCheck := ReflectionObjectStoresOK after.world
      liveActivationCheck := ReflectionLiveActivationsOK after.world
      activationEditCheck := ReflectionActivationEditsOK after.world
      actorIsolationCheck := ReflectionActorIsolationOK after.world }

structure ReflectionCohortWellFormed (world : ActorWorld) : Prop where
  classGraphs : ReflectionClassGraphsOK world
  objectStores : ReflectionObjectStoresOK world
  liveActivations : ReflectionLiveActivationsOK world
  activationEdits : ReflectionActivationEditsOK world
  actorIsolation : ReflectionActorIsolationOK world

theorem ValidReflection.preserves_reflectionCohortWellFormed
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand}
    (valid : ValidReflection frontEnd prepareReflectionRuntime
      concreteReflectionValidator before requester transaction after) :
    ReflectionCohortWellFormed after.world := by
  rcases valid.2.2.2 with ⟨classGraph, objectStore, liveActivation,
    activationEdit, actorIsolation⟩
  exact ⟨classGraph, objectStore, liveActivation, activationEdit,
    actorIsolation⟩

end Newspeak
