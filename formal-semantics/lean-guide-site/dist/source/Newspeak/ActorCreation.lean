import Newspeak.ActorExecution

namespace Newspeak

/-- Platform construction of a fresh actor's distinguished base heap and
    allocation frontiers. -/
abbrev ActorBaseAllocation :=
  ActorWorld → ActorId → AllocationState → Prop

def ActorBaseAllocationDeterministic (base : ActorBaseAllocation) : Prop :=
  ∀ world actor first second,
    base world actor first → base world actor second → first = second

def actorSeedFactory (seed : ActorSeedDescriptor) : FactoryDef :=
  { activationDeclaration := seed.initializerDeclaration
    selector := seed.factorySelector
    parameters := seed.factoryParameters
    plan := .body seed.superclassMessage }

structure ActorSpawnResult where
  world : ActorWorld
  actor : ActorId
  actorClass : ClassId
  reference : FarRefId

namespace ActorWorld

def installFreshActor (world : ActorWorld) (actor : ActorId)
    (allocation : AllocationState) : ActorWorld :=
  { world with
    actorAllocations := world.actorAllocations.install actor allocation
    runStates := world.runStates.install actor .idle
    mailboxes := world.mailboxes.install actor []
    histories := world.histories.install actor []
    deliveredEvents := world.deliveredEvents.install actor []
    nextActor := world.nextActor + 1 }

def spawnActorFromSeed (world : ActorWorld) (instanceMixin : MixinId)
    (seed : ActorSeedDescriptor) (base : AllocationState) : ActorSpawnResult :=
  let actor : ActorId := ⟨world.nextActor⟩
  let allocation := world.program.allocateClassPair base
    (.actor (.namedClass seed.declaration)) instanceMixin seed.classMixin
    world.program.object world.program.nilObject (actorSeedFactory seed)
  let installed := world.installFreshActor actor allocation.1
  let far := installed.installNextFarReference actor (.classObject allocation.2.1)
  ⟨far.1, actor, allocation.2.1, far.2⟩

@[simp] theorem spawnActorFromSeed_actor (world : ActorWorld)
    (instanceMixin : MixinId) (seed : ActorSeedDescriptor)
    (base : AllocationState) :
    (world.spawnActorFromSeed instanceMixin seed base).actor =
      ⟨world.nextActor⟩ := by
  rfl

@[simp] theorem spawnActorFromSeed_reference (world : ActorWorld)
    (instanceMixin : MixinId) (seed : ActorSeedDescriptor)
    (base : AllocationState) :
    (world.spawnActorFromSeed instanceMixin seed base).reference =
      ⟨world.nextFarReference⟩ := by
  rfl

@[simp] theorem spawnActorFromSeed_runState (world : ActorWorld)
    (instanceMixin : MixinId) (seed : ActorSeedDescriptor)
    (base : AllocationState) :
    (world.spawnActorFromSeed instanceMixin seed base).world.runStates
      (world.spawnActorFromSeed instanceMixin seed base).actor = some .idle := by
  simp [spawnActorFromSeed, installFreshActor,
    ActorWorld.installNextFarReference]

@[simp] theorem spawnActorFromSeed_farTarget (world : ActorWorld)
    (instanceMixin : MixinId) (seed : ActorSeedDescriptor)
    (base : AllocationState) :
    (world.spawnActorFromSeed instanceMixin seed base).world.farReferences
      (world.spawnActorFromSeed instanceMixin seed base).reference =
      some ⟨(world.spawnActorFromSeed instanceMixin seed base).actor,
        .classObject
          (world.spawnActorFromSeed instanceMixin seed base).actorClass⟩ := by
  simp [spawnActorFromSeed, installFreshActor,
    ActorWorld.installNextFarReference]

end ActorWorld

/-- The actor-creation primitive.  Static seed validity is stated explicitly:
    its key is the declaration's instance mixin and its declaration is
    top-level. -/
inductive ActorSpawn (baseAllocation : ActorBaseAllocation) :
    ActorWorld → MixinId → ActorSpawnResult → Prop where
  | spawn {world : ActorWorld} {instanceMixin : MixinId}
      {seed : ActorSeedDescriptor} {base : AllocationState} :
      world.program.actorSeeds instanceMixin = some seed →
      world.program.declMixin (.namedClass seed.declaration) =
        some instanceMixin →
      world.program.classOwner seed.declaration = .topOwner →
      baseAllocation world ⟨world.nextActor⟩ base →
      ActorSpawn baseAllocation world instanceMixin
        (world.spawnActorFromSeed instanceMixin seed base)

theorem ActorSpawn.deterministic
    {baseAllocation : ActorBaseAllocation}
    (baseDeterministic : ActorBaseAllocationDeterministic baseAllocation)
    {world : ActorWorld} {instanceMixin : MixinId}
    {first second : ActorSpawnResult}
    (left : ActorSpawn baseAllocation world instanceMixin first)
    (right : ActorSpawn baseAllocation world instanceMixin second) :
    first = second := by
  cases left with
  | @spawn seed₁ base₁ found₁ decl₁ top₁ platform₁ =>
      cases right with
      | @spawn seed₂ base₂ found₂ decl₂ top₂ platform₂ =>
          have seedEqual := Option.some.inj (found₁.symm.trans found₂)
          subst seed₂
          have baseEqual := baseDeterministic world ⟨world.nextActor⟩
            base₁ base₂ platform₁ platform₂
          subst base₂
          rfl

end Newspeak
