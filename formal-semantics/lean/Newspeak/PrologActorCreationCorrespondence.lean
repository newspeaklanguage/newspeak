import Newspeak.ActorCreation
import Newspeak.PrologLookupCorrespondence

/-! # Correspondence for the event ledger and actor creation -/

namespace Newspeak
namespace PrologBridge

inductive PrologActorEventRecord (world : ActorWorld) (event : EventId) :
    Option EventRecord → Prop where
  | record : PrologActorEventRecord world event (world.eventLedger event)

theorem prologActorEventRecord_iff {world : ActorWorld} {event : EventId}
    {result : Option EventRecord} :
    PrologActorEventRecord world event result ↔
      world.eventLedger event = result := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .record

inductive PrologActorEventDestination (world : ActorWorld)
    (event : EventId) : ActorId → Prop where
  | destination {record : EventRecord} :
      PrologActorEventRecord world event (some record) →
      PrologActorEventDestination world event record.destination

theorem prologActorEventDestination_iff {world : ActorWorld}
    {event : EventId} {destination : ActorId} :
    PrologActorEventDestination world event destination ↔
      ∃ record, world.eventLedger event = some record ∧
        record.destination = destination := by
  constructor
  · intro derivation
    cases derivation with
    | destination recordProof =>
        exact ⟨_, prologActorEventRecord_iff.mp recordProof, rfl⟩
  · rintro ⟨record, present, rfl⟩
    exact .destination (prologActorEventRecord_iff.mpr present)

inductive PrologActorDeliveredSequence (world : ActorWorld)
    (actor : ActorId) : List EventId → Prop where
  | delivered :
      PrologActorDeliveredSequence world actor (world.deliveredTo actor)

theorem prologActorDeliveredSequence_iff {world : ActorWorld}
    {actor : ActorId} {events : List EventId} :
    PrologActorDeliveredSequence world actor events ↔
      world.deliveredTo actor = events := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .delivered

inductive PrologActorBaseAllocation (baseAllocation : ActorBaseAllocation)
    (world : ActorWorld) (actor : ActorId) : AllocationState → Prop where
  | witness {base : AllocationState} :
      baseAllocation world actor base →
      PrologActorBaseAllocation baseAllocation world actor base

theorem prologActorBaseAllocation_iff
    {baseAllocation : ActorBaseAllocation} {world : ActorWorld}
    {actor : ActorId} {base : AllocationState} :
    PrologActorBaseAllocation baseAllocation world actor base ↔
      baseAllocation world actor base := by
  constructor
  · intro derivation
    cases derivation with | witness premise => exact premise
  · exact .witness

inductive PrologActorSpawn (baseAllocation : ActorBaseAllocation) :
    ActorWorld → MixinId → ActorSpawnResult → Prop where
  | spawn {world : ActorWorld} {instanceMixin : MixinId}
      {seed : ActorSeedDescriptor} {base : AllocationState} :
      world.program.actorSeeds instanceMixin = some seed →
      world.program.declMixin (.namedClass seed.declaration) =
        some instanceMixin →
      world.program.classOwner seed.declaration = .topOwner →
      PrologActorBaseAllocation baseAllocation world
        ⟨world.nextActor⟩ base →
      PrologActorSpawn baseAllocation world instanceMixin
        (world.spawnActorFromSeed instanceMixin seed base)

theorem prologActorSpawn_iff {baseAllocation : ActorBaseAllocation}
    {world : ActorWorld} {instanceMixin : MixinId}
    {result : ActorSpawnResult} :
    PrologActorSpawn baseAllocation world instanceMixin result ↔
      ActorSpawn baseAllocation world instanceMixin result := by
  constructor
  · intro derivation
    cases derivation with
    | spawn seed decl owner base =>
        exact .spawn seed decl owner (prologActorBaseAllocation_iff.mp base)
  · intro derivation
    cases derivation with
    | spawn seed decl owner base =>
        exact .spawn seed decl owner (prologActorBaseAllocation_iff.mpr base)

end PrologBridge
end Newspeak
