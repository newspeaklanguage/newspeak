import Newspeak.ReflectionQueries

/-! # Prolog correspondence for reflective population queries -/

namespace Newspeak
namespace PrologBridge

inductive PrologHeapAllInstances (heap : Heap) (classId : ClassId) :
    List ObjRef → Prop where
  | application : PrologHeapAllInstances heap classId
      (heap.allInstancesOf classId)

inductive PrologActorInstancesOf (world : ActorWorld) (classId : ClassId) :
    List ActorId → List ObjRef → Prop where
  | empty : PrologActorInstancesOf world classId [] []
  | absent {actor remaining values} :
      world.actorAllocations actor = none →
      PrologActorInstancesOf world classId remaining values →
      PrologActorInstancesOf world classId (actor :: remaining) values
  | present {actor remaining allocation current later} :
      world.actorAllocations actor = some allocation →
      PrologHeapAllInstances allocation.heap classId current →
      PrologActorInstancesOf world classId remaining later →
      PrologActorInstancesOf world classId (actor :: remaining)
        (current ++ later)

theorem prologActorInstancesOf_iff {world : ActorWorld} {classId : ClassId}
    {actors : List ActorId} {values : List ObjRef} :
    PrologActorInstancesOf world classId actors values ↔
      world.actorInstancesOf classId actors = values := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | absent lookup _ ih => simp [ActorWorld.actorInstancesOf, lookup, ih]
    | present lookup current _ ih =>
        cases current
        simp [ActorWorld.actorInstancesOf, lookup, ih]
  · intro equality
    induction actors generalizing values with
    | nil =>
        simp [ActorWorld.actorInstancesOf] at equality
        subst values
        exact .empty
    | cons actor remaining ih =>
        cases lookup : world.actorAllocations actor with
        | none =>
            simp [ActorWorld.actorInstancesOf, lookup] at equality
            exact .absent lookup (ih equality)
        | some allocation =>
            simp [ActorWorld.actorInstancesOf, lookup] at equality
            subst values
            exact .present lookup .application (ih rfl)

inductive PrologAllCohortInstancesOf (world : ActorWorld)
    (classId : ClassId) : List ObjRef → Prop where
  | enumerate {shared actors result} :
      PrologHeapAllInstances world.valueHeap classId shared →
      PrologActorInstancesOf world classId world.actorAllocations.domain actors →
      result = shared ++ actors →
      PrologAllCohortInstancesOf world classId result

theorem prologAllCohortInstancesOf_iff {world : ActorWorld}
    {classId : ClassId} {values : List ObjRef} :
    PrologAllCohortInstancesOf world classId values ↔
      world.allCohortInstancesOf classId = values := by
  constructor
  · rintro ⟨shared, actors, rfl⟩
    cases shared
    simp [ActorWorld.allCohortInstancesOf,
      prologActorInstancesOf_iff.mp actors]
  · intro equality
    exact .enumerate .application
      (prologActorInstancesOf_iff.mpr rfl) equality.symm

inductive PrologHeapAllApplications (heap : Heap) (mixin : MixinId) :
    List ClassId → Prop where
  | application : PrologHeapAllApplications heap mixin
      (heap.allApplicationsOf mixin)

inductive PrologLocateClasses (location : HeapLocation) :
    List ClassId → List LocatedClass → Prop where
  | empty : PrologLocateClasses location [] []
  | step {classId remaining located} :
      PrologLocateClasses location remaining located →
      PrologLocateClasses location (classId :: remaining)
        (⟨location, classId⟩ :: located)

theorem prologLocateClasses_iff {location : HeapLocation}
    {classes : List ClassId} {located : List LocatedClass} :
    PrologLocateClasses location classes located ↔
      classes.map (LocatedClass.mk location) = located := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | step _ ih => simp [ih]
  · intro equality
    subst located
    induction classes with
    | nil => exact .empty
    | cons classId remaining ih => exact .step ih

inductive PrologActorApplicationsOf (world : ActorWorld) (mixin : MixinId) :
    List ActorId → List LocatedClass → Prop where
  | empty : PrologActorApplicationsOf world mixin [] []
  | absent {actor remaining values} :
      world.actorAllocations actor = none →
      PrologActorApplicationsOf world mixin remaining values →
      PrologActorApplicationsOf world mixin (actor :: remaining) values
  | present {actor remaining allocation classes current later} :
      world.actorAllocations actor = some allocation →
      PrologHeapAllApplications allocation.heap mixin classes →
      PrologLocateClasses (.actor actor) classes current →
      PrologActorApplicationsOf world mixin remaining later →
      PrologActorApplicationsOf world mixin (actor :: remaining)
        (current ++ later)

theorem prologActorApplicationsOf_iff {world : ActorWorld} {mixin : MixinId}
    {actors : List ActorId} {values : List LocatedClass} :
    PrologActorApplicationsOf world mixin actors values ↔
      world.actorApplicationsOf mixin actors = values := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | absent lookup _ ih => simp [ActorWorld.actorApplicationsOf, lookup, ih]
    | present lookup classes located _ ih =>
        cases classes
        simp [ActorWorld.actorApplicationsOf, lookup,
          prologLocateClasses_iff.mp located, ih]
  · intro equality
    induction actors generalizing values with
    | nil =>
        simp [ActorWorld.actorApplicationsOf] at equality
        subst values
        exact .empty
    | cons actor remaining ih =>
        cases lookup : world.actorAllocations actor with
        | none =>
            simp [ActorWorld.actorApplicationsOf, lookup] at equality
            exact .absent lookup (ih equality)
        | some allocation =>
            simp [ActorWorld.actorApplicationsOf, lookup] at equality
            subst values
            exact .present lookup .application
              (prologLocateClasses_iff.mpr rfl) (ih rfl)

inductive PrologAllCohortApplicationsOf (world : ActorWorld)
    (mixin : MixinId) : List LocatedClass → Prop where
  | enumerate {classes shared actors result} :
      PrologHeapAllApplications world.valueHeap mixin classes →
      PrologLocateClasses .shared classes shared →
      PrologActorApplicationsOf world mixin world.actorAllocations.domain actors →
      result = shared ++ actors →
      PrologAllCohortApplicationsOf world mixin result

theorem prologAllCohortApplicationsOf_iff {world : ActorWorld}
    {mixin : MixinId} {values : List LocatedClass} :
    PrologAllCohortApplicationsOf world mixin values ↔
      world.allCohortApplicationsOf mixin = values := by
  constructor
  · rintro ⟨classes, shared, actors, rfl⟩
    cases classes
    simp [ActorWorld.allCohortApplicationsOf,
      prologLocateClasses_iff.mp shared,
      prologActorApplicationsOf_iff.mp actors]
  · intro equality
    exact .enumerate .application (prologLocateClasses_iff.mpr rfl)
      (prologActorApplicationsOf_iff.mpr rfl) equality.symm

end PrologBridge
end Newspeak
