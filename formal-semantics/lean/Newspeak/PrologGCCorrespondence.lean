import Newspeak.PrologReflectionCorrespondence

/-!
# Correspondence with the optional global GC wrapper

The wrapper is parameterized by the already-defined VM transition, the exact
new-identity projection, admissibility, and atomic pruning.  This matches the
role of Rules GC-Lift and GC-Collect: they constrain composition and global
identity reuse without choosing a collector or scheduler.
-/

namespace Newspeak

structure GCWrappedWorld where
  world : ActorWorld
  allocatedReferences : List ObjRef

def GCNewReferencesFresh (newReferences allocated : List ObjRef) : Prop :=
  ∀ reference, reference ∈ newReferences → reference ∉ allocated

def extendAllocatedReferences (allocated newReferences : List ObjRef) :
    List ObjRef :=
  FiniteStore.deduplicated (allocated ++ newReferences)

abbrev GCUnderlyingTransition (Label : Type) :=
  Label → ActorWorld → ActorWorld → Prop

inductive GCLiftStep {Label : Type}
    (underlying : GCUnderlyingTransition Label)
    (newReferences : ActorWorld → ActorWorld → List ObjRef) :
    Label → GCWrappedWorld → GCWrappedWorld → Prop where
  | lift {label : Label} {beforeWorld afterWorld : ActorWorld}
      {allocated : List ObjRef} :
      underlying label beforeWorld afterWorld →
      GCNewReferencesFresh (newReferences beforeWorld afterWorld) allocated →
      GCLiftStep underlying newReferences label
        ⟨beforeWorld, allocated⟩
        ⟨afterWorld, extendAllocatedReferences allocated
          (newReferences beforeWorld afterWorld)⟩

abbrev GCAdmissibility (RootHandle : Type) :=
  ActorWorld → List RootHandle → List ObjRef → Prop

abbrev GCPruning := ActorWorld → List ObjRef → ActorWorld

inductive GCCollectStep {RootHandle : Type}
    (admissible : GCAdmissibility RootHandle) (prune : GCPruning)
    (roots : List RootHandle) : GCWrappedWorld → GCWrappedWorld → Prop where
  | collect {world : ActorWorld} {allocated garbage : List ObjRef} :
      admissible world roots garbage →
      GCCollectStep admissible prune roots ⟨world, allocated⟩
        ⟨prune world garbage, allocated⟩

namespace PrologBridge

inductive PrologGCUnderlyingApplication {Label : Type}
    (underlying : GCUnderlyingTransition Label) (label : Label)
    (before : ActorWorld) : ActorWorld → Prop where
  | witness {after : ActorWorld} : underlying label before after →
      PrologGCUnderlyingApplication underlying label before after

inductive PrologGCNewReferencesFresh (newReferences allocated : List ObjRef) :
    Prop where
  | witness : GCNewReferencesFresh newReferences allocated →
      PrologGCNewReferencesFresh newReferences allocated

inductive PrologGCLiftStep {Label : Type}
    (underlying : GCUnderlyingTransition Label)
    (newReferences : ActorWorld → ActorWorld → List ObjRef) :
    Label → GCWrappedWorld → GCWrappedWorld → Prop where
  | lift {label : Label} {beforeWorld afterWorld : ActorWorld}
      {allocated : List ObjRef} :
      PrologGCUnderlyingApplication underlying label beforeWorld afterWorld →
      PrologGCNewReferencesFresh (newReferences beforeWorld afterWorld)
        allocated →
      PrologGCLiftStep underlying newReferences label
        ⟨beforeWorld, allocated⟩
        ⟨afterWorld, extendAllocatedReferences allocated
          (newReferences beforeWorld afterWorld)⟩

theorem prologGCLiftStep_iff
    {Label : Type} {underlying : GCUnderlyingTransition Label}
    {newReferences : ActorWorld → ActorWorld → List ObjRef}
    {label : Label} {before after : GCWrappedWorld} :
    PrologGCLiftStep underlying newReferences label before after ↔
      GCLiftStep underlying newReferences label before after := by
  constructor
  · intro derivation
    cases derivation with
    | lift transition fresh =>
        cases transition with
        | witness transition =>
            cases fresh with
            | witness fresh => exact .lift transition fresh
  · intro derivation
    cases derivation with
    | lift transition fresh =>
        exact .lift (.witness transition) (.witness fresh)

inductive PrologGCAdmissibleApplication {RootHandle : Type}
    (admissible : GCAdmissibility RootHandle) (world : ActorWorld)
    (roots : List RootHandle) (garbage : List ObjRef) : Prop where
  | witness : admissible world roots garbage →
      PrologGCAdmissibleApplication admissible world roots garbage

inductive PrologGCCollectStep {RootHandle : Type}
    (admissible : GCAdmissibility RootHandle) (prune : GCPruning)
    (roots : List RootHandle) : GCWrappedWorld → GCWrappedWorld → Prop where
  | collect {world : ActorWorld} {allocated garbage : List ObjRef} :
      PrologGCAdmissibleApplication admissible world roots garbage →
      PrologGCCollectStep admissible prune roots ⟨world, allocated⟩
        ⟨prune world garbage, allocated⟩

theorem prologGCCollectStep_iff
    {RootHandle : Type} {admissible : GCAdmissibility RootHandle}
    {prune : GCPruning} {roots : List RootHandle}
    {before after : GCWrappedWorld} :
    PrologGCCollectStep admissible prune roots before after ↔
      GCCollectStep admissible prune roots before after := by
  constructor
  · intro derivation
    cases derivation with
    | collect admissible =>
        cases admissible with
        | witness proof => exact .collect proof
  · intro derivation
    cases derivation with
    | collect proof => exact .collect (.witness proof)

end PrologBridge
end Newspeak
