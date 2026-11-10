import Newspeak.ReflectionActivationOrder
import Newspeak.PrologLookupCorrespondence

namespace Newspeak
namespace PrologBridge

inductive PrologActivationIds : ActivationStack → List ActivationId → Prop where
  | empty : PrologActivationIds .empty []
  | push {rest frame ids} :
      PrologActivationIds rest ids →
      PrologActivationIds (.push rest frame) (ids ++ [frame.activation])

theorem prologActivationIds_iff {stack ids} :
    PrologActivationIds stack ids ↔ stack.activationIds = ids := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | push _ ih => simp [ActivationStack.activationIds, ih]
  · intro equality
    subst ids
    induction stack with
    | empty => exact .empty
    | push rest frame ih => exact .push ih

inductive PrologRunStateActivationIds : ActorRunState → List ActivationId → Prop where
  | idle : PrologRunStateActivationIds .idle []
  | running {config reply event ids} :
      PrologActivationIds config.stack ids →
      PrologRunStateActivationIds (.runningTurn config reply event) ids
  | paused {config reply event token reason ids} :
      PrologActivationIds config.stack ids →
      PrologRunStateActivationIds (.pausedTurn config reply event token reason) ids

theorem prologRunStateActivationIds_iff {state ids} :
    PrologRunStateActivationIds state ids ↔ state.stackActivationIds = ids := by
  constructor
  · intro derivation
    cases derivation with
    | idle => rfl
    | running stack | paused stack =>
        exact prologActivationIds_iff.mp stack
  · intro equality
    cases state with
    | idle =>
        simp [ActorRunState.stackActivationIds] at equality
        subst ids
        exact .idle
    | runningTurn config reply event =>
        exact .running (prologActivationIds_iff.mpr equality)
    | pausedTurn config reply event token reason =>
        exact .paused (prologActivationIds_iff.mpr equality)

inductive PrologLiveActivationIdsFrom (world : ActorWorld) :
    List ActorId → List ActivationId → Prop where
  | empty : PrologLiveActivationIdsFrom world [] []
  | absent {actor remaining later ids} :
      world.runStates actor = none →
      PrologLiveActivationIdsFrom world remaining later →
      FiniteStore.deduplicated later = ids →
      PrologLiveActivationIdsFrom world (actor :: remaining) ids
  | present {actor remaining state current later ids} :
      world.runStates actor = some state →
      PrologRunStateActivationIds state current →
      PrologLiveActivationIdsFrom world remaining later →
      FiniteStore.deduplicated (current ++ later) = ids →
      PrologLiveActivationIdsFrom world (actor :: remaining) ids

theorem prologLiveActivationIdsFrom_iff {world actors ids} :
    PrologLiveActivationIdsFrom world actors ids ↔
      world.liveActivationIdsFrom actors = ids := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | absent lookup _ deduplicated ih =>
        simpa [ActorWorld.liveActivationIdsFrom, lookup, ih] using deduplicated
    | present lookup current _ deduplicated ih =>
        simpa [ActorWorld.liveActivationIdsFrom, lookup,
          prologRunStateActivationIds_iff.mp current, ih] using deduplicated
  · intro equality
    induction actors generalizing ids with
    | nil =>
        simp [ActorWorld.liveActivationIdsFrom] at equality
        subst ids
        exact .empty
    | cons actor remaining ih =>
        cases lookup : world.runStates actor with
        | none =>
            rw [ActorWorld.liveActivationIdsFrom, lookup] at equality
            exact .absent lookup (ih rfl) equality
        | some state =>
            rw [ActorWorld.liveActivationIdsFrom, lookup] at equality
            exact .present lookup
              (prologRunStateActivationIds_iff.mpr rfl) (ih rfl) equality

inductive PrologListBefore {Element : Type} (first second : Element) :
    List Element → Prop where
  | here {remaining} : PrologListMember second remaining →
      PrologListBefore first second (first :: remaining)
  | later {head remaining} : PrologListBefore first second remaining →
      PrologListBefore first second (head :: remaining)

theorem prologListBefore_iff {Element : Type} {first second : Element}
    {elements : List Element} :
    PrologListBefore first second elements ↔ ListBefore first second elements := by
  constructor
  · intro derivation
    induction derivation with
    | here member => exact .here (prologListMember_iff.mp member)
    | later _ ih => exact .later ih
  · intro derivation
    induction derivation with
    | here member => exact .here (prologListMember_iff.mpr member)
    | later _ ih => exact .later ih

inductive PrologActorBelow (world : ActorWorld) (actor : ActorId)
    (lower upper : ActivationId) : Prop where
  | below {state ids} :
      world.runStates actor = some state →
      PrologRunStateActivationIds state ids →
      PrologListBefore lower upper ids →
      PrologActorBelow world actor lower upper

theorem prologActorBelow_iff {world actor lower upper} :
    PrologActorBelow world actor lower upper ↔
      world.Below actor lower upper := by
  constructor
  · rintro ⟨lookup, ids, below⟩
    exact ⟨_, lookup, by
      rw [prologRunStateActivationIds_iff.mp ids]
      exact prologListBefore_iff.mp below⟩
  · rintro ⟨state, lookup, below⟩
    exact .below lookup (prologRunStateActivationIds_iff.mpr rfl)
      (prologListBefore_iff.mpr below)

end PrologBridge
end Newspeak
