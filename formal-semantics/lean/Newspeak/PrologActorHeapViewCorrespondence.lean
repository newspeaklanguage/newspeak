import Newspeak.ActorSemantics

/-! # Prolog correspondence for actor-visible heap components -/

namespace Newspeak
namespace PrologBridge

structure PrologActorHeapView (world : ActorWorld) (actor : ActorId)
    (shared privateHeap : Heap) : Prop where
  allocation : ∃ state,
    world.actorAllocations actor = some state ∧ state.heap = privateHeap
  shared_eq : world.valueHeap = shared

theorem prologActorHeapView_iff {world : ActorWorld} {actor : ActorId}
    {shared privateHeap : Heap} :
    PrologActorHeapView world actor shared privateHeap ↔
      (∃ state, world.actorAllocations actor = some state ∧
        state.heap = privateHeap) ∧ world.valueHeap = shared := by
  constructor
  · rintro ⟨allocation, shared⟩
    exact ⟨allocation, shared⟩
  · rintro ⟨allocation, shared⟩
    exact ⟨allocation, shared⟩

inductive PrologPrivateHeapsDisjoint (world : ActorWorld) : Prop where
  | witness : world.PrivateHeapsDisjoint → PrologPrivateHeapsDisjoint world

inductive PrologValueHeapDisjoint (world : ActorWorld) : Prop where
  | witness : world.ValueHeapDisjoint → PrologValueHeapDisjoint world

end PrologBridge
end Newspeak
