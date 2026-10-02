import Newspeak.StrongReferences

namespace Newspeak
namespace Heap

/-- Extensional equality for list-backed finite sets. -/
def SameMembers (left right : List ObjRef) : Prop :=
  ∀ object, object ∈ left ↔ object ∈ right

theorem SameMembers.refl (objects : List ObjRef) :
    SameMembers objects objects := by
  intro object
  rfl

theorem SameMembers.symm {left right : List ObjRef}
    (same : SameMembers left right) : SameMembers right left := by
  intro object
  exact (same object).symm

theorem SameMembers.trans {first second third : List ObjRef}
    (left : SameMembers first second) (right : SameMembers second third) :
    SameMembers first third := by
  intro object
  exact (left object).trans (right object)

theorem extendStrongReachability_congr (h : Heap)
    {left right : List ObjRef} (same : SameMembers left right) :
    SameMembers (h.extendStrongReachability left)
      (h.extendStrongReachability right) := by
  intro target
  simp only [mem_extendStrongReachability_iff]
  constructor
  · intro member
    rcases member with inLeft | ⟨source, inLeft, edge⟩
    · exact Or.inl ((same target).mp inLeft)
    · exact Or.inr ⟨source, (same source).mp inLeft, edge⟩
  · intro member
    rcases member with inRight | ⟨source, inRight, edge⟩
    · exact Or.inl ((same target).mpr inRight)
    · exact Or.inr ⟨source, (same source).mpr inRight, edge⟩

theorem strongReachabilityAt_subset_next (h : Heap)
    (roots : List ObjRef) (depth : Nat) :
    h.strongReachabilityAt roots depth ⊆
      h.strongReachabilityAt roots (depth + 1) := by
  intro target member
  exact (h.mem_extendStrongReachability_iff
    (h.strongReachabilityAt roots depth) target).mpr (Or.inl member)

theorem strongReachabilityAt_subset_of_le (h : Heap)
    (roots : List ObjRef) {earlier later : Nat} (order : earlier ≤ later) :
    h.strongReachabilityAt roots earlier ⊆
      h.strongReachabilityAt roots later := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le order
  induction offset with
  | zero => intro target member; simpa using member
  | succ offset ih =>
      exact List.Subset.trans (ih (by omega))
        (h.strongReachabilityAt_subset_next roots (earlier + offset))

theorem strongReachabilityAt_subset_liveObjects (h : Heap)
    (roots : List ObjRef) (depth : Nat) :
    h.strongReachabilityAt roots depth ⊆ h.liveObjectReferences := by
  intro target member
  exact (h.mem_liveObjectReferences_iff target).mpr
    (h.strongReachabilityAt_objects_are_live roots depth target member)

theorem length_lt_of_subset_not_sameMembers
    {left right : List ObjRef} (leftNodup : left.Nodup)
    (subset : left ⊆ right) (different : ¬SameMembers left right) :
    left.length < right.length := by
  have lengthLe : left.length ≤ right.length :=
    leftNodup.length_le_of_subset subset
  apply Nat.lt_of_le_of_ne lengthLe
  intro lengthEqual
  apply different
  intro object
  constructor
  · intro inLeft
    exact subset inLeft
  · intro inRight
    by_cases inLeft : object ∈ left
    · exact inLeft
    · exfalso
      have consNodup : (object :: left).Nodup := by
        simp [inLeft, leftNodup]
      have consSubset : object :: left ⊆ right := by
        intro candidate member
        rcases List.mem_cons.mp member with equal | inLeft'
        · simpa [equal] using inRight
        · exact subset inLeft'
      have impossible := consNodup.length_le_of_subset consSubset
      simp only [List.length_cons, lengthEqual] at impossible
      omega

theorem strongReachability_fixed_persists (h : Heap)
    (roots : List ObjRef) {depth : Nat}
    (fixed : SameMembers
      (h.strongReachabilityAt roots depth)
      (h.strongReachabilityAt roots (depth + 1))) (offset : Nat) :
    SameMembers
      (h.strongReachabilityAt roots (depth + offset))
      (h.strongReachabilityAt roots (depth + offset + 1)) := by
  induction offset with
  | zero => simpa using fixed
  | succ offset ih =>
      simpa [Nat.add_succ, strongReachabilityAt] using
        h.extendStrongReachability_congr ih

/-- The finite iteration has stabilized extensionally after at most one pass
per live runtime identity. -/
theorem strongReachability_stabilized (h : Heap) (roots : List ObjRef) :
    SameMembers
      (h.strongReachabilityAt roots h.liveObjectReferences.length)
      (h.strongReachabilityAt roots
        (h.liveObjectReferences.length + 1)) := by
  let bound := h.liveObjectReferences.length
  apply Classical.byContradiction
  intro notStable
  change ¬SameMembers
    (h.strongReachabilityAt roots bound)
    (h.strongReachabilityAt roots (bound + 1)) at notStable
  have noEarlierStable : ∀ depth, depth ≤ bound →
      ¬SameMembers
        (h.strongReachabilityAt roots depth)
        (h.strongReachabilityAt roots (depth + 1)) := by
    intro depth depthLe fixed
    obtain ⟨offset, boundEq⟩ := Nat.exists_eq_add_of_le depthLe
    have persists := h.strongReachability_fixed_persists roots fixed offset
    rw [boundEq] at notStable
    exact notStable persists
  have lower : ∀ depth, depth ≤ bound + 1 →
      depth ≤ (h.strongReachabilityAt roots depth).length := by
    intro depth depthLe
    induction depth with
    | zero => omega
    | succ depth ih =>
        have depthLeBound : depth ≤ bound := by omega
        have previousLower :
            depth ≤ (h.strongReachabilityAt roots depth).length :=
          ih (by omega)
        have strictGrowth :
            (h.strongReachabilityAt roots depth).length <
              (h.strongReachabilityAt roots (depth + 1)).length :=
          length_lt_of_subset_not_sameMembers
            (h.strongReachabilityAt_nodup roots depth)
            (h.strongReachabilityAt_subset_next roots depth)
            (noEarlierStable depth depthLeBound)
        simpa using Nat.succ_le_of_lt
          (Nat.lt_of_le_of_lt previousLower strictGrowth)
  have lowerAtSuccessor : bound + 1 ≤
      (h.strongReachabilityAt roots (bound + 1)).length :=
    lower (bound + 1) (Nat.le_refl _)
  have upperAtSuccessor :
      (h.strongReachabilityAt roots (bound + 1)).length ≤ bound := by
    exact (h.strongReachabilityAt_nodup roots (bound + 1)).length_le_of_subset
      (h.strongReachabilityAt_subset_liveObjects roots (bound + 1))
  omega

inductive StronglyReachable (h : Heap) (roots : List ObjRef) :
    ObjRef → Prop where
  | root {object : ObjRef} :
      object ∈ roots → h.IsLiveObject object →
      StronglyReachable h roots object
  | edge {source target : ObjRef} :
      StronglyReachable h roots source →
      h.StrongReferenceEdge source target →
      StronglyReachable h roots target

theorem stronglyReachableWithin_sound (h : Heap) (roots : List ObjRef)
    {depth : Nat} {target : ObjRef}
    (reachable : h.StronglyReachableWithin roots depth target) :
    h.StronglyReachable roots target := by
  induction depth generalizing target with
  | zero =>
      exact .root reachable.1 reachable.2
  | succ depth ih =>
      rcases reachable with previous | ⟨source, sourceReachable, edge⟩
      · exact ih previous
      · exact .edge (ih sourceReachable) edge

theorem stronglyReachableReferences_closed (h : Heap)
    (roots : List ObjRef) {source target : ObjRef}
    (sourceReachable : source ∈ h.stronglyReachableReferences roots)
    (edge : h.StrongReferenceEdge source target) :
    target ∈ h.stronglyReachableReferences roots := by
  let bound := h.liveObjectReferences.length
  have nextMember : target ∈ h.strongReachabilityAt roots (bound + 1) := by
    exact (h.mem_extendStrongReachability_iff
      (h.strongReachabilityAt roots bound) target).mpr
        (Or.inr ⟨source, sourceReachable, edge⟩)
  exact (h.strongReachability_stabilized roots target).mpr nextMember

theorem mem_stronglyReachableReferences_iff_reachable (h : Heap)
    (roots : List ObjRef) (target : ObjRef) :
    target ∈ h.stronglyReachableReferences roots ↔
      h.StronglyReachable roots target := by
  constructor
  · intro member
    exact h.stronglyReachableWithin_sound roots
      ((h.mem_stronglyReachableReferences_iff roots target).mp member)
  · intro reachable
    induction reachable with
    | root inRoots live =>
        apply h.strongReachabilityAt_subset_of_le roots
          (Nat.zero_le h.liveObjectReferences.length)
        exact (h.mem_liveRootReferences_iff roots _).mpr ⟨inRoots, live⟩
    | edge sourceReachable edge ih =>
        exact h.stronglyReachableReferences_closed roots ih edge

/-- Least-fixed-point property: every set containing the live roots and closed
under strong edges contains the executable result. -/
theorem stronglyReachableReferences_least (h : Heap)
    (roots candidate : List ObjRef)
    (containsRoots : ∀ object, object ∈ roots → h.IsLiveObject object →
      object ∈ candidate)
    (closed : ∀ source, source ∈ candidate → ∀ target,
      h.StrongReferenceEdge source target → target ∈ candidate) :
    h.stronglyReachableReferences roots ⊆ candidate := by
  intro target member
  have reachable :=
    (h.mem_stronglyReachableReferences_iff_reachable roots target).mp member
  clear member
  induction reachable with
  | root inRoots live => exact containsRoots _ inRoots live
  | edge _ edge ih => exact closed _ ih _ edge

end Heap
end Newspeak
