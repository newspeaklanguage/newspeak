import Newspeak.ConditionalReachability

namespace Newspeak
namespace Heap

theorem extendConditionalReachability_congr (h : Heap)
    {left right : List ObjRef} (same : SameMembers left right) :
    SameMembers (h.extendConditionalReachability left)
      (h.extendConditionalReachability right) := by
  intro target
  simp only [mem_extendConditionalReachability_iff]
  constructor
  · intro member
    rcases member with previous | strong | weak
    · exact Or.inl ((same target).mp previous)
    · rcases strong with ⟨source, sourceReached, edge⟩
      exact Or.inr (Or.inl
        ⟨source, (same source).mp sourceReached, edge⟩)
    · rcases weak with ⟨map, key, mapReached, keyReached, entry⟩
      exact Or.inr (Or.inr
        ⟨map, key, (same map).mp mapReached,
          (same key).mp keyReached, entry⟩)
  · intro member
    rcases member with previous | strong | weak
    · exact Or.inl ((same target).mpr previous)
    · rcases strong with ⟨source, sourceReached, edge⟩
      exact Or.inr (Or.inl
        ⟨source, (same source).mpr sourceReached, edge⟩)
    · rcases weak with ⟨map, key, mapReached, keyReached, entry⟩
      exact Or.inr (Or.inr
        ⟨map, key, (same map).mpr mapReached,
          (same key).mpr keyReached, entry⟩)

theorem conditionalReachabilityAt_subset_next (h : Heap)
    (roots : List ObjRef) (depth : Nat) :
    h.conditionalReachabilityAt roots depth ⊆
      h.conditionalReachabilityAt roots (depth + 1) := by
  intro target member
  exact (h.mem_extendConditionalReachability_iff
    (h.conditionalReachabilityAt roots depth) target).mpr (Or.inl member)

theorem conditionalReachabilityAt_subset_of_le (h : Heap)
    (roots : List ObjRef) {earlier later : Nat} (order : earlier ≤ later) :
    h.conditionalReachabilityAt roots earlier ⊆
      h.conditionalReachabilityAt roots later := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le order
  induction offset with
  | zero => intro target member; simpa using member
  | succ offset ih =>
      exact List.Subset.trans (ih (by omega))
        (h.conditionalReachabilityAt_subset_next roots (earlier + offset))

theorem conditionalReachabilityAt_subset_liveObjects (h : Heap)
    (roots : List ObjRef) (depth : Nat) :
    h.conditionalReachabilityAt roots depth ⊆ h.liveObjectReferences := by
  intro target member
  exact (h.mem_liveObjectReferences_iff target).mpr
    (h.conditionalReachabilityAt_objects_are_live roots depth target member)

theorem conditionalReachability_fixed_persists (h : Heap)
    (roots : List ObjRef) {depth : Nat}
    (fixed : SameMembers
      (h.conditionalReachabilityAt roots depth)
      (h.conditionalReachabilityAt roots (depth + 1))) (offset : Nat) :
    SameMembers
      (h.conditionalReachabilityAt roots (depth + offset))
      (h.conditionalReachabilityAt roots (depth + offset + 1)) := by
  induction offset with
  | zero => simpa using fixed
  | succ offset ih =>
      simpa [Nat.add_succ, conditionalReachabilityAt] using
        h.extendConditionalReachability_congr ih

/-- Strong-plus-ephemeron iteration stabilizes after at most one strict-growth
    step per live runtime identity. -/
theorem conditionalReachability_stabilized (h : Heap) (roots : List ObjRef) :
    SameMembers
      (h.conditionalReachabilityAt roots h.liveObjectReferences.length)
      (h.conditionalReachabilityAt roots
        (h.liveObjectReferences.length + 1)) := by
  let bound := h.liveObjectReferences.length
  apply Classical.byContradiction
  intro notStable
  change ¬SameMembers
    (h.conditionalReachabilityAt roots bound)
    (h.conditionalReachabilityAt roots (bound + 1)) at notStable
  have noEarlierStable : ∀ depth, depth ≤ bound →
      ¬SameMembers
        (h.conditionalReachabilityAt roots depth)
        (h.conditionalReachabilityAt roots (depth + 1)) := by
    intro depth depthLe fixed
    obtain ⟨offset, boundEq⟩ := Nat.exists_eq_add_of_le depthLe
    have persists := h.conditionalReachability_fixed_persists roots fixed offset
    rw [boundEq] at notStable
    exact notStable persists
  have lower : ∀ depth, depth ≤ bound + 1 →
      depth ≤ (h.conditionalReachabilityAt roots depth).length := by
    intro depth depthLe
    induction depth with
    | zero => omega
    | succ depth ih =>
        have depthLeBound : depth ≤ bound := by omega
        have previousLower :
            depth ≤ (h.conditionalReachabilityAt roots depth).length :=
          ih (by omega)
        have strictGrowth :
            (h.conditionalReachabilityAt roots depth).length <
              (h.conditionalReachabilityAt roots (depth + 1)).length :=
          length_lt_of_subset_not_sameMembers
            (h.conditionalReachabilityAt_nodup roots depth)
            (h.conditionalReachabilityAt_subset_next roots depth)
            (noEarlierStable depth depthLeBound)
        simpa using Nat.succ_le_of_lt
          (Nat.lt_of_le_of_lt previousLower strictGrowth)
  have lowerAtSuccessor : bound + 1 ≤
      (h.conditionalReachabilityAt roots (bound + 1)).length :=
    lower (bound + 1) (Nat.le_refl _)
  have upperAtSuccessor :
      (h.conditionalReachabilityAt roots (bound + 1)).length ≤ bound := by
    exact (h.conditionalReachabilityAt_nodup roots
      (bound + 1)).length_le_of_subset
        (h.conditionalReachabilityAt_subset_liveObjects roots (bound + 1))
  omega

/-- Inductive presentation of the least set closed under both unconditional
    strong edges and enabled ephemeron entries. -/
inductive ConditionallyReachable (h : Heap) (roots : List ObjRef) :
    ObjRef → Prop where
  | root {object : ObjRef} :
      object ∈ roots → h.IsLiveObject object →
      ConditionallyReachable h roots object
  | strongEdge {source target : ObjRef} :
      ConditionallyReachable h roots source →
      h.StrongReferenceEdge source target →
      ConditionallyReachable h roots target
  | weakMapValue {map key value : ObjRef} :
      ConditionallyReachable h roots map →
      ConditionallyReachable h roots key →
      h.WeakMapEntryReference map key value →
      ConditionallyReachable h roots value

theorem conditionallyReachableWithin_sound (h : Heap) (roots : List ObjRef)
    {depth : Nat} {target : ObjRef}
    (reachable : h.ConditionallyReachableWithin roots depth target) :
    h.ConditionallyReachable roots target := by
  induction depth generalizing target with
  | zero => exact .root reachable.1 reachable.2
  | succ depth ih =>
      rcases reachable with previous | strong | weak
      · exact ih previous
      · rcases strong with ⟨source, sourceReachable, edge⟩
        exact .strongEdge (ih sourceReachable) edge
      · rcases weak with
          ⟨map, key, mapReachable, keyReachable, entry⟩
        exact .weakMapValue (ih mapReachable) (ih keyReachable) entry

theorem conditionallyReachableReferences_closed_under_strongEdge (h : Heap)
    (roots : List ObjRef) {source target : ObjRef}
    (sourceReachable : source ∈ h.conditionallyReachableReferences roots)
    (edge : h.StrongReferenceEdge source target) :
    target ∈ h.conditionallyReachableReferences roots := by
  let bound := h.liveObjectReferences.length
  have nextMember : target ∈
      h.conditionalReachabilityAt roots (bound + 1) := by
    exact (h.mem_extendConditionalReachability_iff
      (h.conditionalReachabilityAt roots bound) target).mpr
        (Or.inr (Or.inl ⟨source, sourceReachable, edge⟩))
  exact (h.conditionalReachability_stabilized roots target).mpr nextMember

theorem conditionallyReachableReferences_closed_under_weakMapValue (h : Heap)
    (roots : List ObjRef) {map key value : ObjRef}
    (mapReachable : map ∈ h.conditionallyReachableReferences roots)
    (keyReachable : key ∈ h.conditionallyReachableReferences roots)
    (entry : h.WeakMapEntryReference map key value) :
    value ∈ h.conditionallyReachableReferences roots := by
  let bound := h.liveObjectReferences.length
  have nextMember : value ∈
      h.conditionalReachabilityAt roots (bound + 1) := by
    exact (h.mem_extendConditionalReachability_iff
      (h.conditionalReachabilityAt roots bound) value).mpr
        (Or.inr (Or.inr ⟨map, key, mapReachable, keyReachable, entry⟩))
  exact (h.conditionalReachability_stabilized roots value).mpr nextMember

theorem mem_conditionallyReachableReferences_iff_reachable (h : Heap)
    (roots : List ObjRef) (target : ObjRef) :
    target ∈ h.conditionallyReachableReferences roots ↔
      h.ConditionallyReachable roots target := by
  constructor
  · intro member
    exact h.conditionallyReachableWithin_sound roots
      ((h.mem_conditionalReachabilityAt_iff roots _ target).mp member)
  · intro reachable
    induction reachable with
    | root inRoots live =>
        apply h.conditionalReachabilityAt_subset_of_le roots
          (Nat.zero_le h.liveObjectReferences.length)
        exact (h.mem_liveRootReferences_iff roots _).mpr ⟨inRoots, live⟩
    | strongEdge sourceReachable edge ih =>
        exact h.conditionallyReachableReferences_closed_under_strongEdge
          roots ih edge
    | weakMapValue mapReachable keyReachable entry mapIH keyIH =>
        exact h.conditionallyReachableReferences_closed_under_weakMapValue
          roots mapIH keyIH entry

/-- M8: the executable result is the least live-root-containing set closed
    under unconditional edges and the two-premise ephemeron rule. -/
theorem conditionallyReachableReferences_least (h : Heap)
    (roots candidate : List ObjRef)
    (containsRoots : ∀ object, object ∈ roots → h.IsLiveObject object →
      object ∈ candidate)
    (strongClosed : ∀ source, source ∈ candidate → ∀ target,
      h.StrongReferenceEdge source target → target ∈ candidate)
    (weakMapClosed : ∀ map key,
      map ∈ candidate → key ∈ candidate → ∀ value,
      h.WeakMapEntryReference map key value → value ∈ candidate) :
    h.conditionallyReachableReferences roots ⊆ candidate := by
  intro target member
  have reachable :=
    (h.mem_conditionallyReachableReferences_iff_reachable roots target).mp member
  clear member
  induction reachable with
  | root inRoots live => exact containsRoots _ inRoots live
  | strongEdge _ edge ih => exact strongClosed _ ih _ edge
  | weakMapValue _ _ entry mapIH keyIH =>
      exact weakMapClosed _ _ mapIH keyIH _ entry

theorem stronglyReachableReferences_subset_conditionallyReachableReferences
    (h : Heap) (roots : List ObjRef) :
    h.stronglyReachableReferences roots ⊆
      h.conditionallyReachableReferences roots := by
  intro target member
  have reachable :=
    (h.mem_stronglyReachableReferences_iff_reachable roots target).mp member
  clear member
  have conditional : h.ConditionallyReachable roots target := by
    induction reachable with
    | root inRoots live => exact .root inRoots live
    | edge sourceReachable edge ih => exact .strongEdge ih edge
  exact (h.mem_conditionallyReachableReferences_iff_reachable roots target).mpr
    conditional

end Heap
end Newspeak
