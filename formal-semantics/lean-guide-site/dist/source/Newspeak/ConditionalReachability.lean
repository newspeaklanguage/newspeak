import Newspeak.WeakContainers

namespace Newspeak
namespace Heap

/-- Weak-map lookup when the map is supplied as a general Newspeak object
    reference.  Only ordinary objects can carry weak-container payloads. -/
def weakMapLookupByReference (h : Heap) (source key : ObjRef) : Option ObjRef :=
  match source with
  | .ordinaryObject objectId => h.lookupWeakMapEntry objectId key
  | _ => none

/-- A stored ephemeron entry whose value still denotes a live object.  It is
    enabled only after both its map and key have become reachable. -/
def WeakMapEntryReference (h : Heap)
    (map key value : ObjRef) : Prop :=
  h.weakMapLookupByReference map key = some value ∧
    h.IsLiveObject value

/-- Live values enabled by keys in the current approximation. -/
def enabledWeakMapValues (h : Heap) (reached : List ObjRef)
    (map : ObjRef) : List ObjRef :=
  FiniteStore.deduplicated
    (reached.filterMap fun key =>
      (h.weakMapLookupByReference map key).filter h.isLiveObject)

@[simp] theorem mem_enabledWeakMapValues_iff (h : Heap)
    (reached : List ObjRef) (map value : ObjRef) :
    value ∈ h.enabledWeakMapValues reached map ↔
      ∃ key, key ∈ reached ∧ h.WeakMapEntryReference map key value := by
  rw [enabledWeakMapValues, FiniteStore.mem_deduplicated]
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨key, keyReached, filtered⟩
    cases lookup : h.weakMapLookupByReference map key with
    | none => simp [lookup, Option.filter] at filtered
    | some candidate =>
        by_cases live : h.isLiveObject candidate = true
        · simp [lookup, Option.filter, live] at filtered
          subst candidate
          exact ⟨key, keyReached, lookup,
            (h.isLiveObject_eq_true_iff value).mp live⟩
        · simp [lookup, Option.filter, live] at filtered
  · rintro ⟨key, keyReached, lookup, live⟩
    apply List.mem_filterMap.mpr
    refine ⟨key, keyReached, ?_⟩
    simp [lookup, Option.filter, (h.isLiveObject_eq_true_iff value).mpr live]

theorem enabledWeakMapValues_nodup (h : Heap) (reached : List ObjRef)
    (map : ObjRef) : (h.enabledWeakMapValues reached map).Nodup :=
  FiniteStore.deduplicated_nodup _

theorem enabledWeakMapValues_are_live (h : Heap) (reached : List ObjRef)
    (map value : ObjRef) (member : value ∈ h.enabledWeakMapValues reached map) :
    h.IsLiveObject value := by
  rcases (h.mem_enabledWeakMapValues_iff reached map value).mp member with
    ⟨key, _keyReached, entry⟩
  exact entry.2

/-- One source's unconditional strong successors plus its currently enabled
    ephemeron values. -/
def conditionalSuccessors (h : Heap) (reached : List ObjRef)
    (source : ObjRef) : List ObjRef :=
  FiniteStore.deduplicated
    (h.strongSuccessors source ++ h.enabledWeakMapValues reached source)

@[simp] theorem mem_conditionalSuccessors_iff (h : Heap)
    (reached : List ObjRef) (source target : ObjRef) :
    target ∈ h.conditionalSuccessors reached source ↔
      h.StrongReferenceEdge source target ∨
      ∃ key, key ∈ reached ∧ h.WeakMapEntryReference source key target := by
  simp [conditionalSuccessors, FiniteStore.mem_deduplicated,
    StrongReferenceEdge, mem_enabledWeakMapValues_iff]

theorem conditionalSuccessors_nodup (h : Heap) (reached : List ObjRef)
    (source : ObjRef) : (h.conditionalSuccessors reached source).Nodup :=
  FiniteStore.deduplicated_nodup _

theorem conditionalSuccessors_are_live (h : Heap) (reached : List ObjRef)
    (source target : ObjRef)
    (member : target ∈ h.conditionalSuccessors reached source) :
    h.IsLiveObject target := by
  rcases (h.mem_conditionalSuccessors_iff reached source target).mp member with
    strong | ⟨key, _keyReached, entry⟩
  · exact h.strongSuccessors_are_live source target strong
  · exact entry.2

/-- One monotone approximation step for strong plus ephemeron reachability. -/
def extendConditionalReachability (h : Heap)
    (reached : List ObjRef) : List ObjRef :=
  FiniteStore.deduplicated
    (reached ++ reached.flatMap (h.conditionalSuccessors reached))

@[simp] theorem mem_extendConditionalReachability_iff (h : Heap)
    (reached : List ObjRef) (target : ObjRef) :
    target ∈ h.extendConditionalReachability reached ↔
      target ∈ reached ∨
      (∃ source, source ∈ reached ∧
        h.StrongReferenceEdge source target) ∨
      (∃ map key, map ∈ reached ∧ key ∈ reached ∧
        h.WeakMapEntryReference map key target) := by
  simp only [extendConditionalReachability, FiniteStore.mem_deduplicated,
    List.mem_append, List.mem_flatMap, mem_conditionalSuccessors_iff]
  constructor
  · intro member
    rcases member with previous | ⟨source, sourceReached, successor⟩
    · exact Or.inl previous
    · rcases successor with strong | ⟨key, keyReached, weak⟩
      · exact Or.inr (Or.inl ⟨source, sourceReached, strong⟩)
      · exact Or.inr (Or.inr
          ⟨source, key, sourceReached, keyReached, weak⟩)
  · intro member
    rcases member with previous | strong | weak
    · exact Or.inl previous
    · rcases strong with ⟨source, sourceReached, edge⟩
      exact Or.inr ⟨source, sourceReached, Or.inl edge⟩
    · rcases weak with ⟨map, key, mapReached, keyReached, entry⟩
      exact Or.inr ⟨map, mapReached,
        Or.inr ⟨key, keyReached, entry⟩⟩

def conditionalReachabilityAt (h : Heap) (roots : List ObjRef) :
    Nat → List ObjRef
  | 0 => h.liveRootReferences roots
  | depth + 1 => h.extendConditionalReachability
      (h.conditionalReachabilityAt roots depth)

def ConditionallyReachableWithin (h : Heap) (roots : List ObjRef) :
    Nat → ObjRef → Prop
  | 0, target => target ∈ roots ∧ h.IsLiveObject target
  | depth + 1, target =>
      h.ConditionallyReachableWithin roots depth target ∨
      (∃ source,
        h.ConditionallyReachableWithin roots depth source ∧
        h.StrongReferenceEdge source target) ∨
      (∃ map key,
        h.ConditionallyReachableWithin roots depth map ∧
        h.ConditionallyReachableWithin roots depth key ∧
        h.WeakMapEntryReference map key target)

@[simp] theorem mem_conditionalReachabilityAt_iff (h : Heap)
    (roots : List ObjRef) (depth : Nat) (target : ObjRef) :
    target ∈ h.conditionalReachabilityAt roots depth ↔
      h.ConditionallyReachableWithin roots depth target := by
  induction depth generalizing target with
  | zero => simp [conditionalReachabilityAt, ConditionallyReachableWithin]
  | succ depth ih =>
      simp [conditionalReachabilityAt, ConditionallyReachableWithin, ih]

theorem conditionalReachabilityAt_nodup (h : Heap) (roots : List ObjRef)
    (depth : Nat) : (h.conditionalReachabilityAt roots depth).Nodup := by
  cases depth with
  | zero => exact FiniteStore.deduplicated_nodup _
  | succ depth => exact FiniteStore.deduplicated_nodup _

theorem conditionalReachabilityAt_objects_are_live (h : Heap)
    (roots : List ObjRef) (depth : Nat) (target : ObjRef)
    (member : target ∈ h.conditionalReachabilityAt roots depth) :
    h.IsLiveObject target := by
  induction depth with
  | zero =>
      exact (h.mem_liveRootReferences_iff roots target).mp member |>.2
  | succ depth ih =>
      rcases (h.mem_extendConditionalReachability_iff
        (h.conditionalReachabilityAt roots depth) target).mp member with
        previous | strong | weak
      · exact ih previous
      · rcases strong with ⟨source, _sourceReached, edge⟩
        exact h.strongSuccessors_are_live source target edge
      · rcases weak with ⟨map, key, _mapReached, _keyReached, entry⟩
        exact entry.2

/-- Finite executable result for strong plus conditional ephemeron edges. -/
def conditionallyReachableReferences (h : Heap)
    (roots : List ObjRef) : List ObjRef :=
  h.conditionalReachabilityAt roots h.liveObjectReferences.length

theorem conditionallyReachableReferences_nodup (h : Heap)
    (roots : List ObjRef) :
    (h.conditionallyReachableReferences roots).Nodup :=
  h.conditionalReachabilityAt_nodup roots _

theorem conditionallyReachableReferences_are_live (h : Heap)
    (roots : List ObjRef) (target : ObjRef)
    (member : target ∈ h.conditionallyReachableReferences roots) :
    h.IsLiveObject target :=
  h.conditionalReachabilityAt_objects_are_live roots _ target member

end Heap
end Newspeak
