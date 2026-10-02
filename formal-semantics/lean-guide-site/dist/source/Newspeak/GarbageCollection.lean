import Newspeak.ConditionalReachabilityProofs

namespace Newspeak
namespace Heap

def retainedReference : List ObjRef → ObjRef → Bool
  | [], _ => false
  | candidate :: remaining, reference =>
      if candidate = reference then true
      else retainedReference remaining reference

@[simp] theorem retainedReference_eq_true_iff (reachable : List ObjRef)
    (reference : ObjRef) :
    retainedReference reachable reference = true ↔ reference ∈ reachable := by
  induction reachable with
  | nil => simp [retainedReference]
  | cons candidate remaining ih =>
      by_cases equal : candidate = reference
      · subst candidate
        simp [retainedReference]
      · have reverse : reference ≠ candidate := Ne.symm equal
        simp [retainedReference, equal, reverse, ih]

/-- Clear or remove weak observations after the reachability fixed point has
    been computed.  WeakArray length is preserved; dead cells become `nil`.
    WeakMap entries survive exactly when both key and value survive. -/
def collectWeakContainer (reachable : List ObjRef) (nilObject : ObjRef) :
    WeakContainer → WeakContainer
  | .weakArray elements =>
      .weakArray (elements.map fun reference =>
        if retainedReference reachable reference then reference else nilObject)
  | .weakMap entries =>
      .weakMap (entries.retainKeys fun key =>
        retainedReference reachable key &&
          match entries key with
          | none => false
          | some value => retainedReference reachable value)

def collectObjectDef (reachable : List ObjRef) (nilObject : ObjRef)
    (objectDef : ObjectDef) : ObjectDef :=
  { objectDef with
    weakContainer := objectDef.weakContainer.map
      (collectWeakContainer reachable nilObject) }

/-- Atomic heap pruning at an already-computed reachability fixed point. -/
def collectHeapAtReachability (h : Heap) (reachable : List ObjRef)
    (nilObject : ObjRef) : Heap :=
  { classes := h.classes.retainKeys fun id =>
      retainedReference reachable (.classObject id)
    objects :=
      (h.objects.mapValues fun _ objectDef =>
        collectObjectDef reachable nilObject objectDef).retainKeys fun id =>
          retainedReference reachable (.ordinaryObject id)
    mixinObjects := h.mixinObjects.retainKeys fun id =>
      retainedReference reachable (.mixinObject id)
    activations := h.activations.retainKeys fun id =>
      retainedReference reachable (.activationObject id)
    closures := h.closures.retainKeys fun id =>
      retainedReference reachable (.closureObject id)
    mirrors := h.mirrors.retainKeys fun id =>
      retainedReference reachable (.mirrorObject id)
    actors := h.actors.retainKeys fun id =>
      retainedReference reachable (.actorObject id) }

/-- The complete optional collection pass: compute the least strong plus
    ephemeron closure, then prune and clear atomically. -/
def collectHeap (h : Heap) (roots : List ObjRef) (nilObject : ObjRef) : Heap :=
  h.collectHeapAtReachability (h.conditionallyReachableReferences roots)
    nilObject

@[simp] theorem collectHeapAtReachability_object_present
    (h : Heap) (reachable : List ObjRef) (nilObject : ObjRef)
    (objectId : ObjectId) (objectDef : ObjectDef)
    (lookup : h.objects objectId = some objectDef)
    (retained : (.ordinaryObject objectId : ObjRef) ∈ reachable) :
    (h.collectHeapAtReachability reachable nilObject).objects objectId =
      some (collectObjectDef reachable nilObject objectDef) := by
  have retainedTrue :=
    (retainedReference_eq_true_iff reachable
      (.ordinaryObject objectId)).mpr retained
  simp [collectHeapAtReachability, lookup, retainedTrue]

@[simp] theorem collectHeapAtReachability_object_absent
    (h : Heap) (reachable : List ObjRef) (nilObject : ObjRef)
    (objectId : ObjectId)
    (discarded : (.ordinaryObject objectId : ObjRef) ∉ reachable) :
    (h.collectHeapAtReachability reachable nilObject).objects objectId = none := by
  have retainedFalse :
      retainedReference reachable (.ordinaryObject objectId) = false := by
    cases result : retainedReference reachable (.ordinaryObject objectId) with
    | false => rfl
    | true =>
        exfalso
        exact discarded
          ((retainedReference_eq_true_iff reachable
            (.ordinaryObject objectId)).mp result)
  simp [collectHeapAtReachability, retainedFalse]

@[simp] theorem collectWeakArray_length (reachable : List ObjRef)
    (nilObject : ObjRef) (elements : List ObjRef) :
    match collectWeakContainer reachable nilObject (.weakArray elements) with
    | .weakArray collected => collected.length = elements.length
    | .weakMap _ => False := by
  simp [collectWeakContainer]

theorem mem_collectedWeakArray_implies_retained_or_nil
    (reachable : List ObjRef) (nilObject reference : ObjRef)
    (elements : List ObjRef)
    (member : reference ∈ elements.map fun candidate =>
      if retainedReference reachable candidate then candidate else nilObject) :
    reference ∈ reachable ∨ reference = nilObject := by
  rcases List.mem_map.mp member with ⟨source, _sourceMember, equal⟩
  cases retained : retainedReference reachable source with
  | false =>
      right
      simpa [retained] using equal.symm
  | true =>
      left
      have sourceRetained :=
        (retainedReference_eq_true_iff reachable source).mp retained
      have referenceEqual : reference = source := by
        simpa [retained] using equal.symm
      simpa [referenceEqual] using sourceRetained

theorem readWeakArrayCell_after_collection
    (h : Heap) (reachable : List ObjRef) (nilObject : ObjRef)
    {objectId : ObjectId} {objectDef : ObjectDef}
    {elements : List ObjRef} {index : Nat} {oldValue : ObjRef}
    (objectLookup : h.objects objectId = some objectDef)
    (arrayPayload : objectDef.weakContainer = some (.weakArray elements))
    (objectRetained : (.ordinaryObject objectId : ObjRef) ∈ reachable)
    (cellLookup : elements[index]? = some oldValue) :
    (h.collectHeapAtReachability reachable nilObject).readWeakArrayCell
      objectId index =
        some (if retainedReference reachable oldValue
          then oldValue else nilObject) := by
  rw [readWeakArrayCell_present _ objectId
    (collectObjectDef reachable nilObject objectDef)
    (elements.map fun reference =>
      if retainedReference reachable reference then reference else nilObject)
    index]
  · simp [List.getElem?_map, cellLookup]
  · exact h.collectHeapAtReachability_object_present reachable nilObject
      objectId objectDef objectLookup objectRetained
  · simp [collectObjectDef, arrayPayload, collectWeakContainer]

@[simp] theorem collectedWeakMap_lookup_eq_some_iff
    (reachable : List ObjRef) (nilObject : ObjRef)
    (entries : FiniteStore ObjRef ObjRef) (key value : ObjRef) :
    let collected := match collectWeakContainer reachable nilObject
        (.weakMap entries) with
      | .weakMap result => result
      | .weakArray _ => FiniteStore.empty ObjRef ObjRef
    collected key = some value ↔
      entries key = some value ∧ key ∈ reachable ∧ value ∈ reachable := by
  dsimp [collectWeakContainer]
  rw [FiniteStore.retainKeys_lookup_eq_some_iff]
  constructor
  · rintro ⟨lookup, retained⟩
    simp [lookup] at retained
    exact ⟨lookup, retained.1, retained.2⟩
  · rintro ⟨lookup, keyRetained, valueRetained⟩
    refine ⟨lookup, ?_⟩
    simp [lookup, keyRetained, valueRetained]

theorem lookupWeakMapEntry_after_collection_iff
    (h : Heap) (reachable : List ObjRef) (nilObject : ObjRef)
    {objectId : ObjectId} {objectDef : ObjectDef}
    {entries : FiniteStore ObjRef ObjRef} {key value : ObjRef}
    (objectLookup : h.objects objectId = some objectDef)
    (mapPayload : objectDef.weakContainer = some (.weakMap entries))
    (objectRetained : (.ordinaryObject objectId : ObjRef) ∈ reachable) :
    (h.collectHeapAtReachability reachable nilObject).lookupWeakMapEntry
      objectId key = some value ↔
        entries key = some value ∧ key ∈ reachable ∧ value ∈ reachable := by
  rw [lookupWeakMapEntry_present _ objectId
    (collectObjectDef reachable nilObject objectDef)
    (entries.retainKeys fun candidate =>
      retainedReference reachable candidate &&
        match entries candidate with
        | none => false
        | some candidateValue => retainedReference reachable candidateValue)
    key]
  · exact collectedWeakMap_lookup_eq_some_iff reachable nilObject entries key value
  · exact h.collectHeapAtReachability_object_present reachable nilObject
      objectId objectDef objectLookup objectRetained
  · simp [collectObjectDef, mapPayload, collectWeakContainer]

theorem collectHeapAtReachability_classOf (h : Heap)
    (reachable : List ObjRef) (nilObject reference : ObjRef) :
    (h.collectHeapAtReachability reachable nilObject).classOf reference =
      if retainedReference reachable reference
      then h.classOf reference else none := by
  cases reference with
  | ordinaryObject id =>
      cases retained : retainedReference reachable (.ordinaryObject id) <;>
        simp [collectHeapAtReachability, classOf, collectObjectDef, retained]
      cases objectLookup : h.objects id <;>
        simp
  | classObject id =>
      cases retained : retainedReference reachable (.classObject id) <;>
        simp [collectHeapAtReachability, classOf, retained]
  | mixinObject id =>
      cases retained : retainedReference reachable (.mixinObject id) <;>
        simp [collectHeapAtReachability, classOf, retained]
  | activationObject id =>
      cases retained : retainedReference reachable (.activationObject id) <;>
        simp [collectHeapAtReachability, classOf, retained]
  | closureObject id =>
      cases retained : retainedReference reachable (.closureObject id) <;>
        simp [collectHeapAtReachability, classOf, retained]
  | mirrorObject id =>
      cases retained : retainedReference reachable (.mirrorObject id) <;>
        simp [collectHeapAtReachability, classOf, retained]
  | actorObject id =>
      cases retained : retainedReference reachable (.actorObject id) <;>
        simp [collectHeapAtReachability, classOf, retained]

theorem collectHeapAtReachability_isLiveObject_iff (h : Heap)
    (reachable : List ObjRef) (nilObject reference : ObjRef) :
    (h.collectHeapAtReachability reachable nilObject).IsLiveObject reference ↔
      reference ∈ reachable ∧ h.IsLiveObject reference := by
  simp only [IsLiveObject]
  rw [collectHeapAtReachability_classOf]
  cases retained : retainedReference reachable reference with
  | false =>
      have absent : reference ∉ reachable := by
        intro member
        have := (retainedReference_eq_true_iff reachable reference).mpr member
        simp [retained] at this
      simp [absent]
  | true =>
      have member :=
        (retainedReference_eq_true_iff reachable reference).mp retained
      simp [member]

/-- I33 at an explicit fixed point: every weak reference remaining after the
    atomic pruning pass resolves in the pruned heap. -/
theorem collectHeapAtReachability_weakContainersWellFormed
    (h : Heap) (reachable : List ObjRef) (nilObject : ObjRef)
    (reachableLive : ∀ reference, reference ∈ reachable →
      h.IsLiveObject reference)
    (nilRetained : nilObject ∈ reachable) :
    (h.collectHeapAtReachability reachable nilObject).WeakContainersWellFormed := by
  intro objectId collectedDef container collectedLookup containerPayload
  cases oldLookup : h.objects objectId with
  | none =>
      simp [collectHeapAtReachability, oldLookup] at collectedLookup
  | some oldDef =>
      cases retained : retainedReference reachable (.ordinaryObject objectId) with
      | false =>
          simp [collectHeapAtReachability, retained] at collectedLookup
      | true =>
          have objectRetained : (.ordinaryObject objectId : ObjRef) ∈ reachable :=
            (retainedReference_eq_true_iff reachable
              (.ordinaryObject objectId)).mp retained
          have installed := h.collectHeapAtReachability_object_present
            reachable nilObject objectId oldDef oldLookup objectRetained
          have definitionEqual : collectedDef =
              collectObjectDef reachable nilObject oldDef := by
            exact Option.some.inj (collectedLookup.symm.trans installed)
          subst collectedDef
          cases oldPayload : oldDef.weakContainer with
          | none =>
              simp [collectObjectDef, oldPayload] at containerPayload
          | some oldContainer =>
              cases oldContainer with
              | weakArray elements =>
                  have containerEqual : container = .weakArray
                      (elements.map fun reference =>
                        if retainedReference reachable reference
                        then reference else nilObject) := by
                    have payloadEqual : some (.weakArray
                        (elements.map fun reference =>
                          if retainedReference reachable reference
                          then reference else nilObject)) = some container := by
                      simpa [collectObjectDef, oldPayload, collectWeakContainer]
                        using containerPayload
                    exact (Option.some.inj payloadEqual).symm
                  subst container
                  intro reference member
                  rcases mem_collectedWeakArray_implies_retained_or_nil
                    reachable nilObject reference elements member with
                    retainedMember | isNil
                  · exact (h.collectHeapAtReachability_isLiveObject_iff
                      reachable nilObject reference).mpr
                        ⟨retainedMember,
                          reachableLive reference retainedMember⟩
                  · subst reference
                    exact (h.collectHeapAtReachability_isLiveObject_iff
                      reachable nilObject nilObject).mpr
                        ⟨nilRetained, reachableLive nilObject nilRetained⟩
              | weakMap entries =>
                  have containerEqual : container = .weakMap
                      (entries.retainKeys fun key =>
                        retainedReference reachable key &&
                          match entries key with
                          | none => false
                          | some value => retainedReference reachable value) := by
                    have payloadEqual : some (.weakMap
                        (entries.retainKeys fun key =>
                          retainedReference reachable key &&
                            match entries key with
                            | none => false
                            | some value => retainedReference reachable value)) =
                        some container := by
                      simpa [collectObjectDef, oldPayload, collectWeakContainer]
                        using containerPayload
                    exact (Option.some.inj payloadEqual).symm
                  subst container
                  intro key value lookup
                  have retained :=
                    (collectedWeakMap_lookup_eq_some_iff reachable nilObject
                      entries key value).mp lookup
                  exact ⟨
                    (h.collectHeapAtReachability_isLiveObject_iff
                      reachable nilObject key).mpr
                        ⟨retained.2.1, reachableLive key retained.2.1⟩,
                    (h.collectHeapAtReachability_isLiveObject_iff
                      reachable nilObject value).mpr
                        ⟨retained.2.2, reachableLive value retained.2.2⟩⟩

theorem collectHeap_isLiveObject_iff (h : Heap) (roots : List ObjRef)
    (nilObject reference : ObjRef) :
    (h.collectHeap roots nilObject).IsLiveObject reference ↔
      reference ∈ h.conditionallyReachableReferences roots := by
  rw [collectHeap, collectHeapAtReachability_isLiveObject_iff]
  constructor
  · exact And.left
  · intro retained
    exact ⟨retained,
      h.conditionallyReachableReferences_are_live roots reference retained⟩

theorem collectHeap_weakContainersWellFormed
    (h : Heap) (roots : List ObjRef) (nilObject : ObjRef)
    (nilRoot : nilObject ∈ roots) (nilLive : h.IsLiveObject nilObject) :
    (h.collectHeap roots nilObject).WeakContainersWellFormed := by
  apply h.collectHeapAtReachability_weakContainersWellFormed
  · intro reference member
    exact h.conditionallyReachableReferences_are_live roots reference member
  · exact (h.mem_conditionallyReachableReferences_iff_reachable
      roots nilObject).mpr (.root nilRoot nilLive)

end Heap
end Newspeak
