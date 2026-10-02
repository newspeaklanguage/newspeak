import Newspeak.StrongReachabilityProofs

namespace Newspeak

theorem List.mem_set_implies_new_or_old {Element : Type}
    {elements : List Element} {index : Nat} {newValue candidate : Element}
    (member : candidate ∈ elements.set index newValue) :
    candidate = newValue ∨ candidate ∈ elements := by
  induction elements generalizing index with
  | nil => simp at member
  | cons first remaining ih =>
      cases index with
      | zero =>
          rcases List.mem_cons.mp member with equal | inRemaining
          · exact Or.inl equal
          · exact Or.inr (List.mem_cons.mpr (Or.inr inRemaining))
      | succ index =>
          simp only [List.set] at member
          rcases List.mem_cons.mp member with equal | inSetRemaining
          · exact Or.inr (List.mem_cons.mpr (Or.inl equal))
          · rcases ih inSetRemaining with equal | inRemaining
            · exact Or.inl equal
            · exact Or.inr (List.mem_cons.mpr (Or.inr inRemaining))

namespace WeakContainer

/-- Every identity observed through weak storage still denotes a live heap
    object before collection.  The predicate says nothing about reachability:
    weak-array elements are non-edges and weak-map values are handled by the
    conditional ephemeron closure. -/
def ReferencesAreLive (h : Heap) : WeakContainer → Prop
  | .weakArray elements =>
      ∀ reference, reference ∈ elements → h.IsLiveObject reference
  | .weakMap entries =>
      ∀ key value, entries key = some value →
        h.IsLiveObject key ∧ h.IsLiveObject value

theorem ReferencesAreLive.transport {h h' : Heap} {container : WeakContainer}
    (preservesLive : ∀ reference,
      h.IsLiveObject reference → h'.IsLiveObject reference)
    (valid : container.ReferencesAreLive h) :
    container.ReferencesAreLive h' := by
  cases container with
  | weakArray elements =>
      intro reference member
      exact preservesLive reference (valid reference member)
  | weakMap entries =>
      intro key value lookup
      exact ⟨preservesLive key (valid key value lookup).1,
        preservesLive value (valid key value lookup).2⟩

end WeakContainer

namespace Heap

/-- Heap-wide validity of VM-supported weak payloads.  It is deliberately
    separate from `Program.WellFormed`: garbage collection may temporarily
    need to identify dead weak observations before atomically clearing them. -/
def WeakContainersWellFormed (h : Heap) : Prop :=
  ∀ objectId objectDef container,
    h.objects objectId = some objectDef →
    objectDef.weakContainer = some container →
    container.ReferencesAreLive h

/-- Zero-based VM access to a `WeakArray` cell.  Surface-library indexing is
    translated before this primitive is invoked. -/
def readWeakArrayCell (h : Heap) (objectId : ObjectId)
    (index : Nat) : Option ObjRef := do
  let objectDef ← h.objects objectId
  let container ← objectDef.weakContainer
  match container with
  | .weakArray elements => elements[index]?
  | .weakMap _ => none

/-- Replace an existing zero-based `WeakArray` cell.  The operation fails for
    a missing object, a non-weak-array object, or an out-of-bounds index. -/
def writeWeakArrayCell (h : Heap) (objectId : ObjectId) (index : Nat)
    (value : ObjRef) : Option Heap := do
  let objectDef ← h.objects objectId
  let container ← objectDef.weakContainer
  match container with
  | .weakArray elements =>
      let _ ← elements[index]?
      let updated : ObjectDef :=
        { objectDef with
          weakContainer := some (.weakArray (elements.set index value)) }
      some (h.installObject objectId updated)
  | .weakMap _ => none

/-- Lookup in a VM-supported `WeakMap`.  Absence includes a missing object,
    the wrong weak-container kind, and a missing key. -/
def lookupWeakMapEntry (h : Heap) (objectId : ObjectId)
    (key : ObjRef) : Option ObjRef := do
  let objectDef ← h.objects objectId
  let container ← objectDef.weakContainer
  match container with
  | .weakArray _ => none
  | .weakMap entries => entries key

/-- Insert or replace a `WeakMap` entry.  Unlike weak-array writes, map writes
    need not target an existing key. -/
def writeWeakMapEntry (h : Heap) (objectId : ObjectId) (key value : ObjRef) :
    Option Heap := do
  let objectDef ← h.objects objectId
  let container ← objectDef.weakContainer
  match container with
  | .weakArray _ => none
  | .weakMap entries =>
      let updated : ObjectDef :=
        { objectDef with
          weakContainer := some (.weakMap (entries.install key value)) }
      some (h.installObject objectId updated)

@[simp] theorem readWeakArrayCell_present (h : Heap) (objectId : ObjectId)
    (objectDef : ObjectDef) (elements : List ObjRef) (index : Nat)
    (objectLookup : h.objects objectId = some objectDef)
    (arrayPayload : objectDef.weakContainer = some (.weakArray elements)) :
    h.readWeakArrayCell objectId index = elements[index]? := by
  simp [readWeakArrayCell, objectLookup, arrayPayload]

@[simp] theorem lookupWeakMapEntry_present (h : Heap) (objectId : ObjectId)
    (objectDef : ObjectDef) (entries : FiniteStore ObjRef ObjRef)
    (key : ObjRef) (objectLookup : h.objects objectId = some objectDef)
    (mapPayload : objectDef.weakContainer = some (.weakMap entries)) :
    h.lookupWeakMapEntry objectId key = entries key := by
  simp [lookupWeakMapEntry, objectLookup, mapPayload]

theorem writeWeakArrayCell_installs {h h' : Heap} {objectId : ObjectId}
    {index : Nat} {value : ObjRef}
    (write : h.writeWeakArrayCell objectId index value = some h') :
    ∃ objectDef elements oldValue,
      h.objects objectId = some objectDef ∧
      objectDef.weakContainer = some (.weakArray elements) ∧
      elements[index]? = some oldValue ∧
      h' = h.installObject objectId
        { objectDef with
          weakContainer := some (.weakArray (elements.set index value)) } := by
  cases objectLookup : h.objects objectId with
  | none => simp [writeWeakArrayCell, objectLookup] at write
  | some objectDef =>
      cases objectPayload : objectDef.weakContainer with
      | none => simp [writeWeakArrayCell, objectLookup, objectPayload] at write
      | some container =>
          cases container with
          | weakMap entries =>
              simp [writeWeakArrayCell, objectLookup, objectPayload] at write
          | weakArray elements =>
              cases cellLookup : elements[index]? with
              | none =>
                  simp [writeWeakArrayCell, objectLookup, objectPayload,
                    cellLookup] at write
              | some oldValue =>
                  simp [writeWeakArrayCell, objectLookup, objectPayload,
                    cellLookup] at write
                  subst h'
                  exact ⟨objectDef, elements, oldValue, rfl, objectPayload,
                    cellLookup, rfl⟩

theorem writeWeakMapEntry_installs {h h' : Heap} {objectId : ObjectId}
    {key value : ObjRef}
    (write : h.writeWeakMapEntry objectId key value = some h') :
    ∃ objectDef entries,
      h.objects objectId = some objectDef ∧
      objectDef.weakContainer = some (.weakMap entries) ∧
      h' = h.installObject objectId
        { objectDef with
          weakContainer := some (.weakMap (entries.install key value)) } := by
  cases objectLookup : h.objects objectId with
  | none => simp [writeWeakMapEntry, objectLookup] at write
  | some objectDef =>
      cases objectPayload : objectDef.weakContainer with
      | none => simp [writeWeakMapEntry, objectLookup, objectPayload] at write
      | some container =>
          cases container with
          | weakArray elements =>
              simp [writeWeakMapEntry, objectLookup, objectPayload] at write
          | weakMap entries =>
              simp [writeWeakMapEntry, objectLookup, objectPayload] at write
              subst h'
              exact ⟨objectDef, entries, rfl, objectPayload, rfl⟩

theorem readWeakArrayCell_after_write {h h' : Heap} {objectId : ObjectId}
    {index : Nat} {value : ObjRef}
    (write : h.writeWeakArrayCell objectId index value = some h') :
    h'.readWeakArrayCell objectId index = some value := by
  rcases writeWeakArrayCell_installs write with
    ⟨objectDef, elements, oldValue, objectLookup, objectPayload,
      cellLookup, equal⟩
  subst h'
  rcases List.getElem?_eq_some_iff.mp cellLookup with ⟨inBounds, _⟩
  simp [readWeakArrayCell, installObject, inBounds]

theorem lookupWeakMapEntry_after_write {h h' : Heap} {objectId : ObjectId}
    {key value : ObjRef}
    (write : h.writeWeakMapEntry objectId key value = some h') :
    h'.lookupWeakMapEntry objectId key = some value := by
  rcases writeWeakMapEntry_installs write with
    ⟨objectDef, entries, objectLookup, objectPayload, equal⟩
  subst h'
  simp [lookupWeakMapEntry, installObject]

/-- Replacing an ordinary object's record without changing its class preserves
    the runtime class of every tagged object identity. -/
theorem installObject_preserves_classOf_when_class_unchanged
    (h : Heap) (objectId : ObjectId) (oldDef newDef : ObjectDef)
    (oldLookup : h.objects objectId = some oldDef)
    (sameClass : newDef.classId = oldDef.classId) (reference : ObjRef) :
    (h.installObject objectId newDef).classOf reference = h.classOf reference := by
  cases reference with
  | ordinaryObject candidate =>
      by_cases target : candidate = objectId
      · subst candidate
        simp [classOf, installObject, oldLookup, sameClass]
      · simp [classOf, installObject, target]
  | classObject candidate => rfl
  | mixinObject candidate => rfl
  | activationObject candidate => rfl
  | closureObject candidate => rfl
  | mirrorObject candidate => rfl
  | actorObject candidate => rfl

theorem installObject_preserves_liveness_when_class_unchanged
    (h : Heap) (objectId : ObjectId) (oldDef newDef : ObjectDef)
    (oldLookup : h.objects objectId = some oldDef)
    (sameClass : newDef.classId = oldDef.classId) (reference : ObjRef) :
    (h.installObject objectId newDef).IsLiveObject reference ↔
      h.IsLiveObject reference := by
  simp only [IsLiveObject]
  rw [installObject_preserves_classOf_when_class_unchanged h objectId
    oldDef newDef oldLookup sameClass reference]

theorem readWeakArrayCell_live (h : Heap) (valid : h.WeakContainersWellFormed)
    {objectId : ObjectId} {index : Nat} {value : ObjRef}
    (read : h.readWeakArrayCell objectId index = some value) :
    h.IsLiveObject value := by
  cases objectLookup : h.objects objectId with
  | none => simp [readWeakArrayCell, objectLookup] at read
  | some objectDef =>
      cases objectPayload : objectDef.weakContainer with
      | none => simp [readWeakArrayCell, objectLookup, objectPayload] at read
      | some container =>
          cases container with
          | weakMap entries =>
              simp [readWeakArrayCell, objectLookup, objectPayload] at read
          | weakArray elements =>
              have containerValid := valid objectId objectDef
                (.weakArray elements) objectLookup objectPayload
              apply containerValid value
              rw [List.mem_iff_getElem]
              rcases List.getElem?_eq_some_iff.mp (by
                simpa [readWeakArrayCell, objectLookup, objectPayload] using read)
                with ⟨inBounds, equal⟩
              exact ⟨index, inBounds, equal⟩

theorem lookupWeakMapEntry_live (h : Heap)
    (valid : h.WeakContainersWellFormed) {objectId : ObjectId}
    {key value : ObjRef}
    (lookup : h.lookupWeakMapEntry objectId key = some value) :
    h.IsLiveObject key ∧ h.IsLiveObject value := by
  cases objectLookup : h.objects objectId with
  | none => simp [lookupWeakMapEntry, objectLookup] at lookup
  | some objectDef =>
      cases objectPayload : objectDef.weakContainer with
      | none => simp [lookupWeakMapEntry, objectLookup, objectPayload] at lookup
      | some container =>
          cases container with
          | weakArray elements =>
              simp [lookupWeakMapEntry, objectLookup, objectPayload] at lookup
          | weakMap entries =>
              apply valid objectId objectDef (.weakMap entries) objectLookup
                objectPayload key value
              simpa [lookupWeakMapEntry, objectLookup, objectPayload] using lookup

theorem writeWeakArrayCell_preserves_weakContainersWellFormed
    {h h' : Heap} (valid : h.WeakContainersWellFormed)
    {objectId : ObjectId} {index : Nat} {value : ObjRef}
    (valueLive : h.IsLiveObject value)
    (write : h.writeWeakArrayCell objectId index value = some h') :
    h'.WeakContainersWellFormed := by
  rcases writeWeakArrayCell_installs write with
    ⟨objectDef, elements, oldValue, objectLookup, objectPayload,
      cellLookup, equal⟩
  subst h'
  let updated : ObjectDef :=
    { objectDef with
      weakContainer := some (.weakArray (elements.set index value)) }
  have liveForward : ∀ reference,
      h.IsLiveObject reference →
        (h.installObject objectId updated).IsLiveObject reference := by
    intro reference live
    exact (installObject_preserves_liveness_when_class_unchanged h objectId
      objectDef updated objectLookup rfl reference).mpr live
  intro candidate candidateDef container candidateLookup containerPayload
  by_cases target : candidate = objectId
  · subst candidate
    have candidateEqual : candidateDef = updated := by
      have installed : some updated = some candidateDef := by
        simpa [installObject] using candidateLookup
      exact (Option.some.inj installed).symm
    subst candidateDef
    have containerEqual : container =
        .weakArray (elements.set index value) := by
      simpa [updated] using (Option.some.inj containerPayload).symm
    subst container
    intro reference member
    rcases List.mem_set_implies_new_or_old member with equal | oldMember
    · subst reference
      exact liveForward value valueLive
    · have oldValid := valid objectId objectDef (.weakArray elements)
        objectLookup objectPayload
      exact liveForward reference (oldValid reference oldMember)
  · have oldCandidateLookup : h.objects candidate = some candidateDef := by
      simpa [installObject, target] using candidateLookup
    exact (valid candidate candidateDef container oldCandidateLookup
      containerPayload).transport liveForward

theorem writeWeakMapEntry_preserves_weakContainersWellFormed
    {h h' : Heap} (valid : h.WeakContainersWellFormed)
    {objectId : ObjectId} {key value : ObjRef}
    (keyLive : h.IsLiveObject key) (valueLive : h.IsLiveObject value)
    (write : h.writeWeakMapEntry objectId key value = some h') :
    h'.WeakContainersWellFormed := by
  rcases writeWeakMapEntry_installs write with
    ⟨objectDef, entries, objectLookup, objectPayload, equal⟩
  subst h'
  let updated : ObjectDef :=
    { objectDef with
      weakContainer := some (.weakMap (entries.install key value)) }
  have liveForward : ∀ reference,
      h.IsLiveObject reference →
        (h.installObject objectId updated).IsLiveObject reference := by
    intro reference live
    exact (installObject_preserves_liveness_when_class_unchanged h objectId
      objectDef updated objectLookup rfl reference).mpr live
  intro candidate candidateDef container candidateLookup containerPayload
  by_cases target : candidate = objectId
  · subst candidate
    have candidateEqual : candidateDef = updated := by
      have installed : some updated = some candidateDef := by
        simpa [installObject] using candidateLookup
      exact (Option.some.inj installed).symm
    subst candidateDef
    have containerEqual : container =
        .weakMap (entries.install key value) := by
      simpa [updated] using (Option.some.inj containerPayload).symm
    subst container
    intro candidateKey candidateValue entryLookup
    by_cases atKey : candidateKey = key
    · subst candidateKey
      have valueEqual : candidateValue = value := by
        simpa using (Option.some.inj
          ((FiniteStore.install_at entries key value).symm.trans entryLookup)).symm
      subst candidateValue
      exact ⟨liveForward key keyLive, liveForward value valueLive⟩
    · have oldLookup : entries candidateKey = some candidateValue := by
        simpa [FiniteStore.install_away entries value atKey] using entryLookup
      have oldValid := valid objectId objectDef (.weakMap entries)
        objectLookup objectPayload candidateKey candidateValue oldLookup
      exact ⟨liveForward candidateKey oldValid.1,
        liveForward candidateValue oldValid.2⟩
  · have oldCandidateLookup : h.objects candidate = some candidateDef := by
      simpa [installObject, target] using candidateLookup
    exact (valid candidate candidateDef container oldCandidateLookup
      containerPayload).transport liveForward

end Heap

/-- Changing only an object's weak payload cannot alter its unconditional
    strong references. -/
@[simp] theorem ordinaryObjectRecordStrongReferences_setWeakContainer
    (objectDef : ObjectDef) (container : Option WeakContainer) :
    ordinaryObjectRecordStrongReferences
      { objectDef with weakContainer := container } =
    ordinaryObjectRecordStrongReferences objectDef := by
  rfl

end Newspeak
