import Newspeak.SequentialWellFormed

namespace Newspeak
namespace Program

def ownSlots (p : Program) (h : Heap) (classId : ClassId) : List SlotId :=
  match h.classes classId with
  | none => []
  | some classDef =>
      match p.mixins classDef.mixin with
      | none => []
      | some mixinDef => mixinDef.ownSlots

/-- Root-to-leaf layout for a class chain represented leaf-to-root. -/
def layoutForChain (p : Program) (h : Heap) : List ClassId → List SlotId
  | [] => []
  | classId :: ancestors =>
      p.layoutForChain h ancestors ++ p.ownSlots h classId

def InstanceLayout (p : Program) (h : Heap) (classId : ClassId)
    (slots : List SlotId) : Prop :=
  ∃ chain, p.ClassChain h classId chain ∧
    p.layoutForChain h chain = slots ∧ slots.Nodup

theorem layoutForChain_of_classes_eq {p : Program} {h h' : Heap}
    (classesEq : h'.classes = h.classes) (chain : List ClassId) :
    p.layoutForChain h' chain = p.layoutForChain h chain := by
  induction chain with
  | nil => rfl
  | cons classId ancestors ih =>
      simp [layoutForChain, ownSlots, classesEq, ih]

/-- Instance layouts depend only on the class store.  In particular, method
    activation allocation cannot change the layout later used by Factory-New. -/
theorem InstanceLayout.of_classes_eq {p : Program} {h h' : Heap}
    (classesEq : h'.classes = h.classes) {classId : ClassId}
    {slots : List SlotId} (layout : p.InstanceLayout h classId slots) :
    p.InstanceLayout h' classId slots := by
  rcases layout with ⟨chain, chainWitness, layoutResult, noDuplicates⟩
  refine ⟨chain, classChain_of_classes_eq classesEq chainWitness, ?_,
    noDuplicates⟩
  exact (layoutForChain_of_classes_eq classesEq chain).trans layoutResult

theorem instanceLayout_unique {p : Program} {h : Heap} {classId : ClassId}
    {left right : List SlotId} (leftLayout : p.InstanceLayout h classId left)
    (rightLayout : p.InstanceLayout h classId right) : left = right := by
  rcases leftLayout with ⟨leftChain, leftChainWitness, leftResult, _⟩
  rcases rightLayout with ⟨rightChain, rightChainWitness, rightResult, _⟩
  have chainEqual := ClassChain.unique leftChainWitness rightChainWitness
  subst rightChain
  exact leftResult.symm.trans rightResult

def containsSlot : List SlotId → SlotId → Bool
  | [], _ => false
  | candidate :: remaining, slot =>
      if candidate = slot then true else containsSlot remaining slot

theorem containsSlot_eq_true_iff (layout : List SlotId) (slot : SlotId) :
    containsSlot layout slot = true ↔ slot ∈ layout := by
  induction layout with
  | nil => simp [containsSlot]
  | cons candidate remaining ih =>
      by_cases equal : candidate = slot
      · subst candidate
        simp [containsSlot]
      · simp [containsSlot, equal, ih, Ne.symm equal]

def slotsInitializedTo (layout : List SlotId) (value : ObjRef) :
    FiniteStore SlotId ObjRef :=
  { lookup := fun slot =>
      if containsSlot layout slot then some value else none
    domain := FiniteStore.deduplicated layout
    domainNodup := FiniteStore.deduplicated_nodup layout
    lookupDefinedIffMem := by
      intro slot
      simp [containsSlot_eq_true_iff, FiniteStore.mem_deduplicated] }

@[simp] theorem slotsInitializedTo_domain (layout : List SlotId)
    (value : ObjRef) :
    (slotsInitializedTo layout value).domain =
      FiniteStore.deduplicated layout := by
  rfl

@[simp] theorem mem_slotsInitializedTo_domain_iff (layout : List SlotId)
    (value : ObjRef) (slot : SlotId) :
    slot ∈ (slotsInitializedTo layout value).domain ↔ slot ∈ layout := by
  simp [FiniteStore.mem_deduplicated]

def allocateInstance (_p : Program) (state : AllocationState)
    (classId : ClassId) (layout : List SlotId) (nilObject : ObjRef) :
    AllocationState × ObjectId :=
  let id : ObjectId := ⟨state.nextObject⟩
  let objectDef : ObjectDef :=
    { classId := classId
      slots := slotsInitializedTo layout nilObject
      nestedClasses := FiniteStore.empty ClassDeclId ClassId }
  ({ state with heap := state.heap.installObject id objectDef
                nextObject := state.nextObject + 1 }, id)

@[simp] theorem allocateInstance_reference (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (nilObject : ObjRef) :
    (p.allocateInstance state classId layout nilObject).2 =
      ⟨state.nextObject⟩ := by rfl

@[simp] theorem allocateInstance_installs (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (nilObject : ObjRef) :
    (p.allocateInstance state classId layout nilObject).1.heap.objects
        ⟨state.nextObject⟩ =
      some { classId := classId
             slots := slotsInitializedTo layout nilObject
             nestedClasses := FiniteStore.empty ClassDeclId ClassId } := by
  simp [allocateInstance]

theorem allocatedInstance_slot_iff (p : Program) (state : AllocationState)
    (classId : ClassId) (layout : List SlotId) (nilObject : ObjRef)
    (slot : SlotId) :
    ((p.allocateInstance state classId layout nilObject).1.heap.objects
      ⟨state.nextObject⟩).bind (fun objectDef => objectDef.slots slot) =
      some nilObject ↔ slot ∈ layout := by
  simp [allocateInstance, slotsInitializedTo, containsSlot_eq_true_iff]

theorem allocatedInstance_nested_empty (p : Program) (state : AllocationState)
    (classId : ClassId) (layout : List SlotId) (nilObject : ObjRef)
    (declaration : ClassDeclId) :
    ((p.allocateInstance state classId layout nilObject).1.heap.objects
      ⟨state.nextObject⟩).bind
        (fun objectDef => objectDef.nestedClasses declaration) = none := by
  simp [allocateInstance]

@[simp] theorem allocatedInstance_has_no_weakContainer (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (nilObject : ObjRef) :
    ((p.allocateInstance state classId layout nilObject).1.heap.objects
      ⟨state.nextObject⟩).map ObjectDef.weakContainer = some none := by
  simp [allocateInstance]

theorem allocatedInstance_realizes_layout (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (nilObject : ObjRef) (layoutWitness : p.InstanceLayout state.heap classId layout) :
    (∀ slot,
      ((p.allocateInstance state classId layout nilObject).1.heap.objects
        ⟨state.nextObject⟩).bind (fun objectDef => objectDef.slots slot) =
        some nilObject ↔ slot ∈ layout) ∧ layout.Nodup := by
  constructor
  · intro slot
    exact allocatedInstance_slot_iff p state classId layout nilObject slot
  · rcases layoutWitness with ⟨chain, chainWitness, result, nodup⟩
    exact nodup

theorem allocateInstance_was_fresh (p : Program) {state : AllocationState}
    (fresh : state.ObjectSupplyFresh) (classId : ClassId)
    (layout : List SlotId) (nilObject : ObjRef) :
    state.heap.objects (p.allocateInstance state classId layout nilObject).2 = none :=
  by simpa [allocateInstance] using
    fresh ⟨state.nextObject⟩ (Nat.le_refl _)

theorem allocateInstance_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh) (classId : ClassId)
    (layout : List SlotId) (nilObject : ObjRef) :
    (p.allocateInstance state classId layout nilObject).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id bound
    exact fresh.1 id (by simpa [allocateInstance] using bound)
  · intro id bound
    exact fresh.2.1 id (by simpa [allocateInstance] using bound)
  · intro id bound
    exact fresh.2.2.1 id (by simpa [allocateInstance] using bound)
  · intro id bound
    have later : state.nextObject + 1 ≤ id.index := by
      simpa [allocateInstance] using bound
    have away : id ≠ (⟨state.nextObject⟩ : ObjectId) := by
      intro equal
      have indexEqual := congrArg ObjectId.index equal
      simp at indexEqual
      omega
    rw [show (p.allocateInstance state classId layout nilObject).1.heap =
      state.heap.installObject ⟨state.nextObject⟩
        { classId := classId
          slots := slotsInitializedTo layout nilObject
          nestedClasses := FiniteStore.empty ClassDeclId ClassId } by rfl]
    rw [Heap.installObject_away _ _ away]
    exact fresh.2.2.2.1 id (by omega)
  · intro id bound
    exact fresh.2.2.2.2 id (by simpa [allocateInstance] using bound)

theorem WellFormed.installObject_wellFormed {p : Program} {h : Heap}
    (wf : p.WellFormed h) {id : ObjectId} {objectDef : ObjectDef}
    (objectClassLive : p.IsLiveClass h objectDef.classId) :
    p.WellFormed (h.installObject id objectDef) := by
  have carryLive {classId : ClassId} (live : p.IsLiveClass h classId) :
      p.IsLiveClass (h.installObject id objectDef) classId := by
    simpa [Program.IsLiveClass, Heap.installObject] using live
  apply wf.of_classes_eq (h' := h.installObject id objectDef) rfl
  · intro object classId live
    cases object with
    | ordinaryObject candidate =>
        by_cases atId : candidate = id
        · subst candidate
          simp [Heap.classOf, Heap.installObject] at live
          subst classId
          exact carryLive objectClassLive
        · exact carryLive (wf.objectClassesAreLive (.ordinaryObject candidate)
            classId (by
              simpa [Heap.classOf, Heap.installObject, atId] using live))
    | classObject candidate => exact carryLive (wf.objectClassesAreLive
        (.classObject candidate) classId (by
          simpa [Heap.classOf, Heap.installObject] using live))
    | mixinObject candidate => exact carryLive (wf.objectClassesAreLive
        (.mixinObject candidate) classId (by
          simpa [Heap.classOf, Heap.installObject] using live))
    | activationObject candidate => exact carryLive (wf.objectClassesAreLive
        (.activationObject candidate) classId (by
          simpa [Heap.classOf, Heap.installObject] using live))
    | closureObject candidate => exact carryLive (wf.objectClassesAreLive
        (.closureObject candidate) classId (by
          simpa [Heap.classOf, Heap.installObject] using live))
    | mirrorObject candidate => exact carryLive (wf.objectClassesAreLive
        (.mirrorObject candidate) classId (by
          simpa [Heap.classOf, Heap.installObject] using live))
    | actorObject candidate => exact carryLive (wf.objectClassesAreLive
        (.actorObject candidate) classId (by
          simpa [Heap.classOf, Heap.installObject] using live))
  · intro activationId activation live
    simpa [OptionalClassLive, Program.IsLiveClass, Heap.installObject] using
      wf.activationCurrentClassesAreLive activationId activation
        (by simpa [Heap.installObject] using live)
  · intro closureId closure live
    simpa [OptionalClassLive, Program.IsLiveClass, Heap.installObject] using
      wf.closureCapturedClassesAreLive closureId closure (by
        simpa [Heap.installObject] using live)

theorem allocateInstance_wellFormed (p : Program)
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (classId : ClassId)
    (classLive : p.IsLiveClass state.heap classId) (layout : List SlotId)
    (nilObject : ObjRef) :
    p.WellFormed (p.allocateInstance state classId layout nilObject).1.heap ∧
      (p.allocateInstance state classId layout nilObject).1.SuppliesFresh := by
  constructor
  · apply wf.installObject_wellFormed
    simpa [allocateInstance, Program.IsLiveClass, Heap.installObject] using
      classLive
  · exact p.allocateInstance_preserves_supplies fresh classId layout nilObject

theorem liveOrdinaryObject_has_unique_liveClass {p : Program} {h : Heap}
    (wf : p.WellFormed h) {id : ObjectId} {objectDef : ObjectDef}
    (live : h.objects id = some objectDef) :
    ∃ classId : ClassId,
      (h.classOf (.ordinaryObject id) = some classId ∧
        p.IsLiveClass h classId) ∧
      ∀ otherClass,
        (h.classOf (.ordinaryObject id) = some otherClass ∧
          p.IsLiveClass h otherClass) → otherClass = classId := by
  refine ⟨objectDef.classId, ?_, ?_⟩
  · constructor
    · simp [Heap.classOf, live]
    · exact wf.objectClassesAreLive (.ordinaryObject id) objectDef.classId
        (by simp [Heap.classOf, live])
  · intro classId properties
    have : some objectDef.classId = some classId := by
      simpa [Heap.classOf, live] using properties.1
    exact (Option.some.inj this).symm

end Program
end Newspeak
