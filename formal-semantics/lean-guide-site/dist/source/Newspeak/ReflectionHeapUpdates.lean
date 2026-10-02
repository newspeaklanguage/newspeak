import Newspeak.ReflectionCommands
import Newspeak.InstanceAllocation

namespace Newspeak

namespace Program

/-- Fuel-bounded executable counterpart of `ClassChain`.  The extra unit of
    fuel permits the terminal `Top` record even though `Top` has no heap
    class record.  Reflection validation rejects `none`, including cycles and
    dangling superclass links. -/
def classChainWithFuel (p : Program) (h : Heap) : Nat → ClassId → Option (List ClassId)
  | 0, _ => none
  | fuel + 1, classId =>
      if classId = p.top then
        some [p.top]
      else do
        let definition ← h.classes classId
        let ancestors ← p.classChainWithFuel h fuel definition.superclass
        some (classId :: ancestors)

def executableClassChain (p : Program) (h : Heap)
    (classId : ClassId) : Option (List ClassId) :=
  p.classChainWithFuel h (h.classes.domain.length + 1) classId

theorem classChainWithFuel_of_classes_eq (p : Program) {left right : Heap}
    (classesEqual : left.classes = right.classes) (fuel : Nat)
    (classId : ClassId) :
    p.classChainWithFuel left fuel classId =
      p.classChainWithFuel right fuel classId := by
  induction fuel generalizing classId with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [classChainWithFuel]
      by_cases atTop : classId = p.top
      · simp [atTop]
      · simp [atTop, classesEqual, inductionHypothesis]

theorem executableClassChain_of_classes_eq (p : Program) {left right : Heap}
    (classesEqual : left.classes = right.classes) (classId : ClassId) :
    p.executableClassChain left classId =
      p.executableClassChain right classId := by
  unfold executableClassChain
  rw [classesEqual]
  exact p.classChainWithFuel_of_classes_eq classesEqual _ classId

theorem classChainWithFuel_sound {p : Program} {h : Heap} {fuel : Nat}
    {classId : ClassId} {chain : List ClassId}
    (result : p.classChainWithFuel h fuel classId = some chain) :
    p.ClassChain h classId chain := by
  induction fuel generalizing classId chain with
  | zero => simp [classChainWithFuel] at result
  | succ fuel ih =>
      by_cases atTop : classId = p.top
      · subst classId
        simp [classChainWithFuel] at result
        subst chain
        exact .top
      · simp only [classChainWithFuel, atTop, ↓reduceIte] at result
        cases classResult : h.classes classId with
        | none => simp [classResult] at result
        | some definition =>
            simp only [classResult] at result
            cases ancestorResult : p.classChainWithFuel h fuel definition.superclass with
            | none => simp [ancestorResult] at result
            | some ancestors =>
                have result' : classId :: ancestors = chain := by
                  simpa [ancestorResult] using result
                have result := result'
                subst chain
                exact .step atTop (by simp [Program.superclass?, atTop, classResult])
                  (ih ancestorResult)

theorem executableClassChain_sound {p : Program} {h : Heap}
    {classId : ClassId} {chain : List ClassId}
    (result : p.executableClassChain h classId = some chain) :
    p.ClassChain h classId chain :=
  classChainWithFuel_sound result

/-- Executable, validation-aware instance layout. -/
def instanceLayout? (p : Program) (h : Heap)
    (classId : ClassId) : Option (List SlotId) := do
  let chain ← p.executableClassChain h classId
  let layout := p.layoutForChain h chain
  if layout.Nodup then some layout else none

theorem instanceLayout?_of_classes_eq (p : Program) {left right : Heap}
    (classesEqual : left.classes = right.classes) (classId : ClassId) :
    p.instanceLayout? left classId = p.instanceLayout? right classId := by
  unfold instanceLayout?
  rw [p.executableClassChain_of_classes_eq classesEqual classId]
  cases chainResult : p.executableClassChain right classId with
  | none => rfl
  | some chain =>
      have layoutEqual :
          p.layoutForChain left chain = p.layoutForChain right chain :=
        layoutForChain_of_classes_eq classesEqual chain
      simp [layoutEqual]

theorem instanceLayout?_sound {p : Program} {h : Heap}
    {classId : ClassId} {layout : List SlotId}
    (result : p.instanceLayout? h classId = some layout) :
    p.InstanceLayout h classId layout := by
  unfold instanceLayout? at result
  cases chainResult : p.executableClassChain h classId with
  | none => simp [chainResult] at result
  | some chain =>
      simp only [chainResult] at result
      by_cases noDuplicates : (p.layoutForChain h chain).Nodup
      · simp [noDuplicates] at result
        subst layout
        exact ⟨chain, executableClassChain_sound chainResult, rfl, noDuplicates⟩
      · simp [noDuplicates] at result

def ownNestedKeys (p : Program) (h : Heap) (classId : ClassId) : List ClassDeclId :=
  match h.classes classId with
  | none => []
  | some classDefinition =>
      match p.mixins classDefinition.mixin with
      | none => []
      | some mixinDefinition => mixinDefinition.nestedDeclarations

def nestedKeysForChain (p : Program) (h : Heap) : List ClassId → List ClassDeclId
  | [] => []
  | classId :: ancestors =>
      p.nestedKeysForChain h ancestors ++ p.ownNestedKeys h classId

def nestedKeys? (p : Program) (h : Heap)
    (classId : ClassId) : Option (List ClassDeclId) := do
  let chain ← p.executableClassChain h classId
  some (FiniteStore.deduplicated (p.nestedKeysForChain h chain))

theorem LookupEquivalent.classChainWithFuel_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (fuel : Nat) (classId : ClassId) :
    left.classChainWithFuel heap fuel classId =
      right.classChainWithFuel heap fuel classId := by
  induction fuel generalizing classId with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [classChainWithFuel]
      rw [equivalent.top]
      by_cases atTop : classId = right.top
      · simp [atTop]
      · simp [atTop, inductionHypothesis]

theorem LookupEquivalent.executableClassChain_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (classId : ClassId) :
    left.executableClassChain heap classId =
      right.executableClassChain heap classId :=
  equivalent.classChainWithFuel_eq heap (heap.classes.domain.length + 1) classId

theorem LookupEquivalent.ownSlots_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (classId : ClassId) :
    left.ownSlots heap classId = right.ownSlots heap classId := by
  unfold ownSlots
  cases classResult : heap.classes classId with
  | none => rfl
  | some definition => simp [equivalent.mixins definition.mixin]

theorem LookupEquivalent.layoutForChain_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (chain : List ClassId) :
    left.layoutForChain heap chain = right.layoutForChain heap chain := by
  induction chain with
  | nil => rfl
  | cons classId ancestors inductionHypothesis =>
      simp [layoutForChain, inductionHypothesis,
        equivalent.ownSlots_eq heap classId]

theorem LookupEquivalent.instanceLayout?_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (classId : ClassId) :
    left.instanceLayout? heap classId = right.instanceLayout? heap classId := by
  unfold instanceLayout?
  rw [equivalent.executableClassChain_eq heap classId]
  cases chainResult : right.executableClassChain heap classId with
  | none => rfl
  | some chain => simp [equivalent.layoutForChain_eq heap chain]

theorem LookupEquivalent.ownNestedKeys_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (classId : ClassId) :
    left.ownNestedKeys heap classId = right.ownNestedKeys heap classId := by
  unfold ownNestedKeys
  cases classResult : heap.classes classId with
  | none => rfl
  | some definition => simp [equivalent.mixins definition.mixin]

theorem LookupEquivalent.nestedKeysForChain_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (chain : List ClassId) :
    left.nestedKeysForChain heap chain =
      right.nestedKeysForChain heap chain := by
  induction chain with
  | nil => rfl
  | cons classId ancestors inductionHypothesis =>
      simp [nestedKeysForChain, inductionHypothesis,
        equivalent.ownNestedKeys_eq heap classId]

theorem LookupEquivalent.nestedKeys?_eq
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (classId : ClassId) :
    left.nestedKeys? heap classId = right.nestedKeys? heap classId := by
  unfold nestedKeys?
  rw [equivalent.executableClassChain_eq heap classId]
  cases chainResult : right.executableClassChain heap classId with
  | none => rfl
  | some chain => simp [equivalent.nestedKeysForChain_eq heap chain]

end Program

namespace FiniteStore

/-- Boolean list membership used by executable restriction predicates. -/
def containsKey {Key : Type} [DecidableEq Key] : List Key → Key → Bool
  | [], _ => false
  | candidate :: remaining, key =>
      if candidate = key then true else containsKey remaining key

@[simp] theorem containsKey_eq_true_iff {Key : Type} [DecidableEq Key]
    (keys : List Key) (key : Key) :
    containsKey keys key = true ↔ key ∈ keys := by
  induction keys with
  | nil => simp [containsKey]
  | cons candidate remaining ih =>
      by_cases equal : candidate = key
      · subst candidate
        simp [containsKey]
      · simp [containsKey, equal, ih, Ne.symm equal]

/-- Rebuild a slot store over the final physical layout.  Existing values are
    retained; every newly admitted key receives `initial`. -/
def reconcileKeys {Key Value : Type} [DecidableEq Key]
    (old : FiniteStore Key Value) (keys : List Key) (initial : Value) :
    FiniteStore Key Value :=
  { lookup := fun key =>
      if key ∈ keys then some ((old key).getD initial) else none
    domain := deduplicated keys
    domainNodup := deduplicated_nodup keys
    lookupDefinedIffMem := by
      intro key
      simp [mem_deduplicated] }

@[simp] theorem reconcileKeys_domain {Key Value : Type} [DecidableEq Key]
    (old : FiniteStore Key Value) (keys : List Key) (initial : Value) :
    (reconcileKeys old keys initial).domain = deduplicated keys := by
  rfl

theorem reconcileKeys_preserves {Key Value : Type} [DecidableEq Key]
    (old : FiniteStore Key Value) (keys : List Key) (initial value : Value)
    (key : Key) (member : key ∈ keys) (present : old key = some value) :
    reconcileKeys old keys initial key = some value := by
  simp [reconcileKeys, member, present]

theorem reconcileKeys_initializes {Key Value : Type} [DecidableEq Key]
    (old : FiniteStore Key Value) (keys : List Key) (initial : Value)
    (key : Key) (member : key ∈ keys) (absent : old key = none) :
    reconcileKeys old keys initial key = some initial := by
  simp [reconcileKeys, member, absent]

theorem reconcileKeys_removes {Key Value : Type} [DecidableEq Key]
    (old : FiniteStore Key Value) (keys : List Key) (initial : Value)
    (key : Key) (absent : key ∉ keys) :
    reconcileKeys old keys initial key = none := by
  simp [reconcileKeys, absent]

end FiniteStore

namespace Heap

def transformExistingClass (heap : Heap) (classId : ClassId)
    (transform : ClassDef → ClassDef) : Option Heap := do
  let definition ← heap.classes classId
  some (heap.installClass classId (transform definition))

def reflectedSuperclassTransform (superclass : ClassId)
    (definition : ClassDef) : ClassDef :=
  { definition with superclass := superclass }

def reflectedEnclosingObjectTransform (enclosingObject : ObjRef)
    (definition : ClassDef) : ClassDef :=
  { definition with enclosingObject := enclosingObject }

def reflectChangeSuperclass (heap : Heap) (classId superclass : ClassId) :
    Option Heap :=
  heap.transformExistingClass classId (reflectedSuperclassTransform superclass)

def reflectChangeClassEnclosingObject (heap : Heap) (classId : ClassId)
    (enclosingObject : ObjRef) : Option Heap :=
  heap.transformExistingClass classId
    (reflectedEnclosingObjectTransform enclosingObject)

def transformExistingObject (heap : Heap) (object : ObjectId)
    (transform : ObjectDef → ObjectDef) : Option Heap := do
  let definition ← heap.objects object
  some (heap.installObject object (transform definition))

def reflectedObjectClassTransform (classId : ClassId)
    (definition : ObjectDef) : ObjectDef :=
  { definition with classId := classId }

def reflectChangeObjectClass (heap : Heap) (object : ObjectId)
    (classId : ClassId) : Option Heap :=
  heap.transformExistingObject object (reflectedObjectClassTransform classId)

def reconcileObjectLayout (program : Program) (heap : Heap)
    (object : ObjectId) : Option Heap := do
  let definition ← heap.objects object
  let layout ← program.instanceLayout? heap definition.classId
  let reconciled := FiniteStore.reconcileKeys definition.slots layout program.nilObject
  some (heap.installObject object { definition with slots := reconciled })

def reconcileObjectLayouts (program : Program) :
    Heap → List ObjectId → Option Heap
  | heap, [] => some heap
  | heap, object :: remaining => do
      let reconciled ← heap.reconcileObjectLayout program object
      reconcileObjectLayouts program reconciled remaining

def reconcileAllObjectLayouts (program : Program) (heap : Heap) : Option Heap :=
  reconcileObjectLayouts program heap heap.objects.domain

def reconcileNestedCache (program : Program) (heap : Heap)
    (object : ObjectId) : Option Heap := do
  let definition ← heap.objects object
  let keys ← program.nestedKeys? heap definition.classId
  let retained := definition.nestedClasses.retainKeys fun key =>
    FiniteStore.containsKey keys key
  some (heap.installObject object { definition with nestedClasses := retained })

def reconcileNestedCaches (program : Program) :
    Heap → List ObjectId → Option Heap
  | heap, [] => some heap
  | heap, object :: remaining => do
      let reconciled ← heap.reconcileNestedCache program object
      reconcileNestedCaches program reconciled remaining

def reconcileAllNestedCaches (program : Program) (heap : Heap) : Option Heap :=
  reconcileNestedCaches program heap heap.objects.domain

def reflectWriteObjectSlot (program : Program) (heap : Heap)
    (object : ObjectId) (slot : SlotId) (value : ObjRef) : Option Heap := do
  let definition ← heap.objects object
  let layout ← program.instanceLayout? heap definition.classId
  if Program.containsSlot layout slot then
    heap.writeObjectSlot object slot value
  else none

theorem reconcileObjectLayout_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (object : ObjectId) :
    heap.reconcileObjectLayout left object =
      heap.reconcileObjectLayout right object := by
  unfold reconcileObjectLayout
  cases objectResult : heap.objects object with
  | none => rfl
  | some definition =>
      simp [equivalent.instanceLayout?_eq heap definition.classId,
        equivalent.nilObject]

theorem reconcileObjectLayouts_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (objects : List ObjectId) :
    reconcileObjectLayouts left heap objects =
      reconcileObjectLayouts right heap objects := by
  induction objects generalizing heap with
  | nil => rfl
  | cons object remaining inductionHypothesis =>
      simp only [reconcileObjectLayouts]
      rw [reconcileObjectLayout_of_program_lookupEquivalent equivalent heap object]
      cases result : heap.reconcileObjectLayout right object with
      | none => rfl
      | some reconciled => simp [inductionHypothesis]

theorem reconcileAllObjectLayouts_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) :
    heap.reconcileAllObjectLayouts left =
      heap.reconcileAllObjectLayouts right := by
  unfold reconcileAllObjectLayouts
  exact reconcileObjectLayouts_of_program_lookupEquivalent equivalent heap
    heap.objects.domain

theorem reconcileNestedCache_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (object : ObjectId) :
    heap.reconcileNestedCache left object =
      heap.reconcileNestedCache right object := by
  unfold reconcileNestedCache
  cases objectResult : heap.objects object with
  | none => rfl
  | some definition =>
      simp [equivalent.nestedKeys?_eq heap definition.classId]

theorem reconcileNestedCaches_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (objects : List ObjectId) :
    reconcileNestedCaches left heap objects =
      reconcileNestedCaches right heap objects := by
  induction objects generalizing heap with
  | nil => rfl
  | cons object remaining inductionHypothesis =>
      simp only [reconcileNestedCaches]
      rw [reconcileNestedCache_of_program_lookupEquivalent equivalent heap object]
      cases result : heap.reconcileNestedCache right object with
      | none => rfl
      | some reconciled => simp [inductionHypothesis]

theorem reconcileAllNestedCaches_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) :
    heap.reconcileAllNestedCaches left =
      heap.reconcileAllNestedCaches right := by
  unfold reconcileAllNestedCaches
  exact reconcileNestedCaches_of_program_lookupEquivalent equivalent heap
    heap.objects.domain

theorem reflectWriteObjectSlot_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (object : ObjectId) (slot : SlotId) (value : ObjRef) :
    heap.reflectWriteObjectSlot left object slot value =
      heap.reflectWriteObjectSlot right object slot value := by
  unfold reflectWriteObjectSlot
  cases objectResult : heap.objects object with
  | none => rfl
  | some definition =>
      simp [equivalent.instanceLayout?_eq heap definition.classId]

end Heap

def classGraphCommands (commands : List ReflectionCommand) :
    List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .classGraph)

def objectClassCommands (commands : List ReflectionCommand) :
    List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .objectClass)

def objectSlotCommands (commands : List ReflectionCommand) :
    List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .objectSlot)

def applyClassGraphCommand (heap : Heap) : ReflectionCommand → Option Heap
  | .changeSuperclass _ classId superclass =>
      heap.reflectChangeSuperclass classId superclass
  | .changeClassEnclosingObject _ classId enclosingObject =>
      heap.reflectChangeClassEnclosingObject classId enclosingObject
  | _ => none

def applyClassGraphCommandSequence : Heap → List ReflectionCommand → Option Heap
  | heap, [] => some heap
  | heap, command :: remaining => do
      let updated ← applyClassGraphCommand heap command
      applyClassGraphCommandSequence updated remaining

def applyObjectClassCommand (heap : Heap) : ReflectionCommand → Option Heap
  | .changeObjectClass _ object classId =>
      heap.reflectChangeObjectClass object classId
  | _ => none

def applyObjectClassCommandSequence : Heap → List ReflectionCommand → Option Heap
  | heap, [] => some heap
  | heap, command :: remaining => do
      let updated ← applyObjectClassCommand heap command
      applyObjectClassCommandSequence updated remaining

def applyReflectiveObjectSlotCommand (program : Program) (heap : Heap) :
    ReflectionCommand → Option Heap
  | .objectSlotWrite _ object slot value =>
      heap.reflectWriteObjectSlot program object slot value
  | _ => none

theorem applyReflectiveObjectSlotCommand_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (command : ReflectionCommand) :
    applyReflectiveObjectSlotCommand left heap command =
      applyReflectiveObjectSlotCommand right heap command := by
  cases command <;> simp only [applyReflectiveObjectSlotCommand]
  exact Heap.reflectWriteObjectSlot_of_program_lookupEquivalent equivalent
    heap _ _ _

def applyReflectiveObjectSlotCommandSequence (program : Program) :
    Heap → List ReflectionCommand → Option Heap
  | heap, [] => some heap
  | heap, command :: remaining => do
      let updated ← applyReflectiveObjectSlotCommand program heap command
      applyReflectiveObjectSlotCommandSequence program updated remaining

theorem applyReflectiveObjectSlotCommandSequence_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (heap : Heap) (commands : List ReflectionCommand) :
    applyReflectiveObjectSlotCommandSequence left heap commands =
      applyReflectiveObjectSlotCommandSequence right heap commands := by
  induction commands generalizing heap with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyReflectiveObjectSlotCommandSequence]
      rw [applyReflectiveObjectSlotCommand_of_program_lookupEquivalent
        equivalent heap command]
      cases result : applyReflectiveObjectSlotCommand right heap command with
      | none => rfl
      | some updated => simp [inductionHypothesis]

theorem applyClassGraphCommandSequence_nil (heap : Heap) :
    applyClassGraphCommandSequence heap [] = some heap := by rfl

theorem applyObjectClassCommandSequence_nil (heap : Heap) :
    applyObjectClassCommandSequence heap [] = some heap := by rfl

theorem applyReflectiveObjectSlotCommandSequence_nil
    (program : Program) (heap : Heap) :
    applyReflectiveObjectSlotCommandSequence program heap [] = some heap := by rfl

end Newspeak
