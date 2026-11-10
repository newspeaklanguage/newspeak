import Newspeak.ReflectionHeapUpdates
import Newspeak.PrologLookupCorrespondence

namespace Newspeak

namespace Program

theorem applicationSlots_nodup (application : ClassId) {declarations : List SlotId}
    (distinct : declarations.Nodup) : (applicationSlots application declarations).Nodup := by
  apply List.pairwise_map.mpr
  exact distinct.imp (fun unequal equal =>
    unequal (congrArg PhysicalSlotId.declaration equal))

theorem ownSlots_application {p : Program} {heap : Heap} {application : ClassId}
    {address : PhysicalSlotId} (member : address ∈ p.ownSlots heap application) :
    address.application = application := by
  unfold ownSlots at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
      rfl

theorem layout_application_mem {p : Program} {heap : Heap} {chain : List ClassId}
    {address : PhysicalSlotId} (member : address ∈ p.layoutForChain heap chain) :
    address.application ∈ chain := by
  induction chain with
  | nil => simp [layoutForChain] at member
  | cons application ancestors ih =>
      rcases List.mem_append.mp member with inherited | own
      · exact List.mem_cons_of_mem _ (ih inherited)
      · exact List.mem_cons.mpr (.inl (ownSlots_application own))

/-- Repeated mixins do not cause storage-layout rejection. Only duplicate
    application identities or duplicate declarations within one application
    can collide. This is a structural property, not factory termination. -/
theorem layoutForChain_nodup {p : Program} {heap : Heap} {chain : List ClassId}
    (applicationsDistinct : chain.Nodup)
    (ownDistinct : ∀ application ∈ chain, (p.ownSlots heap application).Nodup) :
    (p.layoutForChain heap chain).Nodup := by
  induction chain with
  | nil => simp [layoutForChain]
  | cons application ancestors ih =>
      have chainDistinct := List.nodup_cons.mp applicationsDistinct
      apply List.nodup_append.mpr
      refine ⟨ih chainDistinct.2 (fun c member => ownDistinct c (by simp [member])),
        ownDistinct application (by simp), ?_⟩
      intro inherited inheritedMember own ownMember equal
      have inheritedClass := layout_application_mem inheritedMember
      have ownClass := ownSlots_application ownMember
      rw [equal, ownClass] at inheritedClass
      exact chainDistinct.1 inheritedClass

/-- Layout validation accepts such a chain. Factory execution is a separate
    computation and can raise an exception instead of returning normally. -/
theorem instanceLayout?_accepts_disjointApplications {p : Program} {heap : Heap}
    {application : ClassId} {chain : List ClassId}
    (chainResult : p.executableClassChain heap application = some chain)
    (applicationsDistinct : chain.Nodup)
    (ownDistinct : ∀ c ∈ chain, (p.ownSlots heap c).Nodup) :
    p.instanceLayout? heap application = some (p.layoutForChain heap chain) := by
  simp [instanceLayout?, chainResult, layoutForChain_nodup applicationsDistinct ownDistinct]

end Program

/-- Application identity is part of the address, independently of mixin identity. -/
theorem physicalSlots_separate_applications {first second : ClassId}
    (different : first ≠ second) (left right : SlotId) :
    (⟨first, left⟩ : PhysicalSlotId) ≠ ⟨second, right⟩ := by
  intro equal
  exact different (congrArg PhysicalSlotId.application equal)

theorem nestedCaches_separate_applications {first second : ClassId}
    (different : first ≠ second) (left right : ClassDeclId) :
    (⟨first, left⟩ : NestedCacheId) ≠ ⟨second, right⟩ := by
  intro equal
  exact different (congrArg NestedCacheId.application equal)

/-- A successful write in one application cannot modify another application's
    cell, even if the declarations (and their source names) are identical. -/
theorem writeObjectSlot_otherApplication {heap updated : Heap}
    {object : ObjectId} {first second : ClassId} {left right : SlotId}
    {value : ObjRef} (different : second ≠ first)
    (write : heap.writeObjectSlot object ⟨first, left⟩ value = some updated) :
    updated.readObjectSlot object ⟨second, right⟩ =
      heap.readObjectSlot object ⟨second, right⟩ := by
  simp [Heap.writeObjectSlot, Option.bind_eq_some_iff] at write
  rcases write with ⟨definition, found, old, _, rfl⟩
  simp [Heap.readObjectSlot, Heap.installObject, found,
    physicalSlots_separate_applications different right left]

namespace ApplicationStorageRegression

private def nilValue : ObjRef := .ordinaryObject ⟨0⟩
private def mixin : MixinDef := {
  declaration := .namedClass ⟨10⟩, methods := FiniteStore.empty _ _,
  ownSlots := [⟨7⟩, ⟨8⟩], nestedDeclarations := [⟨11⟩],
  initializerDeclaration := ⟨10⟩, initializerSelector := ⟨"new"⟩,
  initializerParameters := [], initializerGroups := [], initializerBody := [] }
private def program : Program := {
  top := ⟨0⟩, object := ⟨1⟩, classClass := ⟨9⟩, metaclassClass := ⟨9⟩,
  messageMirrorClass := ⟨9⟩, activationClass := ⟨9⟩, closureClass := ⟨9⟩,
  nilObject := nilValue, mixins := (FiniteStore.empty _ _).install ⟨10⟩ mixin,
  methodBodies := FiniteStore.empty _ _, methodLocals := fun _ => [],
  closureParameters := fun _ => [], closureLocals := fun _ => [],
  closureBodies := FiniteStore.empty _ _, pastFutureExpression := fun _ => .selfValue,
  atoms := fun _ => nilValue, platform := FiniteStore.empty _ _, patternVariable := FiniteStore.empty _ _,
  classBodies := FiniteStore.empty _ _, mixinApplications := FiniteStore.empty _ _,
  objectLiterals := FiniteStore.empty _ _, actorSeeds := FiniteStore.empty _ _,
  classOwner := fun _ => .topOwner, objectLiteralOwner := fun _ => .topOwner,
  declMixin := FiniteStore.empty _ _, lexParent := FiniteStore.empty _ _,
  scopeChain := fun _ => [], declares := fun _ _ => false }
private def classDefinition (parent : ClassId) : ClassDef := {
  mixin := ⟨10⟩, superclass := parent, enclosingObject := nilValue,
  metaclass := ⟨9⟩, origin := .expression (.namedClass ⟨10⟩), primaryFactory := none }
private def heap : Heap := {
  classes := ((FiniteStore.empty _ _).install ⟨1⟩ (classDefinition ⟨0⟩)).install ⟨2⟩ (classDefinition ⟨1⟩),
  objects := FiniteStore.empty _ _, activations := FiniteStore.empty _ _, closures := FiniteStore.empty _ _,
  mirrors := FiniteStore.empty _ _, mixinObjects := FiniteStore.empty _ _, actors := FiniteStore.empty _ _ }
private def layout : List PhysicalSlotId :=
  [⟨⟨1⟩, ⟨7⟩⟩, ⟨⟨1⟩, ⟨8⟩⟩, ⟨⟨2⟩, ⟨7⟩⟩, ⟨⟨2⟩, ⟨8⟩⟩]

-- These are kernel-checked computations, not axioms or expected-failure tests.
example : program.instanceLayout? heap ⟨2⟩ = some layout := by decide
example : program.InstanceLayout heap ⟨2⟩ layout :=
  Program.instanceLayout?_sound (by decide)
example : PrologBridge.PrologInstanceLayout program heap ⟨2⟩ layout :=
  PrologBridge.prologInstanceLayout_iff.mpr
    (Program.instanceLayout?_sound (by decide))

private def cells : FiniteStore PhysicalSlotId ObjRef :=
  (Program.slotsInitializedTo layout nilValue).install ⟨⟨1⟩, ⟨7⟩⟩ (.ordinaryObject ⟨21⟩)
example : cells ⟨⟨1⟩, ⟨7⟩⟩ = some (.ordinaryObject ⟨21⟩) := by decide
example : cells ⟨⟨2⟩, ⟨7⟩⟩ = some nilValue := by decide

private def migrated : FiniteStore PhysicalSlotId ObjRef :=
  FiniteStore.reconcileKeys cells [⟨⟨2⟩, ⟨7⟩⟩, ⟨⟨3⟩, ⟨7⟩⟩] nilValue
example : migrated ⟨⟨1⟩, ⟨7⟩⟩ = none := by decide
example : migrated ⟨⟨2⟩, ⟨7⟩⟩ = some nilValue := by decide
example : migrated ⟨⟨3⟩, ⟨7⟩⟩ = some nilValue := by decide
example : program.nestedKeys? heap ⟨2⟩ = some [⟨⟨1⟩, ⟨11⟩⟩, ⟨⟨2⟩, ⟨11⟩⟩] := by decide

private def cache : FiniteStore NestedCacheId ClassId :=
  ((FiniteStore.empty _ _).install ⟨⟨1⟩, ⟨11⟩⟩ ⟨31⟩).install ⟨⟨2⟩, ⟨11⟩⟩ ⟨32⟩
example : cache ⟨⟨1⟩, ⟨11⟩⟩ = some ⟨31⟩ := by decide
example : cache ⟨⟨2⟩, ⟨11⟩⟩ = some ⟨32⟩ := by decide
example : program.slotSimCode ⟨10⟩ ⟨20⟩ ⟨2⟩ [.immutable ⟨7⟩ .selfValue ⟨10⟩] =
    [.writeSlot ⟨20⟩ ⟨⟨2⟩, ⟨7⟩⟩
      (.ordinarySend .selfValue computingSelector [.closureLiteral ⟨10⟩]),
     .ordinarySend (.readSlot ⟨20⟩ ⟨⟨2⟩, ⟨7⟩⟩) resolveSelector []] := by rfl

private def activation (application : ClassId) : ActivationDef := {
  objectClass := ⟨9⟩, provenance := .initializer ⟨10⟩,
  parameters := FiniteStore.empty _ _, locals := FiniteStore.empty _ _,
  currentReceiver := .ordinaryObject ⟨20⟩, currentClass := some application,
  continuation := none, homeMethod := some ⟨10⟩, continuable := true,
  activationScopes := FiniteStore.empty _ _, objectLiteralScopes := FiniteStore.empty _ _ }
private def activeHeap : Heap :=
  (heap.installObject ⟨20⟩ { classId := ⟨2⟩, slots := cells, nestedClasses := cache }).installActivation ⟨10⟩ (activation ⟨1⟩)
private def allocation : AllocationState := ⟨activeHeap, 40, 40, 40, 40, 40⟩
private def stack : ActivationStack := .push .empty ⟨⟨10⟩, .empty⟩
example : program.ObjectSlotStep
    ⟨allocation, stack, .evaluate (.currentRead ⟨7⟩)⟩
    ⟨allocation, stack, .evaluate (.readSlot ⟨20⟩ ⟨⟨1⟩, ⟨7⟩⟩)⟩ :=
  .currentRead (by rfl) (by rfl) (by rfl)
example : program.ObjectSlotStep
    ⟨allocation, stack, .evaluate (.lazyRead ⟨8⟩ .selfValue)⟩
    ⟨allocation, .push .empty ⟨⟨10⟩, .push .empty (.lazySlotStore ⟨20⟩ ⟨⟨1⟩, ⟨8⟩⟩)⟩,
      .evaluate .selfValue⟩ :=
  .lazyMiss (by rfl) (by rfl) (by rfl) (by decide)
example : program.NestedClassStep
    ⟨allocation, stack, .evaluate (.nestedClass ⟨11⟩ .selfValue)⟩
    ⟨allocation, stack, .object (.classObject ⟨31⟩)⟩ :=
  .hit (by rfl) (by rfl) (by rfl) (by decide)
private def storedAddress : Option SequentialConfig → Option PhysicalSlotId
  | some ⟨_, .push _ ⟨_, .push _ (.storeInitializedSlot _ address _ _ _)⟩, _⟩ => some address
  | _ => none
example : storedAddress (program.slotInitializationNext
    ⟨allocation, stack, .initializeSequentialSlots ⟨20⟩
      [.immutable ⟨7⟩ .selfValue ⟨10⟩] [] []⟩) = some ⟨⟨1⟩, ⟨7⟩⟩ := by decide
example : (program.closureDefinition ⟨10⟩ (activation ⟨1⟩) ⟨12⟩ []).capturedClass =
    some ⟨1⟩ := by rfl

end ApplicationStorageRegression
end Newspeak
