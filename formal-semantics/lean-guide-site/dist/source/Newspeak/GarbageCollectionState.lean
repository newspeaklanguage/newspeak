import Newspeak.GarbageCollection
import Newspeak.SequentialWellFormed
import Newspeak.TopLevel

namespace Newspeak

/-- Lift heap collection without changing any monotone identity frontier. -/
def AllocationState.collectGarbage (state : AllocationState)
    (roots : List ObjRef) (nilObject : ObjRef) : AllocationState :=
  { state with heap := state.heap.collectHeap roots nilObject }

@[simp] theorem AllocationState.collectGarbage_nextMirror
    (state : AllocationState) (roots : List ObjRef) (nilObject : ObjRef) :
    (state.collectGarbage roots nilObject).nextMirror = state.nextMirror := by
  rfl

@[simp] theorem AllocationState.collectGarbage_nextActivation
    (state : AllocationState) (roots : List ObjRef) (nilObject : ObjRef) :
    (state.collectGarbage roots nilObject).nextActivation =
      state.nextActivation := by
  rfl

@[simp] theorem AllocationState.collectGarbage_nextClosure
    (state : AllocationState) (roots : List ObjRef) (nilObject : ObjRef) :
    (state.collectGarbage roots nilObject).nextClosure = state.nextClosure := by
  rfl

@[simp] theorem AllocationState.collectGarbage_nextObject
    (state : AllocationState) (roots : List ObjRef) (nilObject : ObjRef) :
    (state.collectGarbage roots nilObject).nextObject = state.nextObject := by
  rfl

@[simp] theorem AllocationState.collectGarbage_nextClass
    (state : AllocationState) (roots : List ObjRef) (nilObject : ObjRef) :
    (state.collectGarbage roots nilObject).nextClass = state.nextClass := by
  rfl

theorem AllocationState.collectGarbage_preserves_supplies
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (roots : List ObjRef) (nilObject : ObjRef) :
    (state.collectGarbage roots nilObject).SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id frontier
    have absent := fresh.1 id frontier
    simp [AllocationState.collectGarbage, Heap.collectHeap,
      Heap.collectHeapAtReachability, absent]
  · intro id frontier
    have absent := fresh.2.1 id frontier
    simp [AllocationState.collectGarbage, Heap.collectHeap,
      Heap.collectHeapAtReachability, absent]
  · intro id frontier
    have absent := fresh.2.2.1 id frontier
    simp [AllocationState.collectGarbage, Heap.collectHeap,
      Heap.collectHeapAtReachability, absent]
  · intro id frontier
    have absent := fresh.2.2.2.1 id frontier
    simp [AllocationState.collectGarbage, Heap.collectHeap,
      Heap.collectHeapAtReachability, absent]
  · intro id frontier
    have absent := fresh.2.2.2.2 id frontier
    simp [AllocationState.collectGarbage, Heap.collectHeap,
      Heap.collectHeapAtReachability, absent]

/-- Lift collection to a sequential configuration.  Stack and current control
    are definitionally unchanged; only the allocation heap is transformed. -/
def SequentialConfig.collectGarbage (config : SequentialConfig)
    (roots : List ObjRef) (nilObject : ObjRef) : SequentialConfig :=
  { config with allocation := config.allocation.collectGarbage roots nilObject }

@[simp] theorem SequentialConfig.collectGarbage_stack
    (config : SequentialConfig) (roots : List ObjRef) (nilObject : ObjRef) :
    (config.collectGarbage roots nilObject).stack = config.stack := by
  rfl

@[simp] theorem SequentialConfig.collectGarbage_control
    (config : SequentialConfig) (roots : List ObjRef) (nilObject : ObjRef) :
    (config.collectGarbage roots nilObject).control = config.control := by
  rfl

theorem SequentialConfig.collectGarbage_preserves_supplies
    {config : SequentialConfig} (fresh : config.allocation.SuppliesFresh)
    (roots : List ObjRef) (nilObject : ObjRef) :
    (config.collectGarbage roots nilObject).allocation.SuppliesFresh :=
  config.allocation.collectGarbage_preserves_supplies fresh roots nilObject

namespace Heap

/-- Collection agrees with the original heap on the runtime class of every
    retained identity. -/
theorem collectHeap_classOf_retained (h : Heap) (roots : List ObjRef)
    (nilObject reference : ObjRef)
    (retained : reference ∈ h.conditionallyReachableReferences roots) :
    (h.collectHeap roots nilObject).classOf reference = h.classOf reference := by
  rw [collectHeap, collectHeapAtReachability_classOf]
  simp [(retainedReference_eq_true_iff _ _).mpr retained]

/-- Unconditional structural observations of every retained record are
    unchanged.  Weak payload changes are deliberately invisible here. -/
theorem collectHeap_recordStrongReferences_retained
    (h : Heap) (roots : List ObjRef) (nilObject reference : ObjRef)
    (retained : reference ∈ h.conditionallyReachableReferences roots) :
    (h.collectHeap roots nilObject).recordStrongReferences reference =
      h.recordStrongReferences reference := by
  have retainedTrue := (retainedReference_eq_true_iff
    (h.conditionallyReachableReferences roots) reference).mpr retained
  cases reference with
  | ordinaryObject id =>
      cases lookup : h.objects id with
      | none =>
          have notLive : ¬h.IsLiveObject (.ordinaryObject id) := by
            simp [IsLiveObject, classOf, lookup]
          exact (notLive
            (h.conditionallyReachableReferences_are_live roots
              (.ordinaryObject id) retained)).elim
      | some objectDef =>
          simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
            lookup, retainedTrue, collectObjectDef]
  | classObject id =>
      simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
        retainedTrue]
  | mixinObject id =>
      simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
        retainedTrue]
  | activationObject id =>
      simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
        retainedTrue]
  | closureObject id =>
      simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
        retainedTrue]
  | mirrorObject id =>
      simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
        retainedTrue]
  | actorObject id =>
      simp [collectHeap, collectHeapAtReachability, recordStrongReferences,
        retainedTrue]

/-- Strong observational equivalence used by the collection stutter rule. -/
def StrongObservationEquivalent (before after : Heap)
    (observable : List ObjRef) : Prop :=
  (∀ reference, reference ∈ observable →
    after.classOf reference = before.classOf reference) ∧
  (∀ reference, reference ∈ observable →
    after.recordStrongReferences reference =
      before.recordStrongReferences reference)

theorem collectHeap_strongObservationEquivalent (h : Heap)
    (roots : List ObjRef) (nilObject : ObjRef) :
    StrongObservationEquivalent h (h.collectHeap roots nilObject)
      (h.conditionallyReachableReferences roots) := by
  constructor
  · intro reference retained
    exact h.collectHeap_classOf_retained roots nilObject reference retained
  · intro reference retained
    exact h.collectHeap_recordStrongReferences_retained
      roots nilObject reference retained

end Heap

namespace Program

/-- Root adequacy currently required for the program/heap invariant: every
    installed runtime class record must occur in the computed closure.  This
    condition can later be weakened to the exact static/reflective class roots
    once the PEG/program root extractor is installed. -/
def CollectionClassRootsAdequate (_p : Program) (h : Heap)
    (roots : List ObjRef) : Prop :=
  ∀ classId classDef, h.classes classId = some classDef →
    (.classObject classId : ObjRef) ∈
      h.conditionallyReachableReferences roots

theorem CollectionClassRootsAdequate.collectHeap_classes_eq
    {p : Program} {h : Heap} {roots : List ObjRef}
    (adequate : p.CollectionClassRootsAdequate h roots)
    (nilObject : ObjRef) :
    (h.collectHeap roots nilObject).classes = h.classes := by
  let reachable := h.conditionallyReachableReferences roots
  change h.classes.retainKeys (fun classId =>
    Heap.retainedReference reachable (.classObject classId)) = h.classes
  apply FiniteStore.retainKeys_eq_self
  intro classId member
  rcases h.classes.exists_value_of_mem_domain member with
    ⟨classDef, classLookup⟩
  exact (Heap.retainedReference_eq_true_iff reachable
    (.classObject classId)).mpr (adequate classId classDef classLookup)

theorem WellFormed.collectHeap_wellFormed {p : Program} {h : Heap}
    (wf : p.WellFormed h) (roots : List ObjRef) (nilObject : ObjRef)
    (adequate : p.CollectionClassRootsAdequate h roots) :
    p.WellFormed (h.collectHeap roots nilObject) := by
  let reachable := h.conditionallyReachableReferences roots
  change p.WellFormed (h.collectHeapAtReachability reachable nilObject)
  have classesEqual :
      (h.collectHeapAtReachability reachable nilObject).classes = h.classes :=
    adequate.collectHeap_classes_eq nilObject
  apply wf.of_classes_eq classesEqual
  · intro object classId collectedClass
    have classEquation := h.collectHeapAtReachability_classOf
      reachable nilObject object
    rw [classEquation] at collectedClass
    cases retained : Heap.retainedReference reachable object with
    | false => simp [retained] at collectedClass
    | true =>
        have oldClass : h.classOf object = some classId := by
          simpa [retained] using collectedClass
        have oldLive := wf.objectClassesAreLive object classId oldClass
        simpa [Program.IsLiveClass, classesEqual] using oldLive
  · intro activationId activation collectedActivation
    have oldActivation : h.activations activationId = some activation := by
      change h.activations.retainKeys (fun id =>
        Heap.retainedReference reachable (.activationObject id)) activationId =
          some activation at collectedActivation
      exact (FiniteStore.retainKeys_lookup_eq_some_iff _ _ _ _).mp
        collectedActivation |>.1
    have oldLive := wf.activationCurrentClassesAreLive
      activationId activation oldActivation
    simpa [OptionalClassLive, Program.IsLiveClass, classesEqual] using oldLive
  · intro closureId closure collectedClosure
    have oldClosure : h.closures closureId = some closure := by
      change h.closures.retainKeys (fun id =>
        Heap.retainedReference reachable (.closureObject id)) closureId =
          some closure at collectedClosure
      exact (FiniteStore.retainKeys_lookup_eq_some_iff _ _ _ _).mp
        collectedClosure |>.1
    have oldLive := wf.closureCapturedClassesAreLive
      closureId closure oldClosure
    simpa [OptionalClassLive, Program.IsLiveClass, classesEqual] using oldLive

end Program

/-- Every activation named by the concrete activation stack is an explicit
    collection root (or is reached from one). -/
def CollectionStackRootsAdequate (h : Heap) (roots : List ObjRef) :
    ActivationStack → Prop
  | .empty => True
  | .push rest frame =>
      CollectionStackRootsAdequate h roots rest ∧
      (.activationObject frame.activation : ObjRef) ∈
        h.conditionallyReachableReferences roots

theorem stackLive_after_collection {h : Heap} {roots : List ObjRef}
    {nilObject : ObjRef} {stack : ActivationStack}
    (live : Program.StackLive h stack)
    (adequate : CollectionStackRootsAdequate h roots stack) :
    Program.StackLive (h.collectHeap roots nilObject) stack := by
  induction stack with
  | empty => trivial
  | push rest frame ih =>
      rcases live with ⟨restLive, activation, activationLive⟩
      rcases adequate with ⟨restAdequate, frameRetained⟩
      refine ⟨ih restLive restAdequate, activation, ?_⟩
      have retainedTrue := (Heap.retainedReference_eq_true_iff
        (h.conditionallyReachableReferences roots)
        (.activationObject frame.activation)).mpr frameRetained
      simp [Heap.collectHeap, Heap.collectHeapAtReachability,
        activationLive, retainedTrue]

theorem Program.SequentialWellFormed.collectGarbage_wellFormed
    {p : Program} {config : SequentialConfig}
    (wf : Program.SequentialWellFormed p config)
    (roots : List ObjRef) (nilObject : ObjRef)
    (classRoots : p.CollectionClassRootsAdequate
      config.allocation.heap roots)
    (stackRoots : CollectionStackRootsAdequate
      config.allocation.heap roots config.stack) :
    Program.SequentialWellFormed p
      (config.collectGarbage roots nilObject) := by
  let h := config.allocation.heap
  have classesEqual :
      (h.collectHeap roots nilObject).classes = h.classes :=
    classRoots.collectHeap_classes_eq nilObject
  refine
    { heap := wf.heap.collectHeap_wellFormed roots nilObject classRoots
      supplies := config.collectGarbage_preserves_supplies
        wf.supplies roots nilObject
      stack := stackLive_after_collection wf.stack stackRoots
      control := ?_ }
  simpa [SequentialConfig.collectGarbage, AllocationState.collectGarbage,
    Program.ControlWellFormed, Program.IsLiveClass, classesEqual, h] using
      wf.control

/-- One optional machine-level collection transition.  Root adequacy is kept
    as an explicit premise because the complete control/PEG root extractor is
    a separate metacircularity obligation. -/
inductive GarbageCollectionStep (roots : List ObjRef) (nilObject : ObjRef) :
    SequentialConfig → SequentialConfig → Prop where
  | collect (before : SequentialConfig) :
      GarbageCollectionStep roots nilObject before
        (before.collectGarbage roots nilObject)

theorem GarbageCollectionStep.preserves_stack_and_control
    {roots : List ObjRef} {nilObject : ObjRef} {before after : SequentialConfig}
    (step : GarbageCollectionStep roots nilObject before after) :
    after.stack = before.stack ∧ after.control = before.control := by
  cases step
  exact ⟨rfl, rfl⟩

theorem GarbageCollectionStep.preserves_supplies
    {roots : List ObjRef} {nilObject : ObjRef} {before after : SequentialConfig}
    (fresh : before.allocation.SuppliesFresh)
    (step : GarbageCollectionStep roots nilObject before after) :
    after.allocation.SuppliesFresh := by
  cases step
  exact before.collectGarbage_preserves_supplies fresh roots nilObject

theorem GarbageCollectionStep.preserves_sequentialWellFormed
    {p : Program} {roots : List ObjRef} {nilObject : ObjRef}
    {before after : SequentialConfig}
    (wf : Program.SequentialWellFormed p before)
    (classRoots : p.CollectionClassRootsAdequate
      before.allocation.heap roots)
    (stackRoots : CollectionStackRootsAdequate
      before.allocation.heap roots before.stack)
    (step : GarbageCollectionStep roots nilObject before after) :
    Program.SequentialWellFormed p after := by
  cases step
  exact wf.collectGarbage_wellFormed roots nilObject classRoots stackRoots

theorem GarbageCollectionStep.establishes_weakContainersWellFormed
    {roots : List ObjRef} {nilObject : ObjRef}
    {before after : SequentialConfig}
    (nilRoot : nilObject ∈ roots)
    (nilLive : before.allocation.heap.IsLiveObject nilObject)
    (step : GarbageCollectionStep roots nilObject before after) :
    after.allocation.heap.WeakContainersWellFormed := by
  cases step
  exact before.allocation.heap.collectHeap_weakContainersWellFormed
    roots nilObject nilRoot nilLive

/-- The ordinary sequential machine enlarged with optional collection.  The
    relation is intentionally nondeterministic: a collector may stutter at
    any safe point, while ordinary language steps remain unchanged. -/
inductive SequentialStepWithCollection (p : Program) (reifier : ErrorReifier p)
    (roots : List ObjRef) (nilObject : ObjRef) :
    SequentialConfig → SequentialConfig → Prop where
  | ordinary {before after : SequentialConfig} :
      p.SequentialStepWithTopLevel reifier before after →
      SequentialStepWithCollection p reifier roots nilObject before after
  | collection {before after : SequentialConfig} :
      GarbageCollectionStep roots nilObject before after →
      SequentialStepWithCollection p reifier roots nilObject before after

/-- State-level observation relation for a GC stutter.  All control state and
    identity frontiers agree literally; retained records agree on class and
    unconditional reference observations.  Weak reads are the only excluded
    observation and may therefore expose clearing/removal. -/
structure CollectionStutter (before after : SequentialConfig)
    (roots : List ObjRef) : Prop where
  stack : after.stack = before.stack
  control : after.control = before.control
  nextMirror : after.allocation.nextMirror = before.allocation.nextMirror
  nextActivation :
    after.allocation.nextActivation = before.allocation.nextActivation
  nextClosure : after.allocation.nextClosure = before.allocation.nextClosure
  nextObject : after.allocation.nextObject = before.allocation.nextObject
  nextClass : after.allocation.nextClass = before.allocation.nextClass
  strongHeap : Heap.StrongObservationEquivalent
    before.allocation.heap after.allocation.heap
    (before.allocation.heap.conditionallyReachableReferences roots)

theorem GarbageCollectionStep.is_collectionStutter
    {roots : List ObjRef} {nilObject : ObjRef} {before after : SequentialConfig}
    (step : GarbageCollectionStep roots nilObject before after) :
    CollectionStutter before after roots := by
  cases step
  exact
    { stack := rfl
      control := rfl
      nextMirror := rfl
      nextActivation := rfl
      nextClosure := rfl
      nextObject := rfl
      nextClass := rfl
      strongHeap := before.allocation.heap.collectHeap_strongObservationEquivalent
        roots nilObject }

/-- M10, one-step form: erasing collection steps yields either the exact base
    transition or a stutter modulo the specified weak observations. -/
theorem SequentialStepWithCollection.refines_base_or_stutters
    {p : Program} {reifier : ErrorReifier p}
    {roots : List ObjRef} {nilObject : ObjRef}
    {before after : SequentialConfig}
    (step : SequentialStepWithCollection p reifier roots nilObject
      before after) :
    p.SequentialStepWithTopLevel reifier before after ∨
      CollectionStutter before after roots := by
  cases step with
  | ordinary ordinary => exact Or.inl ordinary
  | collection collection => exact Or.inr collection.is_collectionStutter

theorem SequentialStepWithCollection.preserves_sequentialWellFormed
    {p : Program} {reifier : ErrorReifier p}
    {roots : List ObjRef} {nilObject : ObjRef}
    {before after : SequentialConfig}
    (wf : Program.SequentialWellFormed p before)
    (classRoots : p.CollectionClassRootsAdequate
      before.allocation.heap roots)
    (stackRoots : CollectionStackRootsAdequate
      before.allocation.heap roots before.stack)
    (step : SequentialStepWithCollection p reifier roots nilObject
      before after) :
    Program.SequentialWellFormed p after := by
  cases step with
  | ordinary ordinary =>
      exact Program.sequentialStepWithTopLevel_preserves_wellFormed wf ordinary
  | collection collection =>
      exact collection.preserves_sequentialWellFormed wf classRoots stackRoots

end Newspeak
