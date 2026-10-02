import Newspeak.ReflectionHeapUpdates
import Newspeak.Returns

namespace Newspeak

namespace Heap

def reflectedParameterTransform (parameter : ParameterId) (value : ObjRef)
    (definition : ActivationDef) : ActivationDef :=
  { definition with parameters := definition.parameters.install parameter value }

def reflectedLocalTransform (slot : LocalSlotId) (value : ObjRef)
    (definition : ActivationDef) : ActivationDef :=
  { definition with locals := definition.locals.install slot (.value value) }

def transformExistingActivation (heap : Heap) (activation : ActivationId)
    (transform : ActivationDef → ActivationDef) : Option Heap := do
  let definition ← heap.activations activation
  some (heap.installActivation activation (transform definition))

def reflectedCurrentClassTransform (classId : Option ClassId)
    (definition : ActivationDef) : ActivationDef :=
  { definition with currentClass := classId }

def reflectedContinuationTransform (continuation : Option ActivationId)
    (definition : ActivationDef) : ActivationDef :=
  { definition with continuation := continuation }

/-- One local activation-record edit, separated into its executable
    applicability check and record transformer.  This common form makes
    noninterference of parameters, locals, current class, and continuation a
    single algebraic fact. -/
structure ActivationRecordEdit where
  enabled : ActivationDef → Bool
  transform : ActivationDef → ActivationDef

def parameterRecordEdit (parameter : ParameterId) (value : ObjRef) :
    ActivationRecordEdit :=
  { enabled := fun definition => (definition.parameters parameter).isSome
    transform := reflectedParameterTransform parameter value }

def localRecordEdit (slot : LocalSlotId) (value : ObjRef) :
    ActivationRecordEdit :=
  { enabled := fun definition => (definition.locals slot).isSome
    transform := reflectedLocalTransform slot value }

def currentClassRecordEdit (classId : Option ClassId) : ActivationRecordEdit :=
  { enabled := fun _ => true
    transform := reflectedCurrentClassTransform classId }

def continuationRecordEdit (continuation : Option ActivationId) :
    ActivationRecordEdit :=
  { enabled := fun _ => true
    transform := reflectedContinuationTransform continuation }

def applyActivationRecordEdit (heap : Heap) (activation : ActivationId)
    (edit : ActivationRecordEdit) : Option Heap := do
  let definition ← heap.activations activation
  if edit.enabled definition then
    some (heap.installActivation activation (edit.transform definition))
  else none

/-- Reflective parameter mutation is deliberately distinct from base-language
    local writes and is defined only for an existing physical parameter. -/
def reflectWriteActivationParameter (heap : Heap) (activation : ActivationId)
    (parameter : ParameterId) (value : ObjRef) : Option Heap :=
  heap.applyActivationRecordEdit activation (parameterRecordEdit parameter value)

def reflectWriteActivationLocal (heap : Heap) (activation : ActivationId)
    (slot : LocalSlotId) (value : ObjRef) : Option Heap :=
  heap.applyActivationRecordEdit activation (localRecordEdit slot value)

def reflectChangeActivationCurrentClass (heap : Heap)
    (activation : ActivationId) (classId : Option ClassId) : Option Heap :=
  heap.applyActivationRecordEdit activation (currentClassRecordEdit classId)

def reflectChangeActivationContinuation (heap : Heap)
    (activation : ActivationId) (continuation : Option ActivationId) : Option Heap :=
  heap.applyActivationRecordEdit activation
    (continuationRecordEdit continuation)

noncomputable def reflectMakeActivationUncontinuable (heap : Heap)
    (activation : ActivationId) : Option Heap := do
  let _ ← heap.activations activation
  some (heap.markUncontinuable activation)

/-- Retire exactly the named removed stack records.  Unlike non-local return,
    this list has already been computed from the old live stack, so no graph
    closure is needed here. -/
def retireRemovedActivations (heap : Heap) (removed : List ActivationId) : Heap :=
  { heap with activations := heap.activations.mapValues fun activation definition =>
      if FiniteStore.containsKey removed activation then
        markActivationUncontinuable definition
      else definition }

theorem retireRemovedActivations_member (heap : Heap)
    (removed : List ActivationId) (activation : ActivationId)
    (member : activation ∈ removed) :
    (heap.retireRemovedActivations removed).activations activation =
      (heap.activations activation).map markActivationUncontinuable := by
  simp [retireRemovedActivations, FiniteStore.containsKey_eq_true_iff, member]

theorem retireRemovedActivations_makes_uncontinuable (heap : Heap)
    (removed : List ActivationId) (activation : ActivationId)
    (member : activation ∈ removed) {definition : ActivationDef}
    (result : (heap.retireRemovedActivations removed).activations activation =
      some definition) :
    definition.continuable = false := by
  rw [retireRemovedActivations_member heap removed activation member] at result
  cases oldResult : heap.activations activation with
  | none => simp [oldResult] at result
  | some old =>
      simp [oldResult] at result
      subst definition
      rfl

end Heap

def activationCommands (commands : List ReflectionCommand) :
    List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .activation)

def continuationCommands (commands : List ReflectionCommand) :
    List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .continuation)

def debuggerCommands (commands : List ReflectionCommand) :
    List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .debugger)

/-- Decode exactly the four activation commands whose effect is confined to
    one activation record.  Retirement is deliberately absent because it
    changes the continuation graph, not merely one record field. -/
def ordinaryActivationRecordEdit? : ReflectionCommand →
    Option (ActivationId × Heap.ActivationRecordEdit)
  | .activationParameterWrite _ activation parameter value =>
      some (activation, Heap.parameterRecordEdit parameter value)
  | .activationLocalWrite _ activation slot value =>
      some (activation, Heap.localRecordEdit slot value)
  | .changeActivationCurrentClass _ activation classId =>
      some (activation, Heap.currentClassRecordEdit classId)
  | .changeActivationContinuation _ activation continuation =>
      some (activation, Heap.continuationRecordEdit continuation)
  | _ => none

noncomputable def applyActivationCommand (heap : Heap) :
    ReflectionCommand → Option Heap
  | .activationParameterWrite _ activation parameter value =>
      heap.reflectWriteActivationParameter activation parameter value
  | .activationLocalWrite _ activation slot value =>
      heap.reflectWriteActivationLocal activation slot value
  | .changeActivationCurrentClass _ activation classId =>
      heap.reflectChangeActivationCurrentClass activation classId
  | .changeActivationContinuation _ activation continuation =>
      heap.reflectChangeActivationContinuation activation continuation
  | .makeActivationUncontinuable _ activation =>
      heap.reflectMakeActivationUncontinuable activation
  | _ => none

theorem applyActivationCommand_of_ordinary_edit
    (heap : Heap) (command : ReflectionCommand) (activation : ActivationId)
    (edit : Heap.ActivationRecordEdit)
    (decoded : ordinaryActivationRecordEdit? command = some (activation, edit)) :
    applyActivationCommand heap command =
      heap.applyActivationRecordEdit activation edit := by
  cases command <;> simp [ordinaryActivationRecordEdit?] at decoded ⊢
  all_goals rcases decoded with ⟨rfl, rfl⟩
  all_goals rfl

noncomputable def applyActivationCommandSequence :
    Heap → List ReflectionCommand → Option Heap
  | heap, [] => some heap
  | heap, command :: remaining => do
      let updated ← applyActivationCommand heap command
      applyActivationCommandSequence updated remaining

@[simp] theorem applyActivationCommandSequence_nil (heap : Heap) :
    applyActivationCommandSequence heap [] = some heap := by rfl

/-- IDs removed while popping down to `target`, in top-to-bottom order. -/
def discardedActivationsAbove : ActivationStack → ActivationId →
    Option (List ActivationId)
  | .empty, _ => none
  | .push rest frame, target =>
      if frame.activation = target then some []
      else do
        let discarded ← discardedActivationsAbove rest target
        some (frame.activation :: discarded)

theorem discardedActivationsAbove_matches_resume
    {stack resumed : ActivationStack} {target : ActivationId}
    (resume : resumeActivation stack target = some resumed) :
    ∃ discarded, discardedActivationsAbove stack target = some discarded := by
  induction stack with
  | empty => simp [resumeActivation] at resume
  | push rest frame ih =>
      by_cases atTarget : frame.activation = target
      · exact ⟨[], by simp [discardedActivationsAbove, atTarget]⟩
      · simp [resumeActivation, atTarget] at resume
        rcases ih resume with ⟨discarded, result⟩
        exact ⟨frame.activation :: discarded,
          by simp [discardedActivationsAbove, atTarget, result]⟩

/-- Actor-local implementation of reflective continuation transfer.  The
    target remains continuable but its continuation is severed; popped frames
    become uncontinuable while remaining inspectable in the heap. -/
def ActorWorld.applyContinuationTransfer (world : ActorWorld) :
    ReflectionCommand → Option ActorWorld
  | .continueAtActivation _ actor activation value => do
      let state ← world.runStates actor
      match state with
      | .runningTurn config replyPromise triggeringEvent => do
          let target ← config.allocation.heap.activations activation
          if target.continuable then
            let resumed ← resumeActivation config.stack activation
            let discarded ← discardedActivationsAbove config.stack activation
            let retired := config.allocation.heap.retireRemovedActivations discarded
            let severed ← retired.reflectChangeActivationContinuation activation none
            let allocation := { config.allocation with heap := severed }
            let resumedConfig : SequentialConfig :=
              { allocation := allocation
                stack := resumed
                control := .object value }
            some (world.advanceRunningTurn actor resumedConfig replyPromise triggeringEvent)
          else none
      | .idle | .pausedTurn .. => none
  | _ => none

def ActorWorld.applyContinuationTransferSequence :
    ActorWorld → List ReflectionCommand → Option ActorWorld
  | world, [] => some world
  | world, command :: remaining => do
      let updated ← world.applyContinuationTransfer command
      updated.applyContinuationTransferSequence remaining

@[simp] theorem ActorWorld.applyContinuationTransferSequence_nil
    (world : ActorWorld) :
    world.applyContinuationTransferSequence [] = some world := by rfl

theorem ActorWorld.applyContinuationTransfer_sets_object_control
    {world after : ActorWorld} {mirror : MirrorId} {actor : ActorId}
    {activation : ActivationId} {value : ObjRef}
    (result : world.applyContinuationTransfer
      (.continueAtActivation mirror actor activation value) = some after) :
    ∃ config reply event,
      after.runStates actor = some (.runningTurn config reply event) ∧
      config.control = .object value := by
  simp only [ActorWorld.applyContinuationTransfer] at result
  cases stateResult : world.runStates actor with
  | none =>
      rw [stateResult] at result
      contradiction
  | some state =>
      cases state with
      | idle =>
          rw [stateResult] at result
          contradiction
      | pausedTurn config reply event token reason =>
          rw [stateResult] at result
          contradiction
      | runningTurn config reply event =>
          rw [stateResult] at result
          dsimp at result
          cases targetResult : config.allocation.heap.activations activation with
          | none =>
              rw [targetResult] at result
              contradiction
          | some target =>
              rw [targetResult] at result
              dsimp at result
              cases continuable : target.continuable with
              | false =>
                  simp [continuable] at result
              | true =>
                  simp only [continuable, ↓reduceIte] at result
                  cases resumeResult : resumeActivation config.stack activation with
                  | none =>
                      rw [resumeResult] at result
                      contradiction
                  | some resumed =>
                      rw [resumeResult] at result
                      cases discardedResult : discardedActivationsAbove config.stack activation with
                      | none =>
                          rw [discardedResult] at result
                          contradiction
                      | some discarded =>
                          rw [discardedResult] at result
                          dsimp at result
                          cases severedResult :
                              Heap.reflectChangeActivationContinuation
                                (config.allocation.heap.retireRemovedActivations discarded)
                                activation none with
                          | none =>
                              rw [severedResult] at result
                              contradiction
                          | some severed =>
                              rw [severedResult] at result
                              dsimp at result
                              injection result with result
                              subst after
                              let resumedConfig : SequentialConfig :=
                                { allocation := { config.allocation with heap := severed }
                                  stack := resumed
                                  control := .object value }
                              refine ⟨resumedConfig, reply, event, ?_, ?_⟩
                              · simp [ActorWorld.advanceRunningTurn, resumedConfig]
                              · simp [resumedConfig]

end Newspeak
