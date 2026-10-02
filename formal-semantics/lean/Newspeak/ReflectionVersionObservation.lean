import Newspeak.ReflectionVMs

namespace Newspeak

inductive RunControlObservation where
  | idle
  | running (stack : ActivationStack) (control : ControlTerm)
      (reply : PromiseId) (event : EventId)
  | paused (stack : ActivationStack) (control : ControlTerm)
      (reply : PromiseId) (event : EventId) (token : PauseTokenId)
      (reason : DebuggerStopReason)

def ActorRunState.controlObservation : ActorRunState → RunControlObservation
  | .idle => .idle
  | .runningTurn config reply event =>
      .running config.stack config.control reply event
  | .pausedTurn config reply event token reason =>
      .paused config.stack config.control reply event token reason

def ActorWorld.materializedControl (world : ActorWorld) (actor : ActorId) :
    Option RunControlObservation :=
  (world.runStates actor).map ActorRunState.controlObservation

def MaterializedControlPreserved (before after : ActorWorld) : Prop :=
  ∀ actor, after.materializedControl actor = before.materializedControl actor

theorem MaterializedControlPreserved.refl (world : ActorWorld) :
    MaterializedControlPreserved world world := by
  intro actor
  rfl

theorem MaterializedControlPreserved.trans {first second third : ActorWorld}
    (left : MaterializedControlPreserved first second)
    (right : MaterializedControlPreserved second third) :
    MaterializedControlPreserved first third := by
  intro actor
  exact (right actor).trans (left actor)

theorem ActorWorld.replaceActorAllocationCoherently_preserves_control
    (world : ActorWorld) (actor : ActorId) (allocation : AllocationState) :
    MaterializedControlPreserved world
      (world.replaceActorAllocationCoherently actor allocation) := by
  intro candidate
  by_cases same : candidate = actor
  · subst candidate
    cases stateResult : world.runStates actor with
    | none => simp [ActorWorld.materializedControl,
        ActorWorld.replaceActorAllocationCoherently, stateResult]
    | some state =>
        cases state <;>
          simp [ActorWorld.materializedControl,
            ActorWorld.replaceActorAllocationCoherently, stateResult,
            ActorRunState.controlObservation]
  · cases stateResult : world.runStates actor with
    | none => simp [ActorWorld.materializedControl,
        ActorWorld.replaceActorAllocationCoherently, stateResult]
    | some state =>
        cases state <;>
          simp [ActorWorld.materializedControl,
            ActorWorld.replaceActorAllocationCoherently, stateResult, same]

theorem ActorWorld.updateHeapAt_preserves_control
    {world after : ActorWorld} {location : HeapLocation}
    {update : Heap → Option Heap}
    (result : world.updateHeapAt location update = some after) :
    MaterializedControlPreserved world after := by
  cases location with
  | shared =>
      unfold ActorWorld.updateHeapAt at result
      cases heapResult : update world.valueHeap with
      | none => simp [heapResult] at result
      | some heap =>
          simp [heapResult] at result
          subst after
          intro actor
          rfl
  | actor owner =>
      unfold ActorWorld.updateHeapAt at result
      cases allocationResult : world.actorAllocations owner with
      | none => simp [allocationResult] at result
      | some allocation =>
          simp only [allocationResult] at result
          cases heapResult : update allocation.heap with
          | none => simp [heapResult] at result
          | some heap =>
              simp [heapResult] at result
              subst after
              exact world.replaceActorAllocationCoherently_preserves_control
                owner { allocation with heap := heap }

theorem ActorWorld.transformActorHeaps_preserves_control
    {world after : ActorWorld} {transform : Heap → Option Heap}
    {actors : List ActorId}
    (result : world.transformActorHeaps transform actors = some after) :
    MaterializedControlPreserved world after := by
  induction actors generalizing world after with
  | nil =>
      simp [ActorWorld.transformActorHeaps] at result
      subst after
      exact MaterializedControlPreserved.refl world
  | cons actor remaining ih =>
      unfold ActorWorld.transformActorHeaps at result
      cases allocationResult : world.actorAllocations actor with
      | none => simp [allocationResult] at result
      | some allocation =>
          rw [allocationResult] at result
          dsimp at result
          cases heapResult : transform allocation.heap with
          | none => simp [heapResult] at result
          | some heap =>
              rw [heapResult] at result
              dsimp at result
              let updated := world.replaceActorAllocationCoherently actor
                { allocation with heap := heap }
              exact MaterializedControlPreserved.trans
                (world.replaceActorAllocationCoherently_preserves_control actor
                  { allocation with heap := heap })
                (ih result)

theorem ActorWorld.transformEveryHeap_preserves_control
    {world after : ActorWorld} {transform : Heap → Option Heap}
    (result : world.transformEveryHeap transform = some after) :
    MaterializedControlPreserved world after := by
  unfold ActorWorld.transformEveryHeap at result
  cases sharedResult : transform world.valueHeap with
  | none => simp [sharedResult] at result
  | some shared =>
      rw [sharedResult] at result
      dsimp at result
      let updated : ActorWorld := { world with valueHeap := shared }
      exact MaterializedControlPreserved.trans
        (by
          intro actor
          rfl)
        (ActorWorld.transformActorHeaps_preserves_control result)

theorem reconcileEveryObjectLayout_preserves_control
    {program : Program} {before after : ActorWorld}
    (result : reconcileEveryObjectLayout program before = some after) :
    MaterializedControlPreserved before after :=
  ActorWorld.transformEveryHeap_preserves_control result

theorem reconcileEveryNestedCache_preserves_control
    {program : Program} {before after : ActorWorld}
    (result : reconcileEveryNestedCache program before = some after) :
    MaterializedControlPreserved before after :=
  ActorWorld.transformEveryHeap_preserves_control result

def CodeOnlyTransaction (transaction : List ReflectionCommand) : Prop :=
  ∀ command, command ∈ transaction → command.kind = .code

theorem filter_nonCode_empty_of_codeOnly
    {transaction : List ReflectionCommand}
    (onlyCode : CodeOnlyTransaction transaction)
    (kind : ReflectionCommandKind) (notCode : kind ≠ .code) :
    transaction.filter (fun command => decide (command.kind = kind)) = [] := by
  induction transaction with
  | nil => rfl
  | cons command remaining ih =>
      have commandCode : command.kind = .code :=
        onlyCode command (by simp)
      have remainingOnly : CodeOnlyTransaction remaining := by
        intro candidate member
        exact onlyCode candidate (List.mem_cons_of_mem command member)
      cases kind with
      | code => exact (notCode rfl).elim
      | classGraph =>
          simp only [List.filter]
          rw [commandCode]
          change remaining.filter
            (fun command => decide (command.kind = .classGraph)) = []
          exact ih remainingOnly
      | objectClass =>
          simp only [List.filter]
          rw [commandCode]
          change remaining.filter
            (fun command => decide (command.kind = .objectClass)) = []
          exact ih remainingOnly
      | objectSlot =>
          simp only [List.filter]
          rw [commandCode]
          change remaining.filter
            (fun command => decide (command.kind = .objectSlot)) = []
          exact ih remainingOnly
      | activation =>
          simp only [List.filter]
          rw [commandCode]
          change remaining.filter
            (fun command => decide (command.kind = .activation)) = []
          exact ih remainingOnly
      | continuation =>
          simp only [List.filter]
          rw [commandCode]
          change remaining.filter
            (fun command => decide (command.kind = .continuation)) = []
          exact ih remainingOnly
      | debugger =>
          simp only [List.filter]
          rw [commandCode]
          change remaining.filter
            (fun command => decide (command.kind = .debugger)) = []
          exact ih remainingOnly

theorem codeOnly_runtime_projections_empty
    {transaction : List ReflectionCommand}
    (onlyCode : CodeOnlyTransaction transaction) :
    classGraphCommands transaction = [] ∧
    objectClassCommands transaction = [] ∧
    objectSlotCommands transaction = [] ∧
    activationCommands transaction = [] ∧
    debuggerCommands transaction = [] ∧
    continuationCommands transaction = [] := by
  refine ⟨filter_nonCode_empty_of_codeOnly onlyCode .classGraph (by decide),
    filter_nonCode_empty_of_codeOnly onlyCode .objectClass (by decide),
    filter_nonCode_empty_of_codeOnly onlyCode .objectSlot (by decide),
    filter_nonCode_empty_of_codeOnly onlyCode .activation (by decide),
    filter_nonCode_empty_of_codeOnly onlyCode .debugger (by decide),
    filter_nonCode_empty_of_codeOnly onlyCode .continuation (by decide)⟩

theorem prepareReflectionRuntime_codeOnly_preserves_control
    {program : Program} {requester : ActorId}
    {transaction : List ReflectionCommand} {before after : ActorWorld}
    (onlyCode : CodeOnlyTransaction transaction)
    (result : prepareReflectionRuntime program requester transaction before =
      some after) :
    MaterializedControlPreserved before after := by
  rcases codeOnly_runtime_projections_empty onlyCode with
    ⟨classEmpty, objectClassEmpty, slotEmpty, activationEmpty,
      debuggerEmpty, continuationEmpty⟩
  unfold prepareReflectionRuntime at result
  rw [classEmpty, objectClassEmpty, slotEmpty, activationEmpty,
    debuggerEmpty, continuationEmpty] at result
  dsimp [applyCohortClassGraphCommands, applyCohortObjectClassCommands,
    applyCohortObjectSlotCommands, applyCohortActivationCommands,
    applyDebuggerCommandSequence,
    ActorWorld.applyContinuationTransferSequence] at result
  cases layoutResult : reconcileEveryObjectLayout program before with
  | none => simp [layoutResult] at result
  | some layouts =>
      rw [layoutResult] at result
      dsimp at result
      cases nestedResult : reconcileEveryNestedCache program layouts with
      | none => simp [nestedResult] at result
      | some nested =>
          rw [nestedResult] at result
          dsimp at result
          injection result with result
          subst after
          exact MaterializedControlPreserved.trans
            (reconcileEveryObjectLayout_preserves_control layoutResult)
            (reconcileEveryNestedCache_preserves_control nestedResult)

theorem prepareReflection_codeOnly_preserves_materialized_control
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand}
    (onlyCode : CodeOnlyTransaction transaction)
    (result : prepareReflection frontEnd prepareReflectionRuntime before
      requester transaction = some after) :
    MaterializedControlPreserved before.world after.world := by
  unfold prepareReflection at result
  cases sourceResult : frontEnd.patchSourceCommands before.source
      (codeCommands transaction) with
  | none => simp [sourceResult] at result
  | some source =>
      rw [sourceResult] at result
      dsimp at result
      cases programResult : frontEnd.reelaborateProgram before.world.program source with
      | none => simp [programResult] at result
      | some program =>
          rw [programResult] at result
          dsimp at result
          cases runtimeResult : prepareReflectionRuntime program requester transaction
              before.world with
          | none => simp [runtimeResult] at result
          | some runtime =>
              rw [runtimeResult] at result
              dsimp at result
              injection result with result
              subst after
              have preserved : MaterializedControlPreserved before.world runtime :=
                prepareReflectionRuntime_codeOnly_preserves_control
                  onlyCode runtimeResult
              exact preserved

end Newspeak
