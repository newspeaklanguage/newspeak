import Newspeak.ReflectionTransactions

namespace Newspeak

def Heap.containsClassId (heap : Heap) (classId : ClassId) : Bool :=
  (heap.classes classId).isSome

def Heap.containsObjectId (heap : Heap) (object : ObjectId) : Bool :=
  (heap.objects object).isSome

def Heap.containsActivationId (heap : Heap) (activation : ActivationId) : Bool :=
  (heap.activations activation).isSome

def ActorWorld.firstActorHeapSatisfying (world : ActorWorld)
    (accept : Heap → Bool) : List ActorId → Option ActorId
  | [] => none
  | actor :: remaining => match world.actorAllocations actor with
      | some allocation =>
          if accept allocation.heap then some actor
          else world.firstActorHeapSatisfying accept remaining
      | none => world.firstActorHeapSatisfying accept remaining

def ActorWorld.locateHeapSatisfying (world : ActorWorld)
    (accept : Heap → Bool) : Option HeapLocation :=
  if accept world.valueHeap then some .shared
  else
    (world.firstActorHeapSatisfying accept
      world.actorAllocations.domain).map .actor

def ActorWorld.locateClassId (world : ActorWorld) (classId : ClassId) :
    Option HeapLocation :=
  world.locateHeapSatisfying fun heap => heap.containsClassId classId

def ActorWorld.locateObjectId (world : ActorWorld) (object : ObjectId) :
    Option HeapLocation :=
  world.locateHeapSatisfying fun heap => heap.containsObjectId object

def ActorWorld.locateActivationId (world : ActorWorld)
    (activation : ActivationId) : Option HeapLocation :=
  world.locateHeapSatisfying fun heap => heap.containsActivationId activation

/-- Install one actor's allocation both in the dormant allocation table and,
    if a turn is live, in the configuration that the scheduler will step. -/
def ActorWorld.replaceActorAllocationCoherently (world : ActorWorld)
    (actor : ActorId) (allocation : AllocationState) : ActorWorld :=
  let runStates := match world.runStates actor with
    | none | some .idle => world.runStates
    | some (.runningTurn config reply event) =>
        world.runStates.install actor
          (.runningTurn { config with allocation := allocation } reply event)
    | some (.pausedTurn config reply event token reason) =>
        world.runStates.install actor
          (.pausedTurn { config with allocation := allocation } reply event token reason)
  { world with
    actorAllocations := world.actorAllocations.install actor allocation
    runStates := runStates }

def ActorWorld.updateHeapAt (world : ActorWorld) (location : HeapLocation)
    (update : Heap → Option Heap) : Option ActorWorld :=
  match location with
  | .shared => do
      let heap ← update world.valueHeap
      some { world with valueHeap := heap }
  | .actor actor => do
      let allocation ← world.actorAllocations actor
      let heap ← update allocation.heap
      some (world.replaceActorAllocationCoherently actor
        { allocation with heap := heap })

theorem ActorWorld.replaceActorAllocationCoherently_table
    (world : ActorWorld) (actor : ActorId) (allocation : AllocationState) :
    (world.replaceActorAllocationCoherently actor allocation).actorAllocations
      actor = some allocation := by
  simp [replaceActorAllocationCoherently]

theorem ActorWorld.replaceActorAllocationCoherently_running
    {world : ActorWorld} {actor : ActorId} {old : SequentialConfig}
    {reply : PromiseId} {event : EventId} (allocation : AllocationState)
    (running : world.runStates actor = some (.runningTurn old reply event)) :
    (world.replaceActorAllocationCoherently actor allocation).runStates actor =
      some (.runningTurn { old with allocation := allocation } reply event) := by
  simp [replaceActorAllocationCoherently, running]

theorem ActorWorld.replaceActorAllocationCoherently_paused
    {world : ActorWorld} {actor : ActorId} {old : SequentialConfig}
    {reply : PromiseId} {event : EventId} {token : PauseTokenId}
    {reason : DebuggerStopReason} (allocation : AllocationState)
    (paused : world.runStates actor =
      some (.pausedTurn old reply event token reason)) :
    (world.replaceActorAllocationCoherently actor allocation).runStates actor =
      some (.pausedTurn { old with allocation := allocation } reply event token
        reason) := by
  simp [replaceActorAllocationCoherently, paused]

def classGraphCommandClass? : ReflectionCommand → Option ClassId
  | .changeSuperclass _ classId _ => some classId
  | .changeClassEnclosingObject _ classId _ => some classId
  | _ => none

def applyCohortClassGraphCommand (world : ActorWorld)
    (command : ReflectionCommand) : Option ActorWorld := do
  let classId ← classGraphCommandClass? command
  let location ← world.locateClassId classId
  world.updateHeapAt location fun heap => applyClassGraphCommand heap command

def applyCohortClassGraphCommands :
    ActorWorld → List ReflectionCommand → Option ActorWorld
  | world, [] => some world
  | world, command :: remaining => do
      let updated ← applyCohortClassGraphCommand world command
      applyCohortClassGraphCommands updated remaining

def objectClassCommandObject? : ReflectionCommand → Option ObjectId
  | .changeObjectClass _ object _ => some object
  | _ => none

def applyCohortObjectClassCommand (world : ActorWorld)
    (command : ReflectionCommand) : Option ActorWorld := do
  let object ← objectClassCommandObject? command
  let location ← world.locateObjectId object
  world.updateHeapAt location fun heap => applyObjectClassCommand heap command

def applyCohortObjectClassCommands :
    ActorWorld → List ReflectionCommand → Option ActorWorld
  | world, [] => some world
  | world, command :: remaining => do
      let updated ← applyCohortObjectClassCommand world command
      applyCohortObjectClassCommands updated remaining

def ActorWorld.transformActorHeaps (world : ActorWorld)
    (transform : Heap → Option Heap) : List ActorId → Option ActorWorld
  | [] => some world
  | actor :: remaining => do
      let allocation ← world.actorAllocations actor
      let heap ← transform allocation.heap
      let updated := world.replaceActorAllocationCoherently actor
        { allocation with heap := heap }
      updated.transformActorHeaps transform remaining

def ActorWorld.transformEveryHeap (world : ActorWorld)
    (transform : Heap → Option Heap) : Option ActorWorld := do
  let shared ← transform world.valueHeap
  let updated := { world with valueHeap := shared }
  updated.transformActorHeaps transform world.actorAllocations.domain

def reconcileEveryObjectLayout (program : Program) (world : ActorWorld) :
    Option ActorWorld :=
  world.transformEveryHeap (Heap.reconcileAllObjectLayouts program)

def reconcileEveryNestedCache (program : Program) (world : ActorWorld) :
    Option ActorWorld :=
  world.transformEveryHeap (Heap.reconcileAllNestedCaches program)

theorem reconcileEveryObjectLayout_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (world : ActorWorld) :
    reconcileEveryObjectLayout left world =
      reconcileEveryObjectLayout right world := by
  have transforms : Heap.reconcileAllObjectLayouts left =
      Heap.reconcileAllObjectLayouts right := by
    funext heap
    exact Heap.reconcileAllObjectLayouts_of_program_lookupEquivalent
      equivalent heap
  simp [reconcileEveryObjectLayout, transforms]

theorem reconcileEveryNestedCache_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (world : ActorWorld) :
    reconcileEveryNestedCache left world =
      reconcileEveryNestedCache right world := by
  have transforms : Heap.reconcileAllNestedCaches left =
      Heap.reconcileAllNestedCaches right := by
    funext heap
    exact Heap.reconcileAllNestedCaches_of_program_lookupEquivalent
      equivalent heap
  simp [reconcileEveryNestedCache, transforms]

def objectSlotCommandObject? : ReflectionCommand → Option ObjectId
  | .objectSlotWrite _ object _ _ => some object
  | _ => none

def applyCohortObjectSlotCommand (program : Program) (world : ActorWorld)
    (command : ReflectionCommand) : Option ActorWorld := do
  let object ← objectSlotCommandObject? command
  let location ← world.locateObjectId object
  world.updateHeapAt location fun heap =>
    applyReflectiveObjectSlotCommand program heap command

theorem applyCohortObjectSlotCommand_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (world : ActorWorld) (command : ReflectionCommand) :
    applyCohortObjectSlotCommand left world command =
      applyCohortObjectSlotCommand right world command := by
  have updates :
      (fun heap => applyReflectiveObjectSlotCommand left heap command) =
        (fun heap => applyReflectiveObjectSlotCommand right heap command) := by
    funext heap
    exact applyReflectiveObjectSlotCommand_of_program_lookupEquivalent
      equivalent heap command
  simp [applyCohortObjectSlotCommand, updates]

def applyCohortObjectSlotCommands (program : Program) :
    ActorWorld → List ReflectionCommand → Option ActorWorld
  | world, [] => some world
  | world, command :: remaining => do
      let updated ← applyCohortObjectSlotCommand program world command
      applyCohortObjectSlotCommands program updated remaining

theorem applyCohortObjectSlotCommands_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (world : ActorWorld) (commands : List ReflectionCommand) :
    applyCohortObjectSlotCommands left world commands =
      applyCohortObjectSlotCommands right world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyCohortObjectSlotCommands]
      rw [applyCohortObjectSlotCommand_of_program_lookupEquivalent
        equivalent world command]
      cases result : applyCohortObjectSlotCommand right world command with
      | none => rfl
      | some updated => simp [inductionHypothesis]

def activationCommandActivation? : ReflectionCommand → Option ActivationId
  | .activationParameterWrite _ activation _ _ => some activation
  | .activationLocalWrite _ activation _ _ => some activation
  | .changeActivationCurrentClass _ activation _ => some activation
  | .changeActivationContinuation _ activation _ => some activation
  | .makeActivationUncontinuable _ activation => some activation
  | _ => none

noncomputable def applyCohortActivationCommand (world : ActorWorld)
    (command : ReflectionCommand) : Option ActorWorld := do
  let activation ← activationCommandActivation? command
  let location ← world.locateActivationId activation
  world.updateHeapAt location fun heap => applyActivationCommand heap command

noncomputable def applyCohortActivationCommands :
    ActorWorld → List ReflectionCommand → Option ActorWorld
  | world, [] => some world
  | world, command :: remaining => do
      let updated ← applyCohortActivationCommand world command
      applyCohortActivationCommands updated remaining

/-- Concrete instance of the ordered run-time preparation boundary. -/
noncomputable def prepareReflectionRuntime : ReflectionRuntimePreparation :=
  fun program requester transaction world => do
    let classUpdated ← applyCohortClassGraphCommands world
      (classGraphCommands transaction)
    let objectClassUpdated ← applyCohortObjectClassCommands classUpdated
      (objectClassCommands transaction)
    let layoutsReconciled ← reconcileEveryObjectLayout program objectClassUpdated
    let cachesReconciled ← reconcileEveryNestedCache program layoutsReconciled
    let slotsUpdated ← applyCohortObjectSlotCommands program cachesReconciled
      (objectSlotCommands transaction)
    let activationsUpdated ← applyCohortActivationCommands slotsUpdated
      (activationCommands transaction)
    let debuggerUpdated ← applyDebuggerCommandSequence materializeStackTemplate
      program requester activationsUpdated (debuggerCommands transaction)
    debuggerUpdated.applyContinuationTransferSequence
      (continuationCommands transaction)

theorem applyDebuggerCommand_materialized_program_irrelevant
    (left right : Program) (requester : ActorId) (world : ActorWorld)
    (command : ReflectionCommand) :
    applyDebuggerCommand materializeStackTemplate left requester world command =
      applyDebuggerCommand materializeStackTemplate right requester world command := by
  cases command <;> simp [applyDebuggerCommand, materializeStackTemplate]

theorem applyDebuggerCommandSequence_materialized_program_irrelevant
    (left right : Program) (requester : ActorId) (world : ActorWorld)
    (commands : List ReflectionCommand) :
    applyDebuggerCommandSequence materializeStackTemplate left requester world commands =
      applyDebuggerCommandSequence materializeStackTemplate right requester world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyDebuggerCommandSequence]
      rw [applyDebuggerCommand_materialized_program_irrelevant left right
        requester world command]
      cases result : applyDebuggerCommand materializeStackTemplate right requester
          world command with
      | none => rfl
      | some updated => simp [inductionHypothesis]

/-- The concrete run-time reflection pipeline observes a `Program` only
    through its semantic projections; finite-store domain order is therefore
    irrelevant to every phase and to failure. -/
theorem prepareReflectionRuntime_of_program_lookupEquivalent
    {left right : Program} (equivalent : left.LookupEquivalent right)
    (requester : ActorId) (transaction : List ReflectionCommand)
    (world : ActorWorld) :
    prepareReflectionRuntime left requester transaction world =
      prepareReflectionRuntime right requester transaction world := by
  unfold prepareReflectionRuntime
  have layouts : reconcileEveryObjectLayout left =
      reconcileEveryObjectLayout right := by
    funext currentWorld
    exact reconcileEveryObjectLayout_of_program_lookupEquivalent equivalent
      currentWorld
  have caches : reconcileEveryNestedCache left =
      reconcileEveryNestedCache right := by
    funext currentWorld
    exact reconcileEveryNestedCache_of_program_lookupEquivalent equivalent
      currentWorld
  have slots : applyCohortObjectSlotCommands left =
      applyCohortObjectSlotCommands right := by
    funext currentWorld commands
    exact applyCohortObjectSlotCommands_of_program_lookupEquivalent equivalent
      currentWorld commands
  have debugger : applyDebuggerCommandSequence materializeStackTemplate left =
      applyDebuggerCommandSequence materializeStackTemplate right := by
    funext currentRequester currentWorld commands
    exact applyDebuggerCommandSequence_materialized_program_irrelevant
      left right currentRequester currentWorld commands
  rw [layouts, caches, slots, debugger]

end Newspeak
