import Newspeak.ReflectionActivationUpdates

namespace Newspeak

/-- Executable boundary from debugger frame images back to semantic control.
    The following module fixes every state transition around this boundary;
    a concrete decoder/materializer is supplied by the subsequent stack-image
    refinement layer. -/
abbrev StackTemplateMaterializer :=
  Program → AllocationState → ActivationStack → StackTemplate →
    Option (AllocationState × ActivationStack × ControlTerm)

namespace ActivationStack

def activationIds : ActivationStack → List ActivationId
  | .empty => []
  | .push rest frame => activationIds rest ++ [frame.activation]

def Nonempty : ActivationStack → Prop
  | .empty => False
  | .push _ _ => True

end ActivationStack

namespace ActorWorld

def PauseTokenFrontierFresh (world : ActorWorld) : Prop :=
  ∀ actor config reply event token reason,
    world.runStates actor = some (.pausedTurn config reply event token reason) →
    token.index < world.nextPauseToken

def pauseRunningActor (world : ActorWorld) (actor : ActorId)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) : ActorWorld :=
  let token : PauseTokenId := ⟨world.nextPauseToken⟩
  { world with
    runStates := world.runStates.install actor
      (.pausedTurn config reply event token reason)
    nextPauseToken := world.nextPauseToken + 1 }

def replaceRunningActorConfiguration (world : ActorWorld) (actor : ActorId)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    ActorWorld :=
  world.advanceRunningTurn actor config reply event

def replacePausedActorConfiguration (world : ActorWorld) (actor : ActorId)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) : ActorWorld :=
  let token : PauseTokenId := ⟨world.nextPauseToken⟩
  { world with
    actorAllocations := world.actorAllocations.install actor config.allocation
    runStates := world.runStates.install actor
      (.pausedTurn config reply event token reason)
    nextPauseToken := world.nextPauseToken + 1 }

def resumePausedActorConfiguration (world : ActorWorld) (actor : ActorId)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    ActorWorld :=
  world.advanceRunningTurn actor config reply event

@[simp] theorem pauseRunningActor_token (world : ActorWorld) (actor : ActorId)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) :
    (world.pauseRunningActor actor config reply event reason).runStates actor =
      some (.pausedTurn config reply event ⟨world.nextPauseToken⟩ reason) := by
  simp [pauseRunningActor]

@[simp] theorem pauseRunningActor_advances_frontier (world : ActorWorld)
    (actor : ActorId) (config : SequentialConfig) (reply : PromiseId)
    (event : EventId) (reason : DebuggerStopReason) :
    (world.pauseRunningActor actor config reply event reason).nextPauseToken =
      world.nextPauseToken + 1 := by rfl

@[simp] theorem replacePausedActorConfiguration_token (world : ActorWorld)
    (actor : ActorId) (config : SequentialConfig) (reply : PromiseId)
    (event : EventId) (reason : DebuggerStopReason) :
    (world.replacePausedActorConfiguration actor config reply event reason).runStates
      actor =
      some (.pausedTurn config reply event ⟨world.nextPauseToken⟩ reason) := by
  simp [replacePausedActorConfiguration]

end ActorWorld

/-- Complete debugger phase for one command.  Pausing and paused replacement
    mint fresh tokens.  Resumption installs `runningTurn`, so the next actor
    action is the ordinary full-speed sequential relation. -/
def applyDebuggerCommand (materialize : StackTemplateMaterializer)
    (program : Program) (requester : ActorId) (world : ActorWorld) :
    ReflectionCommand → Option ActorWorld
  | .pauseActor _ actor reason => do
      let state ← world.runStates actor
      match state with
      | .runningTurn config reply event =>
          if requester = actor then none
          else match config.stack with
            | .empty => none
            | .push _ _ => some (world.pauseRunningActor actor config reply event reason)
      | .idle | .pausedTurn .. => none
  | .replaceCurrentActorStack _ actor stackTemplate => do
      if requester = actor then
        let state ← world.runStates actor
        match state with
        | .runningTurn config reply event => do
            let materialized ← materialize program config.allocation config.stack
              stackTemplate
            let (allocation, stack, control) := materialized
            let replacement : SequentialConfig := ⟨allocation, stack, control⟩
            some (world.replaceRunningActorConfiguration actor replacement reply event)
        | .idle | .pausedTurn .. => none
      else none
  | .replacePausedActorStack _ actor token stackTemplate => do
      let state ← world.runStates actor
      match state with
      | .pausedTurn config reply event currentToken reason =>
          if token = currentToken then
            let materialized ← materialize program config.allocation config.stack
              stackTemplate
            let (allocation, stack, control) := materialized
            let replacement : SequentialConfig := ⟨allocation, stack, control⟩
            some (world.replacePausedActorConfiguration actor replacement reply event
              reason)
          else none
      | .idle | .runningTurn .. => none
  | .resumePausedActorAtFullSpeed _ actor token => do
      let state ← world.runStates actor
      match state with
      | .pausedTurn config reply event currentToken _ =>
          if token = currentToken then
            some (world.resumePausedActorConfiguration actor config reply event)
          else none
      | .idle | .runningTurn .. => none
  | .replaceAndResumePausedActorStack _ actor token stackTemplate => do
      let state ← world.runStates actor
      match state with
      | .pausedTurn config reply event currentToken _ =>
          if token = currentToken then
            let materialized ← materialize program config.allocation config.stack
              stackTemplate
            let (allocation, stack, control) := materialized
            let replacement : SequentialConfig := ⟨allocation, stack, control⟩
            some (world.resumePausedActorConfiguration actor replacement reply event)
          else none
      | .idle | .runningTurn .. => none
  | _ => none

def applyDebuggerCommandSequence (materialize : StackTemplateMaterializer)
    (program : Program) (requester : ActorId) :
    ActorWorld → List ReflectionCommand → Option ActorWorld
  | world, [] => some world
  | world, command :: remaining => do
      let updated ← applyDebuggerCommand materialize program requester world command
      applyDebuggerCommandSequence materialize program requester updated remaining

@[simp] theorem applyDebuggerCommandSequence_nil
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) :
    applyDebuggerCommandSequence materialize program requester world [] =
      some world := by rfl

theorem resumePausedActorAtFullSpeed_rejects_wrong_token
    (materialize : StackTemplateMaterializer) (program : Program)
    {requester actor : ActorId} {world : ActorWorld} {mirror : MirrorId}
    {supplied current : PauseTokenId} {config : SequentialConfig}
    {reply : PromiseId} {event : EventId} {reason : DebuggerStopReason}
    (paused : world.runStates actor =
      some (.pausedTurn config reply event current reason))
    (wrong : supplied ≠ current) :
    applyDebuggerCommand materialize program requester world
      (.resumePausedActorAtFullSpeed mirror actor supplied) = none := by
  simp [applyDebuggerCommand, paused, wrong]

theorem resumePausedActorAtFullSpeed_installs_running_turn
    (materialize : StackTemplateMaterializer) (program : Program)
    {requester actor : ActorId} {world after : ActorWorld} {mirror : MirrorId}
    {token : PauseTokenId} {config : SequentialConfig} {reply : PromiseId}
    {event : EventId} {reason : DebuggerStopReason}
    (paused : world.runStates actor =
      some (.pausedTurn config reply event token reason))
    (result : applyDebuggerCommand materialize program requester world
      (.resumePausedActorAtFullSpeed mirror actor token) = some after) :
    after.runStates actor = some (.runningTurn config reply event) := by
  simp [applyDebuggerCommand, paused] at result
  subst after
  simp [ActorWorld.resumePausedActorConfiguration,
    ActorWorld.advanceRunningTurn]

theorem replacePausedActorStack_invalidates_token
    (materialize : StackTemplateMaterializer) (program : Program)
    {requester actor : ActorId} {world after : ActorWorld} {mirror : MirrorId}
    {token : PauseTokenId} {template : StackTemplate}
    {config : SequentialConfig} {reply : PromiseId} {event : EventId}
    {reason : DebuggerStopReason}
    (paused : world.runStates actor =
      some (.pausedTurn config reply event token reason))
    (result : applyDebuggerCommand materialize program requester world
      (.replacePausedActorStack mirror actor token template) = some after) :
    ∃ replacement,
      after.runStates actor = some (.pausedTurn replacement reply event
        ⟨world.nextPauseToken⟩ reason) ∧
      after.nextPauseToken = world.nextPauseToken + 1 := by
  simp only [applyDebuggerCommand, paused] at result
  cases materializedResult : materialize program config.allocation config.stack template with
  | none => simp [materializedResult] at result
  | some materialized =>
      rcases materialized with ⟨allocation, stack, control⟩
      simp [materializedResult] at result
      subst after
      refine ⟨⟨allocation, stack, control⟩, ?_, rfl⟩
      simp [ActorWorld.replacePausedActorConfiguration]

end Newspeak
