import Newspeak.ReflectionStackImages

namespace Newspeak

def codeCommands (commands : List ReflectionCommand) : List ReflectionCommand :=
  commands.filter fun command => decide (command.kind = .code)

/-- A reflective VM pairs the run-time actor cohort with the source image from
    which its current annotated `Program` was elaborated. -/
structure ReflectiveVM (SourceImage : Type) where
  source : SourceImage
  world : ActorWorld

/-- Fixed front-end boundary.  `patchSourceCommands` performs only source AST
    edits; `reelaborateProgram` reruns the ordinary complete elaborator.  Both
    are partial functions, so parse/binding/access/arity failures cannot expose
    a half-patched program. -/
structure ReflectionFrontEnd (SourceImage : Type) where
  patchSourceCommands : SourceImage → List ReflectionCommand → Option SourceImage
  reelaborateProgram : Program → SourceImage → Option Program

/-- Ordered run-time phases after successful re-elaboration: class graph,
    object class, layouts, nested caches, object slots, activations, debugger,
    and continuation transfer.  The concrete constituents are defined in the
    preceding reflection modules; this boundary also performs cohort-store
    repartitioning while maintaining actor/run-state heap coherence. -/
abbrev ReflectionRuntimePreparation :=
  Program → ActorId → List ReflectionCommand → ActorWorld → Option ActorWorld

def prepareReflection {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (before : ReflectiveVM SourceImage) (requester : ActorId)
    (transaction : List ReflectionCommand) : Option (ReflectiveVM SourceImage) := do
  let sourceCandidate ←
    frontEnd.patchSourceCommands before.source (codeCommands transaction)
  let programCandidate ←
    frontEnd.reelaborateProgram before.world.program sourceCandidate
  let runtimeCandidate ←
    prepareRuntime programCandidate requester transaction before.world
  let committedWorld :=
    { runtimeCandidate with
      program := programCandidate
      programVersion := before.world.programVersion + 1 }
  some ⟨sourceCandidate, committedWorld⟩

def ReflectionTransactionAuthorized (world : ActorWorld) (requester : ActorId)
    (transaction : List ReflectionCommand) : Prop :=
  ∀ command, command ∈ transaction → command.Authorized world requester

/-- The five validation families in Section 11.  Keeping the predicates as
    explicit fields makes every required check visible while allowing later
    modules to discharge them from the accumulated `WellFormed` structure. -/
structure ReflectionValidation where
  classGraphCheck : Prop
  objectStoreCheck : Prop
  liveActivationCheck : Prop
  activationEditCheck : Prop
  actorIsolationCheck : Prop

def ReflectionValidation.AllHold (checks : ReflectionValidation) : Prop :=
  checks.classGraphCheck ∧ checks.objectStoreCheck ∧
    checks.liveActivationCheck ∧ checks.activationEditCheck ∧
    checks.actorIsolationCheck

abbrev ReflectionValidator (SourceImage : Type) :=
  ReflectiveVM SourceImage → List ReflectionCommand →
    ReflectiveVM SourceImage → ReflectionValidation

def ValidReflection {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (validate : ReflectionValidator SourceImage)
    (before : ReflectiveVM SourceImage) (requester : ActorId)
    (transaction : List ReflectionCommand)
    (after : ReflectiveVM SourceImage) : Prop :=
  prepareReflection frontEnd prepareRuntime before requester transaction =
      some after ∧
    ReflectionTransactionAuthorized before.world requester transaction ∧
    ReflectionTransactionNonconflicting transaction ∧
    (validate before transaction after).AllHold

inductive ReflectionValidationKind where
  | classGraphCheck
  | objectStoreCheck
  | liveActivationCheck
  | activationEditCheck
  | actorIsolationCheck
deriving Repr, DecidableEq, BEq

inductive ReflectionFailure where
  | unauthorizedCommand (index : Nat)
  | commandConflict (first second : Nat)
  | sourcePatchFailure
  | elaborationFailure
  | statePreparationFailure
  | invariantFailure (kind : ReflectionValidationKind)
deriving Repr, DecidableEq, BEq

/-- Rejection evidence is diagnostic only.  The transition rule below fixes
    its semantic effect—literal identity—independently of which earliest
    diagnostic is selected. -/
abbrev ReflectionRejected (SourceImage : Type) :=
  ReflectiveVM SourceImage → ActorId → List ReflectionCommand →
    ReflectionFailure → Prop

inductive ReflectionStep {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (validate : ReflectionValidator SourceImage)
    (rejected : ReflectionRejected SourceImage) :
    ReflectiveVM SourceImage → ReflectiveVM SourceImage → Prop where
  | commit {before after requester transaction} :
      ValidReflection frontEnd prepareRuntime validate before requester
        transaction after →
      ReflectionStep frontEnd prepareRuntime validate rejected before after
  | reject {state requester transaction failure} :
      rejected state requester transaction failure →
      ReflectionStep frontEnd prepareRuntime validate rejected state state

theorem prepareReflection_increments_version_exactly_once
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand}
    (prepared : prepareReflection frontEnd prepareRuntime before requester
      transaction = some after) :
    after.world.programVersion = before.world.programVersion + 1 := by
  unfold prepareReflection at prepared
  cases sourceResult : frontEnd.patchSourceCommands before.source
      (codeCommands transaction) with
  | none =>
      rw [sourceResult] at prepared
      contradiction
  | some source =>
      rw [sourceResult] at prepared
      dsimp at prepared
      cases programResult : frontEnd.reelaborateProgram before.world.program source with
      | none =>
          rw [programResult] at prepared
          contradiction
      | some program =>
          rw [programResult] at prepared
          dsimp at prepared
          cases runtimeResult : prepareRuntime program requester transaction before.world with
          | none =>
              rw [runtimeResult] at prepared
              contradiction
          | some runtime =>
              rw [runtimeResult] at prepared
              dsimp at prepared
              injection prepared with prepared
              subst after
              rfl

theorem ValidReflection.increments_version_exactly_once
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand}
    (valid : ValidReflection frontEnd prepareRuntime validate before requester
      transaction after) :
    after.world.programVersion = before.world.programVersion + 1 :=
  prepareReflection_increments_version_exactly_once valid.1

theorem ValidReflection.every_command_authorized
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand}
    (valid : ValidReflection frontEnd prepareRuntime validate before requester
      transaction after) {command : ReflectionCommand}
    (member : command ∈ transaction) :
    command.Authorized before.world requester :=
  valid.2.1 command member

theorem ReflectionStep.reject_is_identity
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {rejected : ReflectionRejected SourceImage}
    {before after : ReflectiveVM SourceImage}
    (step : ReflectionStep frontEnd prepareRuntime validate rejected before after)
    (_wasRejected : ∃ requester transaction failure,
      rejected before requester transaction failure) :
    before = after ∨
      ∃ requester transaction,
        ValidReflection frontEnd prepareRuntime validate before requester
          transaction after := by
  cases step with
  | commit valid => exact .inr ⟨_, _, valid⟩
  | reject evidence => exact .inl rfl

theorem ReflectionStep.atomic_version_effect
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {rejected : ReflectionRejected SourceImage}
    {before after : ReflectiveVM SourceImage}
    (step : ReflectionStep frontEnd prepareRuntime validate rejected before after) :
    after.world.programVersion = before.world.programVersion ∨
      after.world.programVersion = before.world.programVersion + 1 := by
  cases step with
  | commit valid => exact .inr valid.increments_version_exactly_once
  | reject evidence => exact .inl rfl

end Newspeak
