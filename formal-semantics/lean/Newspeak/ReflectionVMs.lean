import Newspeak.ReflectionValidation

namespace Newspeak

def ActorWorld.observedProgram (world : ActorWorld) (actor : ActorId) :
    Option Program := do
  let _ ← world.actorAllocations actor
  some world.program

theorem ActorWorld.cohort_observes_one_program
    {world : ActorWorld} {first second : ActorId}
    {firstAllocation secondAllocation : AllocationState}
    (firstLive : world.actorAllocations first = some firstAllocation)
    (secondLive : world.actorAllocations second = some secondAllocation) :
    world.observedProgram first = world.observedProgram second := by
  simp [ActorWorld.observedProgram, firstLive, secondLive]

theorem ActorSequentialStep.uses_installed_program
    {program : Program} {reifier : ErrorReifier program}
    {actor : ActorId} {before after : ActorWorld}
    (step : ActorSequentialStep program reifier actor before after) :
    before.program = program := by
  cases step with
  | advance _ _ programEqual _ _ _ _ => exact programEqual

abbrev VMNetwork (SourceImage : Type) :=
  FiniteStore VMId (ReflectiveVM SourceImage)

/-- A reflection commit/rejection is local to one VM cohort.  The network
    wrapper makes the "other VMs do not change" clause literal store equality. -/
inductive VMReflectionStep {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (validate : ReflectionValidator SourceImage)
    (rejected : ReflectionRejected SourceImage) :
    VMNetwork SourceImage → VMId → VMNetwork SourceImage → Prop where
  | selected {before after : VMNetwork SourceImage} {vm : VMId}
      {localBefore localAfter : ReflectiveVM SourceImage} :
      before vm = some localBefore →
      ReflectionStep frontEnd prepareRuntime validate rejected
        localBefore localAfter →
      after = before.install vm localAfter →
      VMReflectionStep frontEnd prepareRuntime validate rejected before vm after

theorem VMReflectionStep.selected_vm_installed
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {rejected : ReflectionRejected SourceImage}
    {before after : VMNetwork SourceImage} {vm : VMId}
    (step : VMReflectionStep frontEnd prepareRuntime validate rejected
      before vm after) :
    ∃ localBefore localAfter,
      before vm = some localBefore ∧ after vm = some localAfter ∧
      ReflectionStep frontEnd prepareRuntime validate rejected
        localBefore localAfter := by
  cases step with
  | selected live localStep installed =>
      subst after
      exact ⟨_, _, live, by simp, localStep⟩

theorem VMReflectionStep.other_vms_unchanged
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {validate : ReflectionValidator SourceImage}
    {rejected : ReflectionRejected SourceImage}
    {before after : VMNetwork SourceImage} {selected other : VMId}
    (step : VMReflectionStep frontEnd prepareRuntime validate rejected
      before selected after)
    (different : other ≠ selected) :
    after other = before other := by
  cases step with
  | selected live localStep installed =>
      subst after
      exact FiniteStore.install_away _ _ different

end Newspeak
