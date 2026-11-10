import Newspeak.ReflectionTransactions
import Newspeak.PrologLookupCorrespondence

namespace Newspeak
namespace PrologBridge

inductive PrologPrepareReflection {SourceImage : Type}
    (frontEnd : ReflectionFrontEnd SourceImage)
    (prepareRuntime : ReflectionRuntimePreparation)
    (before : ReflectiveVM SourceImage) (requester : ActorId)
    (transaction : List ReflectionCommand) : ReflectiveVM SourceImage → Prop where
  | prepared {sourceCandidate programCandidate runtimeCandidate} :
      frontEnd.patchSourceCommands before.source (codeCommands transaction) =
        some sourceCandidate →
      frontEnd.reelaborateProgram before.world.program sourceCandidate =
        some programCandidate →
      prepareRuntime programCandidate requester transaction before.world =
        some runtimeCandidate →
      PrologPrepareReflection frontEnd prepareRuntime before requester transaction
        ⟨sourceCandidate,
          { runtimeCandidate with
            program := programCandidate
            programVersion := before.world.programVersion + 1 }⟩

theorem prologPrepareReflection_iff
    {SourceImage : Type} {frontEnd : ReflectionFrontEnd SourceImage}
    {prepareRuntime : ReflectionRuntimePreparation}
    {before after : ReflectiveVM SourceImage} {requester : ActorId}
    {transaction : List ReflectionCommand} :
    PrologPrepareReflection frontEnd prepareRuntime before requester transaction after ↔
      prepareReflection frontEnd prepareRuntime before requester transaction =
        some after := by
  constructor
  · rintro ⟨source, program, runtime⟩
    simp [prepareReflection, source, program, runtime]
  · intro result
    unfold prepareReflection at result
    cases sourceResult : frontEnd.patchSourceCommands before.source
        (codeCommands transaction) with
    | none => simp [sourceResult] at result
    | some source =>
        cases programResult : frontEnd.reelaborateProgram before.world.program source with
        | none => simp [sourceResult, programResult] at result
        | some program =>
            cases runtimeResult : prepareRuntime program requester transaction before.world with
            | none => simp [sourceResult, programResult, runtimeResult] at result
            | some runtime =>
                simp [sourceResult, programResult, runtimeResult] at result
                subst after
                exact .prepared sourceResult programResult runtimeResult

end PrologBridge
end Newspeak
