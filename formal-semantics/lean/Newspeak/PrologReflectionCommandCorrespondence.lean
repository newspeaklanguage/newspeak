import Newspeak.PrologReflectionCorrespondence

/-! # Prolog correspondence for reflection-command authority projections -/

namespace Newspeak
namespace PrologBridge

/-- The direct Prolog constructor clauses jointly expose these three total
    Lean projections. -/
structure PrologReflectionCommandFields (command : ReflectionCommand)
    (mirror : MirrorId) (target : MirrorTarget) (right : ReflectRight) : Prop where
  mirror_eq : command.mirror = mirror
  target_eq : command.target = target
  right_eq : command.requiredRight = right

theorem prologReflectionCommandFields_iff {command : ReflectionCommand}
    {mirror : MirrorId} {target : MirrorTarget} {right : ReflectRight} :
    PrologReflectionCommandFields command mirror target right ↔
      command.mirror = mirror ∧ command.target = target ∧
        command.requiredRight = right := by
  constructor
  · rintro ⟨mirror, target, right⟩
    exact ⟨mirror, target, right⟩
  · rintro ⟨mirror, target, right⟩
    exact ⟨mirror, target, right⟩

inductive PrologReflectionCommandAuthorized (world : ActorWorld)
    (actor : ActorId) (command : ReflectionCommand) : Prop where
  | authorize {mirror target right} :
      PrologReflectionCommandFields command mirror target right →
      PrologMirrorAuthorizes world actor mirror target right →
      PrologReflectionCommandAuthorized world actor command

theorem prologReflectionCommandAuthorized_iff {world : ActorWorld}
    {actor : ActorId} {command : ReflectionCommand} :
    PrologReflectionCommandAuthorized world actor command ↔
      command.Authorized world actor := by
  constructor
  · rintro ⟨fields, authorized⟩
    rcases fields with ⟨rfl, rfl, rfl⟩
    exact prologMirrorAuthorizes_iff.mp authorized
  · intro authorized
    exact .authorize ⟨rfl, rfl, rfl⟩
      (prologMirrorAuthorizes_iff.mpr authorized)

end PrologBridge
end Newspeak
