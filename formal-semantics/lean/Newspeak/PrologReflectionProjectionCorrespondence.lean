import Newspeak.ReflectionRuntimePreparation

/-! # Prolog correspondence for reflection-command family projections -/

namespace Newspeak
namespace PrologBridge

inductive PrologReflectionCommandFamily (command : ReflectionCommand) :
    ReflectionCommandKind → Prop where
  | classified : PrologReflectionCommandFamily command command.kind

theorem prologReflectionCommandFamily_iff {command family} :
    PrologReflectionCommandFamily command family ↔ command.kind = family := by
  constructor
  · rintro ⟨⟩
    rfl
  · intro equality
    subst family
    exact .classified

inductive PrologFilterReflectionCommands (family : ReflectionCommandKind) :
    List ReflectionCommand → List ReflectionCommand → Prop where
  | empty : PrologFilterReflectionCommands family [] []
  | keep {command remaining filtered} :
      PrologReflectionCommandFamily command family →
      PrologFilterReflectionCommands family remaining filtered →
      PrologFilterReflectionCommands family (command :: remaining)
        (command :: filtered)
  | skip {command remaining filtered actual} :
      PrologReflectionCommandFamily command actual →
      actual ≠ family →
      PrologFilterReflectionCommands family remaining filtered →
      PrologFilterReflectionCommands family (command :: remaining) filtered

theorem prologFilterReflectionCommands_iff {family commands filtered} :
    PrologFilterReflectionCommands family commands filtered ↔
      commands.filter (fun command => decide (command.kind = family)) =
        filtered := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | keep classifiedProof _ ih =>
        have equality := prologReflectionCommandFamily_iff.mp classifiedProof
        simp [equality, ih]
    | skip classifiedProof different _ ih =>
        have equality := prologReflectionCommandFamily_iff.mp classifiedProof
        simp [equality, different, ih]
  · intro equality
    induction commands generalizing filtered with
    | nil =>
        simp at equality
        subst filtered
        exact .empty
    | cons command remaining ih =>
        by_cases same : command.kind = family
        · simp [same] at equality
          subst filtered
          exact .keep (prologReflectionCommandFamily_iff.mpr same) (ih rfl)
        · simp [same] at equality
          exact .skip .classified same (ih equality)

end PrologBridge
end Newspeak
