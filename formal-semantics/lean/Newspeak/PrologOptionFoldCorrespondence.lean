import Newspeak.ReflectionSourceImage
import Newspeak.ReflectionRuntimePreparation

namespace Newspeak
namespace PrologBridge

def optionFold {State Command : Type} (step : State → Command → Option State) :
    State → List Command → Option State
  | state, [] => some state
  | state, command :: remaining => do
      let updated ← step state command
      optionFold step updated remaining

inductive PrologOptionFold {State Command : Type}
    (step : State → Command → Option State) :
    State → List Command → State → Prop where
  | empty {state} : PrologOptionFold step state [] state
  | next {state command remaining updated result} :
      step state command = some updated →
      PrologOptionFold step updated remaining result →
      PrologOptionFold step state (command :: remaining) result

theorem prologOptionFold_iff {State Command : Type}
    {step : State → Command → Option State} {state commands result} :
    PrologOptionFold step state commands result ↔
      optionFold step state commands = some result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | next first _ ih => simp [optionFold, first, ih]
  · intro execution
    induction commands generalizing state result with
    | nil =>
        simp [optionFold] at execution
        subst result
        exact .empty
    | cons command remaining ih =>
        cases first : step state command with
        | none => simp [optionFold, first] at execution
        | some updated =>
            exact .next first (ih (by simpa [optionFold, first] using execution))

theorem applySourceCodeCommands_eq_optionFold
    (source : IdentifiedSourceImage) (commands : List ReflectionCommand) :
    source.applySourceCodeCommands commands =
      optionFold IdentifiedSourceImage.patchSourceCodeCommand source commands := by
  induction commands generalizing source with
  | nil => rfl
  | cons command remaining ih =>
      simp only [IdentifiedSourceImage.applySourceCodeCommands, optionFold]
      cases result : source.patchSourceCodeCommand command <;> simp [ih]

theorem applyClassGraphCommandSequence_eq_optionFold
    (heap : Heap) (commands : List ReflectionCommand) :
    applyClassGraphCommandSequence heap commands =
      optionFold applyClassGraphCommand heap commands := by
  induction commands generalizing heap with
  | nil => rfl
  | cons command remaining ih =>
      simp only [applyClassGraphCommandSequence, optionFold]
      cases result : applyClassGraphCommand heap command <;> simp [ih]

theorem applyObjectClassCommandSequence_eq_optionFold
    (heap : Heap) (commands : List ReflectionCommand) :
    applyObjectClassCommandSequence heap commands =
      optionFold applyObjectClassCommand heap commands := by
  induction commands generalizing heap with
  | nil => rfl
  | cons command remaining ih =>
      simp only [applyObjectClassCommandSequence, optionFold]
      cases result : applyObjectClassCommand heap command <;> simp [ih]

theorem applyReflectiveObjectSlotCommandSequence_eq_optionFold
    (program : Program) (heap : Heap) (commands : List ReflectionCommand) :
    applyReflectiveObjectSlotCommandSequence program heap commands =
      optionFold (applyReflectiveObjectSlotCommand program) heap commands := by
  induction commands generalizing heap with
  | nil => rfl
  | cons command remaining ih =>
      simp only [applyReflectiveObjectSlotCommandSequence, optionFold]
      cases result : applyReflectiveObjectSlotCommand program heap command <;>
        simp [ih]

end PrologBridge
end Newspeak
