import Newspeak.ClassConstruction

namespace Newspeak
namespace Program

def startMessageEvaluation (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack)
    (template : MessageTemplate) : SequentialConfig :=
  match template.arguments with
  | [] => ⟨state, .push rest ⟨current, frames⟩,
      .messageValue ⟨template.selector, []⟩⟩
  | first :: remaining =>
      ⟨state, .push rest ⟨current,
        .push frames (.messageArguments template.selector [] remaining)⟩,
        .evaluate first⟩

def continueMessageEvaluation (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (selector : Selector) (values : List ObjRef) (remaining : List CoreExpr)
    (value : ObjRef) : SequentialConfig :=
  let accumulated := values ++ [value]
  match remaining with
  | [] => ⟨state, .push rest ⟨current, frames⟩,
      .messageValue ⟨selector, accumulated⟩⟩
  | first :: later =>
      ⟨state, .push rest ⟨current,
        .push frames (.messageArguments selector accumulated later)⟩,
        .evaluate first⟩

/-- Equation (9.10): evaluate only a deferred message's arguments, in source
    order, and produce a reified message value for the initializer
    coordinator. -/
inductive MessageEvaluationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | start {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {template : MessageTemplate} :
      MessageEvaluationStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluateMessage template⟩
        (startMessageEvaluation state rest current frames template)
  | argument {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {selector : Selector}
      {values : List ObjRef} {remaining : List CoreExpr} {value : ObjRef} :
      MessageEvaluationStep p
        ⟨state, .push rest ⟨current,
          .push frames (.messageArguments selector values remaining)⟩,
          .object value⟩
        (continueMessageEvaluation state rest current frames selector values
          remaining value)

theorem messageEvaluationStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.MessageEvaluationStep before after₁)
    (step₂ : p.MessageEvaluationStep before after₂) : after₁ = after₂ := by
  cases step₁ <;> cases step₂ <;> rfl

end Program
end Newspeak
