import Newspeak.MethodInvocation

namespace Newspeak

structure PendingSend where
  request : SendRequest
  selector : Selector
  arguments : List CoreExpr
deriving Repr

/-- Equation (8.4), restricted to the four send forms that do not evaluate an
    explicit receiver. -/
def nonOrdinaryRequest : CoreExpr → Option PendingSend
  | .implicitSend selector arguments annotation immediate =>
      some ⟨.implicit annotation immediate, selector, arguments⟩
  | .selfSend selector arguments immediate =>
      some ⟨.self immediate, selector, arguments⟩
  | .outerSend selector arguments target immediate =>
      some ⟨.outer target immediate, selector, arguments⟩
  | .superSend selector arguments =>
      some ⟨.super, selector, arguments⟩
  | _ => none

def startPendingSend (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack)
    (pending : PendingSend) : SequentialConfig :=
  match pending.arguments with
  | [] =>
      ⟨state, .push rest ⟨current, frames⟩,
        .dispatch pending.request ⟨pending.selector, []⟩⟩
  | first :: remaining =>
      ⟨state,
        .push rest ⟨current,
          .push frames (.arguments pending.request pending.selector [] remaining)⟩,
        .evaluate first⟩

def continueReceiver (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (receiver : ObjRef)
    (selector : Selector) (arguments : List CoreExpr) : SequentialConfig :=
  match arguments with
  | [] =>
      ⟨state, .push rest ⟨current, frames⟩,
        .dispatch (.ordinary receiver) ⟨selector, []⟩⟩
  | first :: remaining =>
      ⟨state,
        .push rest ⟨current,
          .push frames (.arguments (.ordinary receiver) selector [] remaining)⟩,
        .evaluate first⟩

def continueEventualReceiver (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (receiver : ObjRef) (selector : Selector) (arguments : List CoreExpr) :
    SequentialConfig :=
  match arguments with
  | [] =>
      ⟨state, .push rest ⟨current, frames⟩,
        .dispatch (.eventual receiver) ⟨selector, []⟩⟩
  | first :: remaining =>
      ⟨state,
        .push rest ⟨current,
          .push frames (.arguments (.eventual receiver) selector [] remaining)⟩,
        .evaluate first⟩

def continueArguments (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (request : SendRequest)
    (selector : Selector) (values : List ObjRef)
    (remaining : List CoreExpr) (value : ObjRef) : SequentialConfig :=
  let accumulated := values ++ [value]
  match remaining with
  | [] =>
      ⟨state, .push rest ⟨current, frames⟩,
        .dispatch request ⟨selector, accumulated⟩⟩
  | first :: later =>
      ⟨state,
        .push rest ⟨current,
          .push frames (.arguments request selector accumulated later)⟩,
        .evaluate first⟩

namespace Program

/-- Send receiver and argument evaluation from Equations (8.3)--(8.7), plus
    the value and self base cases.  The target functions above split empty and
    nonempty lists, making left-to-right order executable. -/
inductive ExpressionOrderStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | value {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjRef} :
      ExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate (.value object)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object object⟩
  | selfValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {activation : ActivationDef}
      (currentActivation : state.heap.activations current = some activation) :
      ExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate .selfValue⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .object activation.currentReceiver⟩
  | ordinaryReceiver {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : CoreExpr}
      {selector : Selector} {arguments : List CoreExpr} :
      ExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.ordinarySend receiver selector arguments)⟩
        ⟨state,
          .push rest ⟨current, .push frames (.receiver selector arguments)⟩,
          .evaluate receiver⟩
  | eventualReceiver {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : CoreExpr}
      {selector : Selector} {arguments : List CoreExpr} :
      ExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.eventualSend receiver selector arguments)⟩
        ⟨state,
          .push rest ⟨current, .push frames (.asyncReceiver selector arguments)⟩,
          .evaluate receiver⟩
  | nonOrdinary {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {expression : CoreExpr}
      {pending : PendingSend}
      (requestData : nonOrdinaryRequest expression = some pending) :
      ExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expression⟩
        (startPendingSend state rest current frames pending)
  | receiverValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : ObjRef}
      {selector : Selector} {arguments : List CoreExpr} :
      ExpressionOrderStep p
        ⟨state,
          .push rest ⟨current, .push frames (.receiver selector arguments)⟩,
          .object receiver⟩
        (continueReceiver state rest current frames receiver selector arguments)
  | eventualReceiverValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : ObjRef}
      {selector : Selector} {arguments : List CoreExpr} :
      ExpressionOrderStep p
        ⟨state,
          .push rest ⟨current,
            .push frames (.asyncReceiver selector arguments)⟩,
          .object receiver⟩
        (continueEventualReceiver state rest current frames receiver selector
          arguments)
  | argumentValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {request : SendRequest}
      {selector : Selector} {values : List ObjRef}
      {remaining : List CoreExpr} {value : ObjRef} :
      ExpressionOrderStep p
        ⟨state,
          .push rest ⟨current,
            .push frames (.arguments request selector values remaining)⟩,
          .object value⟩
        (continueArguments state rest current frames request selector values
          remaining value)

theorem expressionOrderStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ExpressionOrderStep before after₁)
    (step₂ : p.ExpressionOrderStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | value =>
      cases step₂ with
      | value => rfl
      | nonOrdinary requestData =>
          simp [nonOrdinaryRequest] at requestData
  | selfValue activation₁ =>
      cases step₂ with
      | selfValue activation₂ =>
          have hactivation := Option.some.inj
            (activation₁.symm.trans activation₂)
          subst hactivation
          rfl
      | nonOrdinary requestData =>
          simp [nonOrdinaryRequest] at requestData
  | ordinaryReceiver =>
      cases step₂ with
      | ordinaryReceiver => rfl
      | nonOrdinary requestData =>
          simp [nonOrdinaryRequest] at requestData
  | eventualReceiver =>
      cases step₂ with
      | eventualReceiver => rfl
      | nonOrdinary requestData =>
          simp [nonOrdinaryRequest] at requestData
  | nonOrdinary request₁ =>
      cases step₂ with
      | value => simp [nonOrdinaryRequest] at request₁
      | selfValue => simp [nonOrdinaryRequest] at request₁
      | ordinaryReceiver => simp [nonOrdinaryRequest] at request₁
      | eventualReceiver => simp [nonOrdinaryRequest] at request₁
      | nonOrdinary request₂ =>
          have hpending := Option.some.inj (request₁.symm.trans request₂)
          subst hpending
          rfl
  | receiverValue => cases step₂; rfl
  | eventualReceiverValue => cases step₂; rfl
  | argumentValue => cases step₂; rfl

end Program
end Newspeak
