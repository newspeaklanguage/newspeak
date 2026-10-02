import Newspeak.Bodies

namespace Newspeak

/-- Least set from Equation (8.32): the return target and every activation
    whose continuation (transitively) points into that set. -/
inductive DependentActivation (h : Heap) (target : ActivationId) :
    ActivationId → Prop where
  | target : DependentActivation h target target
  | child {parent child : ActivationId} {activation : ActivationDef} :
      DependentActivation h target parent →
      h.activations child = some activation →
      activation.continuation = some parent →
      DependentActivation h target child

def markActivationUncontinuable (activation : ActivationDef) : ActivationDef :=
  { activation with continuation := none, continuable := false }

/-- Executable pointwise form of `markUncontinuable` over the finite activation
    domain. -/
noncomputable def Heap.markUncontinuable (h : Heap)
    (target : ActivationId) : Heap := by
  classical
  exact { h with
    activations := h.activations.mapValues fun candidate activation =>
      if DependentActivation h target candidate then
        markActivationUncontinuable activation
      else activation }

@[simp] theorem Heap.markUncontinuable_target (h : Heap)
    (target : ActivationId) :
    (h.markUncontinuable target).activations target =
      (h.activations target).map markActivationUncontinuable := by
  classical
  simp [Heap.markUncontinuable, DependentActivation.target]

theorem Heap.markUncontinuable_nonDependent (h : Heap)
    (target candidate : ActivationId)
    (notDependent : ¬DependentActivation h target candidate) :
    (h.markUncontinuable target).activations candidate =
      h.activations candidate := by
  classical
  simp [Heap.markUncontinuable, notDependent]

theorem Heap.markUncontinuable_dependent (h : Heap)
    (target candidate : ActivationId)
    (dependent : DependentActivation h target candidate) :
    (h.markUncontinuable target).activations candidate =
      (h.activations candidate).map markActivationUncontinuable := by
  classical
  simp [Heap.markUncontinuable, dependent]

theorem Heap.markUncontinuable_clears_target (h : Heap)
    {target : ActivationId} {activation : ActivationDef}
    (live : h.activations target = some activation) :
    (h.markUncontinuable target).activations target =
      some (markActivationUncontinuable activation) := by
  simp [live]

/-- Equation (8.31), extended to initializers: method and initializer home
    activations return from themselves; closures return from the home
    activation captured in their activation record. -/
def Heap.returnTarget (h : Heap) (current : ActivationId) :
    Option ActivationId := do
  let activation ← h.activations current
  match activation.provenance with
  | .top => none
  | .method _ => some current
  | .closure _ => activation.homeMethod
  | .initializer _ => some current

namespace Program

/-- Return-frame handling and local/non-local transfer (Equations 8.29,
    8.34, and 8.35). -/
noncomputable def returnMachineNext (_p : Program) (config : SequentialConfig) :
    Option SequentialConfig :=
  match config.stack with
  | .empty => none
  | .push rest currentFrame =>
      let state := config.allocation
      let current := currentFrame.activation
      match config.control with
      | .object value =>
          match currentFrame.frames with
          | .push below .returnFrame =>
              match state.heap.returnTarget current with
              | none => none
              | some target =>
                  some ⟨state, .push rest ⟨current, below⟩,
                    .transfer target value⟩
          | _ => none
      | .transfer target value =>
          match state.heap.returnTarget current with
          | none => none
          | some expectedTarget =>
              if target ≠ expectedTarget then none
              else
                match state.heap.activations target with
                | none => none
                | some targetActivation =>
                    let marked := state.heap.markUncontinuable target
                    let markedState := {state with heap := marked}
                    if targetActivation.continuable then
                      match targetActivation.continuation with
                      | some continuation =>
                          match resumeActivation (.push rest currentFrame)
                              continuation with
                          | some resumed =>
                              some ⟨markedState, resumed, .object value⟩
                          | none => none
                      | none =>
                          some ⟨markedState, .push rest currentFrame,
                            .throw .cannotReturn⟩
                    else
                      some ⟨markedState, .push rest currentFrame,
                        .throw .cannotReturn⟩
      | _ => none

inductive ReturnMachineStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | graph {before after : SequentialConfig}
      (next : p.returnMachineNext before = some after) :
      ReturnMachineStep p before after

theorem returnMachineStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ReturnMachineStep before after₁)
    (step₂ : p.ReturnMachineStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | graph next₁ =>
      cases step₂ with
      | graph next₂ =>
          exact Option.some.inj (next₁.symm.trans next₂)

end Program
end Newspeak
