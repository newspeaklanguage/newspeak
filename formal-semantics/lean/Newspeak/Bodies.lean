import Newspeak.ExpressionOrder

namespace Newspeak

def eagerLocalInitializer : LocalDeclaration → Option (LocalSlotId × CoreExpr)
  | .immutable slot initializer => some (slot, initializer)
  | .mutableInitialized slot initializer => some (slot, initializer)
  | _ => none

def nilInitializedLocal : LocalDeclaration → Option LocalSlotId
  | .mutableUninitialized slot => some slot
  | .lazyImmutable slot _ => some slot
  | .lazyMutable slot _ => some slot
  | _ => none

def computingSelector : Selector := ⟨"computing:"⟩
def resolveSelector : Selector := ⟨"resolve"⟩

def Program.localInstallExpression (p : Program) (activation : ActivationId) :
    LocalDeclaration → CoreExpr
  | .immutable slot initializer
  | .mutableInitialized slot initializer =>
      .writeLocal activation slot
        (.ordinarySend (p.pastFutureExpression activation) computingSelector
          [initializer])
  | .mutableUninitialized slot
  | .lazyImmutable slot _
  | .lazyMutable slot _ =>
      .writeLocal activation slot (.value p.nilObject)

def localResolveExpression (activation : ActivationId)
    (declaration : LocalDeclaration) : Option CoreExpr :=
  match eagerLocalInitializer declaration with
  | some (slot, _) =>
      some (.ordinarySend (.readLocal activation slot) resolveSelector [])
  | none => none

/-- Equation (8.22): install every future/nil first, then resolve eager
    declarations in source order. -/
def Program.localSimCode (p : Program) (activation : ActivationId)
    (declarations : List LocalDeclaration) : List CoreExpr :=
  declarations.map (p.localInstallExpression activation) ++
    declarations.filterMap (localResolveExpression activation)

theorem Program.localSimCode_installationPrefix (p : Program)
    (activation : ActivationId) (declarations : List LocalDeclaration) :
    (p.localSimCode activation declarations).take declarations.length =
      declarations.map (p.localInstallExpression activation) := by
  simp [localSimCode]

def startSimultaneousLocals (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (activation : ActivationId) (declarations : List LocalDeclaration)
    (remaining : List LocalDeclarationGroup) (body : List Statement)
    (target : InitializationTarget) : SequentialConfig :=
  match p.localSimCode activation declarations with
  | [] =>
      ⟨state, .push rest ⟨current, frames⟩,
        .initialize activation remaining body target⟩
  | first :: later =>
      ⟨state,
        .push rest ⟨current,
          .push frames (.simultaneousLocals later activation remaining body target)⟩,
        .evaluate first⟩

def emptyBodyResult (p : Program) : InitializationTarget → ObjRef
  | .methodBody receiver => receiver
  | .closureBody => p.nilObject

def lastBodyResult : InitializationTarget → ObjRef → ObjRef
  | .methodBody receiver, _ => receiver
  | .closureBody, value => value

def startStatement (frames : EvalStack) : Statement → EvalStack × CoreExpr
  | .expression expression => (frames, expression)
  | .return expression => (.push frames .returnFrame, expression)

def resumeActivation : ActivationStack → ActivationId → Option ActivationStack
  | .empty, _ => none
  | .push rest frame, target =>
      if frame.activation = target then some (.push rest frame)
      else resumeActivation rest target

namespace Program

/-- Executable graph of local initialization, local primitives, body
    sequencing, and ordinary completion (Equations 8.14--8.30). -/
def bodyMachineNext (p : Program) (config : SequentialConfig) :
    Option SequentialConfig :=
  match config.stack with
  | .empty => none
  | .push rest currentFrame =>
      let state := config.allocation
      let current := currentFrame.activation
      let frames := currentFrame.frames
      match config.control with
      | .initialize activation groups body target =>
          if activation ≠ current then none
          else
            match groups with
            | [] =>
                some ⟨state, .push rest ⟨current, frames⟩, .body target body⟩
            | .sequential declaration :: remaining =>
                match eagerLocalInitializer declaration with
                | some (slot, initializer) =>
                    some ⟨state,
                      .push rest ⟨current,
                        .push frames (.initializeLocal slot remaining body target)⟩,
                      .evaluate initializer⟩
                | none =>
                    match nilInitializedLocal declaration with
                    | none => none
                    | some slot =>
                        match state.heap.writeActivationLocal activation slot
                            p.nilObject with
                        | none => none
                        | some heap =>
                            some ⟨{state with heap := heap},
                              .push rest ⟨current, frames⟩,
                              .initialize activation remaining body target⟩
            | .simultaneous declarations :: remaining =>
                some (startSimultaneousLocals p state rest current frames
                  activation declarations remaining body target)
      | .evaluate (.readLocal activation slot) =>
          match state.heap.readActivationLocal activation slot with
          | none => none
          | some value =>
              some ⟨state, .push rest ⟨current, frames⟩, .object value⟩
      | .evaluate (.writeLocal activation slot expression) =>
          some ⟨state,
            .push rest ⟨current, .push frames (.localWrite activation slot)⟩,
            .evaluate expression⟩
      | .object value =>
          match frames with
          | .push below (.initializeLocal slot remaining body target) =>
              match state.heap.writeActivationLocal current slot value with
              | none => none
              | some heap =>
                  some ⟨{state with heap := heap},
                    .push rest ⟨current, below⟩,
                    .initialize current remaining body target⟩
          | .push below (.localWrite activation slot) =>
              match state.heap.writeActivationLocal activation slot value with
              | none => none
              | some heap =>
                  some ⟨{state with heap := heap},
                    .push rest ⟨current, below⟩, .object value⟩
          | .push below (.simultaneousLocals code activation remaining body target) =>
              match code with
              | [] =>
                  some ⟨state, .push rest ⟨current, below⟩,
                    .initialize activation remaining body target⟩
              | first :: later =>
                  some ⟨state,
                    .push rest ⟨current,
                      .push below (.simultaneousLocals later activation remaining
                        body target)⟩,
                    .evaluate first⟩
          | .push below (.sequence target remaining) =>
              match remaining with
              | [] =>
                  some ⟨state, .push rest ⟨current, below⟩,
                    .finish (lastBodyResult target value)⟩
              | statement :: later =>
                  let started := startStatement (.push below (.sequence target later))
                    statement
                  some ⟨state, .push rest ⟨current, started.1⟩,
                    .evaluate started.2⟩
          | _ => none
      | .body target statements =>
          match statements with
          | [] =>
              some ⟨state, .push rest ⟨current, frames⟩,
                .finish (emptyBodyResult p target)⟩
          | statement :: remaining =>
              let started := startStatement (.push frames (.sequence target remaining))
                statement
              some ⟨state, .push rest ⟨current, started.1⟩,
                .evaluate started.2⟩
      | .finish value =>
          match state.heap.activations current with
          | none => none
          | some activation =>
              match state.heap.severActivationContinuation current with
              | none => none
              | some heap =>
                  match activation.continuation with
                  | none =>
                      some ⟨{state with heap := heap}, .empty, .halt value⟩
                  | some continuation =>
                      match resumeActivation (.push rest currentFrame) continuation with
                      | none => none
                      | some resumed =>
                          some ⟨{state with heap := heap}, resumed, .object value⟩
      | _ => none

inductive BodyMachineStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | graph {before after : SequentialConfig}
      (next : p.bodyMachineNext before = some after) :
      BodyMachineStep p before after

theorem bodyMachineStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.BodyMachineStep before after₁)
    (step₂ : p.BodyMachineStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | graph next₁ =>
      cases step₂ with
      | graph next₂ =>
          exact Option.some.inj (next₁.symm.trans next₂)

end Program
end Newspeak
