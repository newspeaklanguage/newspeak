import Newspeak.Returns

namespace Newspeak

def ActivationDef.effectiveHome (id : ActivationId)
    (activation : ActivationDef) : Option ActivationId :=
  match activation.provenance with
  | .top => none
  | .method _ => some id
  | .closure _ => activation.homeMethod
  | .initializer _ => some id

def extendActivationScope (base : FiniteStore ActivationDeclId ActivationId)
    (declaration : ActivationDeclId) (activation : ActivationId) :
    FiniteStore ActivationDeclId ActivationId :=
  base.install declaration activation

@[simp] theorem mem_extendActivationScope_domain_iff
    (base : FiniteStore ActivationDeclId ActivationId)
    (declaration query : ActivationDeclId) (activation : ActivationId) :
    query ∈ (extendActivationScope base declaration activation).domain ↔
      query = declaration ∨ query ∈ base.domain := by
  exact FiniteStore.mem_install_domain_iff base declaration query activation

namespace Program

def closureDefinition (p : Program) (definingActivation : ActivationId)
    (defining : ActivationDef) (declaration : ActivationDeclId)
    (body : List Statement) : ClosureDef :=
  { classId := p.closureClass
    declaration := declaration
    parameters := p.closureParameters declaration
    locals := p.closureLocals declaration
    body := body
    definingActivation := definingActivation
    capturedReceiver := defining.currentReceiver
    capturedClass := defining.currentClass
    homeMethod := defining.effectiveHome definingActivation }

def cascadeClosureDefinition (p : Program)
    (definingActivation : ActivationId) (defining : ActivationDef)
    (descriptor : CascadeDescriptor)
    (clauses : List (Selector × List CoreExpr)) : ClosureDef :=
  { classId := p.closureClass
    declaration := descriptor.closureDeclaration
    parameters := [descriptor.receiverParameter]
    locals := []
    body := cascadeStatements descriptor clauses
    definingActivation := definingActivation
    capturedReceiver := defining.currentReceiver
    capturedClass := defining.currentClass
    homeMethod := defining.effectiveHome definingActivation }

theorem cascadeClosureDefinition_materializes_and_captures (p : Program)
    (definingActivation : ActivationId) (defining : ActivationDef)
    (descriptor : CascadeDescriptor)
    (clauses : List (Selector × List CoreExpr)) :
    let closure := p.cascadeClosureDefinition definingActivation defining
      descriptor clauses
    closure.declaration = descriptor.closureDeclaration ∧
      closure.parameters = [descriptor.receiverParameter] ∧
      closure.locals = [] ∧
      closure.body = cascadeStatements descriptor clauses ∧
      closure.definingActivation = definingActivation ∧
      closure.capturedReceiver = defining.currentReceiver ∧
      closure.capturedClass = defining.currentClass ∧
      closure.homeMethod = defining.effectiveHome definingActivation := by
  simp [cascadeClosureDefinition]

theorem closureDefinition_materializes_and_captures (p : Program)
    (definingActivation : ActivationId) (defining : ActivationDef)
    (declaration : ActivationDeclId) (body : List Statement) :
    let closure := p.closureDefinition definingActivation defining declaration body
    closure.parameters = p.closureParameters declaration ∧
      closure.locals = p.closureLocals declaration ∧
      closure.body = body ∧
      closure.definingActivation = definingActivation ∧
      closure.capturedReceiver = defining.currentReceiver ∧
      closure.capturedClass = defining.currentClass ∧
      closure.homeMethod = defining.effectiveHome definingActivation := by
  simp [closureDefinition]

def allocateClosureObject (_p : Program) (state : AllocationState)
    (closure : ClosureDef) : AllocationState × ClosureId :=
  let id : ClosureId := ⟨state.nextClosure⟩
  ({ state with heap := state.heap.installClosure id closure
                nextClosure := state.nextClosure + 1 },
    id)

@[simp] theorem allocateClosureObject_reference (p : Program)
    (state : AllocationState) (closure : ClosureDef) :
    (p.allocateClosureObject state closure).2 = ⟨state.nextClosure⟩ := by
  rfl

@[simp] theorem allocateClosureObject_installs (p : Program)
    (state : AllocationState) (closure : ClosureDef) :
    let allocation := p.allocateClosureObject state closure
    allocation.1.heap.closures allocation.2 = some closure := by
  simp [allocateClosureObject]

theorem allocateClosureObject_was_fresh (_p : Program)
    {state : AllocationState} (fresh : state.ClosureSupplyFresh)
    (_closure : ClosureDef) :
    state.heap.closures ⟨state.nextClosure⟩ = none :=
  fresh ⟨state.nextClosure⟩ (Nat.le_refl _)

theorem allocateClosureObject_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (closure : ClosureDef) :
    (p.allocateClosureObject state closure).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id hid
    apply fresh.1 id
    simpa [allocateClosureObject] using hid
  · intro id hid
    apply fresh.2.1 id
    simpa [allocateClosureObject] using hid
  · intro id hid
    have hid' : state.nextClosure + 1 ≤ id.index := by
      simpa [allocateClosureObject] using hid
    have hne : id ≠ (⟨state.nextClosure⟩ : ClosureId) := by
      intro heq
      have hindex : id.index = state.nextClosure := congrArg ClosureId.index heq
      omega
    rw [show (p.allocateClosureObject state closure).1.heap =
      state.heap.installClosure ⟨state.nextClosure⟩ closure by rfl]
    rw [Heap.installClosure_away state.heap closure hne]
    exact fresh.2.2.1 id (by omega)
  · intro id hid
    apply fresh.2.2.2.1 id
    simpa [allocateClosureObject] using hid
  · intro id hid
    apply fresh.2.2.2.2 id
    simpa [allocateClosureObject] using hid

def closureActivationDefinition (p : Program) (id : ActivationId)
    (closure : ClosureDef) (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId) : ActivationDef :=
  { objectClass := p.activationClass
    provenance := .closure closure.declaration
    parameters := bindParameters closure.parameters message.arguments
    locals := initializeLocalCells (localSlots closure.locals)
    currentReceiver := closure.capturedReceiver
    currentClass := closure.capturedClass
    continuation := continuation
    homeMethod := closure.homeMethod
    continuable := true
    activationScopes := extendActivationScope defining.activationScopes
      closure.declaration id
    objectLiteralScopes := defining.objectLiteralScopes }

def allocateClosureActivation (p : Program) (state : AllocationState)
    (closure : ClosureDef) (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId) : AllocationState × ActivationId :=
  let id : ActivationId := ⟨state.nextActivation⟩
  let activation := p.closureActivationDefinition id closure defining message
    continuation
  ({ state with heap := state.heap.installActivation id activation
                nextActivation := state.nextActivation + 1 },
    id)

@[simp] theorem allocateClosureActivation_reference (p : Program)
    (state : AllocationState) (closure : ClosureDef)
    (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId) :
    (p.allocateClosureActivation state closure defining message
      continuation).2 = ⟨state.nextActivation⟩ := by
  rfl

@[simp] theorem allocateClosureActivation_installs (p : Program)
    (state : AllocationState) (closure : ClosureDef)
    (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateClosureActivation state closure defining message
      continuation
    allocation.1.heap.activations allocation.2 =
      some (p.closureActivationDefinition allocation.2 closure defining message
        continuation) := by
  simp [allocateClosureActivation]

theorem allocateClosureActivation_was_fresh (_p : Program)
    {state : AllocationState} (fresh : state.ActivationSupplyFresh)
    (_closure : ClosureDef) (_defining : ActivationDef) (_message : Message)
    (_continuation : Option ActivationId) :
    state.heap.activations ⟨state.nextActivation⟩ = none :=
  fresh ⟨state.nextActivation⟩ (Nat.le_refl _)

theorem closureActivationDefinition_captures (p : Program)
    (id : ActivationId) (closure : ClosureDef) (defining : ActivationDef)
    (message : Message) (continuation : Option ActivationId) :
    let activation := p.closureActivationDefinition id closure defining
      message continuation
    activation.currentReceiver = closure.capturedReceiver ∧
      activation.currentClass = closure.capturedClass ∧
      activation.homeMethod = closure.homeMethod ∧
      activation.continuation = continuation ∧
      activation.activationScopes closure.declaration = some id := by
  simp [closureActivationDefinition, extendActivationScope]

theorem allocateClosureActivation_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (closure : ClosureDef) (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId) :
    (p.allocateClosureActivation state closure defining message
      continuation).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id hid
    apply fresh.1 id
    simpa [allocateClosureActivation] using hid
  · intro id hid
    have hid' : state.nextActivation + 1 ≤ id.index := by
      simpa [allocateClosureActivation] using hid
    have hne : id ≠ (⟨state.nextActivation⟩ : ActivationId) := by
      intro heq
      have hindex : id.index = state.nextActivation :=
        congrArg ActivationId.index heq
      omega
    rw [show (p.allocateClosureActivation state closure defining message
      continuation).1.heap =
      state.heap.installActivation ⟨state.nextActivation⟩
        (p.closureActivationDefinition ⟨state.nextActivation⟩ closure
          defining message continuation) by rfl]
    rw [Heap.installActivation_away state.heap
      (p.closureActivationDefinition ⟨state.nextActivation⟩ closure
        defining message continuation) hne]
    exact fresh.2.1 id (by omega)
  · intro id hid
    apply fresh.2.2.1 id
    simpa [allocateClosureActivation] using hid
  · intro id hid
    apply fresh.2.2.2.1 id
    simpa [allocateClosureActivation] using hid
  · intro id hid
    apply fresh.2.2.2.2 id
    simpa [allocateClosureActivation] using hid

def closureCreationTarget (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (defining : ActivationDef) (declaration : ActivationDeclId)
    (body : List Statement) : SequentialConfig :=
  let closure := p.closureDefinition current defining declaration body
  let allocation := p.allocateClosureObject state closure
  ⟨allocation.1, .push rest ⟨current, frames⟩,
    .object (.closureObject allocation.2)⟩

def cascadeClosureCreationTarget (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (defining : ActivationDef) (descriptor : CascadeDescriptor)
    (clauses : List (Selector × List CoreExpr)) : SequentialConfig :=
  let closure := p.cascadeClosureDefinition current defining descriptor clauses
  let allocation := p.allocateClosureObject state closure
  ⟨allocation.1, .push rest ⟨current, frames⟩,
    .object (.closureObject allocation.2)⟩

inductive ClosureCreationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | create {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {defining : ActivationDef} {declaration : ActivationDeclId}
      {body : List Statement}
      (currentActivation : state.heap.activations current = some defining)
      (currentBody : p.closureBodies declaration = some body) :
      ClosureCreationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.closureLiteral declaration)⟩
        (p.closureCreationTarget state rest current frames defining declaration body)
  | createCascade {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {defining : ActivationDef} {descriptor : CascadeDescriptor}
      {clauses : List (Selector × List CoreExpr)}
      (currentActivation : state.heap.activations current = some defining) :
      ClosureCreationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.cascadeClosure descriptor clauses)⟩
        (p.cascadeClosureCreationTarget state rest current frames defining
          descriptor clauses)

inductive ClosureDispatchStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | value {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {id : ClosureId}
      {closure : ClosureDef} {message : Message}
      (live : state.heap.closures id = some closure)
      (selectorMatches : message.selector = valueSelector closure.parameters.length)
      (arityMatches : message.arguments.length = closure.parameters.length) :
      ClosureDispatchStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary (.closureObject id)) message⟩
        ⟨state, .push rest ⟨current, frames⟩, .invokeClosure id message⟩

def nonTailClosureInvocationTarget (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (closure : ClosureDef) (defining : ActivationDef)
    (message : Message) : SequentialConfig :=
  let allocation := p.allocateClosureActivation state closure defining message
    (some current)
  ⟨allocation.1, .push (.push rest ⟨current, frames⟩) ⟨allocation.2, .empty⟩,
    .initialize allocation.2 closure.locals closure.body .closureBody⟩

def tailClosureInvocationTarget (p : Program) (state : AllocationState)
    (rest : ActivationStack) (caller : ActivationDef) (closure : ClosureDef)
    (defining : ActivationDef) (message : Message) : SequentialConfig :=
  let allocation := p.allocateClosureActivation state closure defining message
    caller.continuation
  ⟨allocation.1, .push rest ⟨allocation.2, .empty⟩,
    .initialize allocation.2 closure.locals closure.body .closureBody⟩

inductive ClosureInvocationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | nonTail {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {topFrame : EvalFrame}
      {id : ClosureId} {closure : ClosureDef} {defining : ActivationDef}
      {message : Message}
      (live : state.heap.closures id = some closure)
      (definingLive : state.heap.activations closure.definingActivation =
        some defining)
      (selectorMatches : message.selector = valueSelector closure.parameters.length)
      (arityMatches : message.arguments.length = closure.parameters.length) :
      ClosureInvocationStep p
        ⟨state, .push rest ⟨current, .push frames topFrame⟩,
          .invokeClosure id message⟩
        (p.nonTailClosureInvocationTarget state rest current
          (.push frames topFrame) closure defining message)
  | tail {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {caller defining : ActivationDef}
      {closureDef : ClosureDef} {id : ClosureId} {message : Message}
      (callerLive : state.heap.activations current = some caller)
      (live : state.heap.closures id = some closureDef)
      (definingLive : state.heap.activations closureDef.definingActivation =
        some defining)
      (selectorMatches : message.selector =
        valueSelector closureDef.parameters.length)
      (arityMatches : message.arguments.length = closureDef.parameters.length) :
      ClosureInvocationStep p
        ⟨state, .push rest ⟨current, .empty⟩, .invokeClosure id message⟩
        (p.tailClosureInvocationTarget state rest caller closureDef defining message)

inductive ClosureMachineStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | creation {before after : SequentialConfig} :
      p.ClosureCreationStep before after → p.ClosureMachineStep before after
  | dispatch {before after : SequentialConfig} :
      p.ClosureDispatchStep before after → p.ClosureMachineStep before after
  | invocation {before after : SequentialConfig} :
      p.ClosureInvocationStep before after → p.ClosureMachineStep before after

theorem closureCreation_control {p : Program}
    {before after : SequentialConfig}
    (step : p.ClosureCreationStep before after) :
    ∃ expression, before.control = .evaluate expression := by
  cases step <;> exact ⟨_, rfl⟩

theorem closureDispatch_control {p : Program}
    {before after : SequentialConfig}
    (step : p.ClosureDispatchStep before after) :
    ∃ id message,
      before.control = .dispatch (.ordinary (.closureObject id)) message := by
  cases step
  exact ⟨_, _, rfl⟩

theorem closureInvocation_control {p : Program}
    {before after : SequentialConfig}
    (step : p.ClosureInvocationStep before after) :
    ∃ id message, before.control = .invokeClosure id message := by
  cases step <;> exact ⟨_, _, rfl⟩

theorem closureCreationStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ClosureCreationStep before after₁)
    (step₂ : p.ClosureCreationStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | create live₁ body₁ =>
      cases step₂ with
      | create live₂ body₂ =>
          have hdefining := Option.some.inj (live₁.symm.trans live₂)
          subst hdefining
          have hbody := Option.some.inj (body₁.symm.trans body₂)
          subst hbody
          rfl
  | createCascade live₁ =>
      cases step₂ with
      | createCascade live₂ =>
          have hdefining := Option.some.inj (live₁.symm.trans live₂)
          subst hdefining
          rfl

theorem closureDispatchStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ClosureDispatchStep before after₁)
    (step₂ : p.ClosureDispatchStep before after₂) : after₁ = after₂ := by
  cases step₁
  cases step₂
  rfl

theorem closureInvocationStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ClosureInvocationStep before after₁)
    (step₂ : p.ClosureInvocationStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | nonTail live₁ defining₁ _ _ =>
      cases step₂ with
      | nonTail live₂ defining₂ _ _ =>
          have hclosure := Option.some.inj (live₁.symm.trans live₂)
          subst hclosure
          have hdefining := Option.some.inj (defining₁.symm.trans defining₂)
          subst hdefining
          rfl
  | tail caller₁ live₁ defining₁ _ _ =>
      cases step₂ with
      | tail caller₂ live₂ defining₂ _ _ =>
          have hcaller := Option.some.inj (caller₁.symm.trans caller₂)
          subst hcaller
          have hclosure := Option.some.inj (live₁.symm.trans live₂)
          subst hclosure
          have hdefining := Option.some.inj (defining₁.symm.trans defining₂)
          subst hdefining
          rfl

theorem closureMachineStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ClosureMachineStep before after₁)
    (step₂ : p.ClosureMachineStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | creation creation₁ =>
      cases step₂ with
      | creation creation₂ =>
          exact closureCreationStep_deterministic creation₁ creation₂
      | dispatch dispatch₂ =>
          rcases closureCreation_control creation₁ with ⟨_, creationControl⟩
          rcases closureDispatch_control dispatch₂ with ⟨_, _, dispatchControl⟩
          rw [dispatchControl] at creationControl
          cases creationControl
      | invocation invocation₂ =>
          rcases closureCreation_control creation₁ with ⟨_, creationControl⟩
          rcases closureInvocation_control invocation₂ with ⟨_, _, invocationControl⟩
          rw [invocationControl] at creationControl
          cases creationControl
  | dispatch dispatch₁ =>
      cases step₂ with
      | creation creation₂ =>
          rcases closureDispatch_control dispatch₁ with ⟨_, _, dispatchControl⟩
          rcases closureCreation_control creation₂ with ⟨_, creationControl⟩
          rw [creationControl] at dispatchControl
          cases dispatchControl
      | dispatch dispatch₂ =>
          exact closureDispatchStep_deterministic dispatch₁ dispatch₂
      | invocation invocation₂ =>
          rcases closureDispatch_control dispatch₁ with ⟨_, _, dispatchControl⟩
          rcases closureInvocation_control invocation₂ with ⟨_, _, invocationControl⟩
          rw [invocationControl] at dispatchControl
          cases dispatchControl
  | invocation invocation₁ =>
      cases step₂ with
      | creation creation₂ =>
          rcases closureInvocation_control invocation₁ with ⟨_, _, invocationControl⟩
          rcases closureCreation_control creation₂ with ⟨_, creationControl⟩
          rw [creationControl] at invocationControl
          cases invocationControl
      | dispatch dispatch₂ =>
          rcases closureInvocation_control invocation₁ with ⟨_, _, invocationControl⟩
          rcases closureDispatch_control dispatch₂ with ⟨_, _, dispatchControl⟩
          rw [dispatchControl] at invocationControl
          cases invocationControl
      | invocation invocation₂ =>
          exact closureInvocationStep_deterministic invocation₁ invocation₂

end Program
end Newspeak
