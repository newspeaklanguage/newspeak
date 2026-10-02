import Newspeak.RequestResolution

namespace Newspeak

inductive InitializationTarget where
  | methodBody (receiver : ObjRef)
  | closureBody
deriving Repr, DecidableEq, BEq

/-- Initial intra-activation frame fragment.  The remaining frame constructors
    are added with sequencing, local initialization, and return. -/
inductive EvalFrame where
  | receiver (selector : Selector) (arguments : List CoreExpr)
  | asyncReceiver (selector : Selector) (arguments : List CoreExpr)
  | arguments (request : SendRequest) (selector : Selector)
      (values : List ObjRef) (remaining : List CoreExpr)
  | initializeLocal (slot : LocalSlotId)
      (remaining : List LocalDeclarationGroup) (body : List Statement)
      (target : InitializationTarget)
  | localWrite (activation : ActivationId) (slot : LocalSlotId)
  | slotWrite (object : ObjectId) (slot : SlotId)
  | lazySlotStore (object : ObjectId) (slot : SlotId)
  | makeClassBody (descriptor : ClassBodyDescriptor)
      (enclosingObject : ObjRef)
  | makeObjectLiteral (descriptor : ObjectLiteralDescriptor)
      (enclosingObject : ObjRef)
  | nestedClassStore (object : ObjectId) (declaration : ClassDeclId)
  | mixinSuperclass (descriptor : MixinApplicationDescriptor)
      (mixinSource : CoreExpr)
  | mixinSource (descriptor : MixinApplicationDescriptor)
      (superclass : ClassId)
  | messageArguments (selector : Selector) (values : List ObjRef)
      (remaining : List CoreExpr)
  | superclassMessage (classId : ClassId) (object : ObjectId)
      (original : Message)
  | afterSuperclass (classId : ClassId) (object : ObjectId)
      (original : Message)
  | mixinMessage (classId : ClassId) (object : ObjectId)
  | afterMixin (classId : ClassId) (object : ObjectId)
  | storeInitializedSlot (object : ObjectId) (slot : SlotId)
      (remainingDeclarations : List SlotDeclaration)
      (remainingGroups : List SlotDeclarationGroup) (body : List Statement)
  | simultaneousSlots (remainingCode : List CoreExpr) (object : ObjectId)
      (remainingGroups : List SlotDeclarationGroup) (body : List Statement)
  | simultaneousLocals (remainingCode : List CoreExpr)
      (activation : ActivationId) (remaining : List LocalDeclarationGroup)
      (body : List Statement) (target : InitializationTarget)
  | sequence (target : InitializationTarget) (remaining : List Statement)
  | returnFrame
deriving Repr

/-- Snoc-shaped intra-activation stack matching `π · F`. -/
inductive EvalStack where
  | empty
  | push (rest : EvalStack) (top : EvalFrame)
deriving Repr

structure ActivationFrame where
  activation : ActivationId
  frames : EvalStack
deriving Repr

/-- Snoc-shaped stack matching the prose notation `A · ⟨a,π⟩`. -/
inductive ActivationStack where
  | empty
  | push (rest : ActivationStack) (current : ActivationFrame)
deriving Repr

inductive RuntimeError where
  | invalidSuper (currentClass : ClassId)
  | cannotReturn
  | classExpected
  | classNotInstantiable
  | wrongFactory
  | topSuperclass
deriving Repr, DecidableEq, BEq

/-- First control-term fragment needed to connect request completion to method
    activation. -/
inductive ControlTerm where
  | evaluate (expression : CoreExpr)
  | object (value : ObjRef)
  | evaluateMessage (template : MessageTemplate)
  | messageValue (message : Message)
  | initClass (classId : ClassId) (object : ObjectId) (message : Message)
  | ownInitialization (classId : ClassId) (object : ObjectId)
      (message : Message)
  | initializeSlotGroups (object : ObjectId)
      (groups : List SlotDeclarationGroup) (body : List Statement)
  | initializeSequentialSlots (object : ObjectId)
      (declarations : List SlotDeclaration)
      (remainingGroups : List SlotDeclarationGroup) (body : List Statement)
  | dispatch (request : SendRequest) (message : Message)
  | invoke (method : MethodDef) (receiver : ObjRef)
      (definingClass : ClassId) (message : Message)
  | invokeClosure (closure : ClosureId) (message : Message)
  | initialize (activation : ActivationId)
      (locals : List LocalDeclarationGroup) (body : List Statement)
      (target : InitializationTarget)
  | body (target : InitializationTarget) (statements : List Statement)
  | finish (value : ObjRef)
  | transfer (target : ActivationId) (value : ObjRef)
  | halt (value : ObjRef)
  /-- An exception signal that escaped the top activation of an actor turn. -/
  | abort (exception : ObjRef)
  | throw (error : RuntimeError)
  | runtimeError (error : RuntimeError)
deriving Repr

structure SequentialConfig where
  allocation : AllocationState
  stack : ActivationStack
  control : ControlTerm

def bindParameters : List ParameterId → List ObjRef →
    FiniteStore ParameterId ObjRef
  | parameter :: parameters, argument :: arguments =>
      (bindParameters parameters arguments).install parameter argument
  | _, _ => FiniteStore.empty ParameterId ObjRef

/-- Parameter identities that actually receive arguments.  Arity mismatch is
    represented exactly as in `bindParameters`: binding stops when either list
    ends. -/
def boundParameterIds : List ParameterId → List ObjRef → List ParameterId
  | parameter :: parameters, _ :: arguments =>
      parameter :: boundParameterIds parameters arguments
  | _, _ => []

@[simp] theorem mem_bindParameters_domain_iff (parameters : List ParameterId)
    (arguments : List ObjRef) (query : ParameterId) :
    query ∈ (bindParameters parameters arguments).domain ↔
      query ∈ boundParameterIds parameters arguments := by
  induction parameters generalizing arguments with
  | nil => simp [bindParameters, boundParameterIds]
  | cons parameter parameters ih =>
      cases arguments with
      | nil => simp [bindParameters, boundParameterIds]
      | cons argument arguments =>
          change query ∈
              ((bindParameters parameters arguments).install parameter argument).domain ↔
            query ∈ parameter :: boundParameterIds parameters arguments
          rw [FiniteStore.mem_install_domain_iff]
          simp [ih]

def initializeLocalCells (locals : List LocalSlotId) :
    FiniteStore LocalSlotId LocalCell :=
  FiniteStore.constantOn locals .uninitialized

@[simp] theorem mem_initializeLocalCells_domain_iff
    (locals : List LocalSlotId) (query : LocalSlotId) :
    query ∈ (initializeLocalCells locals).domain ↔ query ∈ locals := by
  simp [initializeLocalCells, FiniteStore.mem_deduplicated]

def methodActivationScopes (method : MethodDef) (id : ActivationId) :
    FiniteStore ActivationDeclId ActivationId :=
  (FiniteStore.empty ActivationDeclId ActivationId).install
    method.activationDeclaration id

@[simp] theorem mem_methodActivationScopes_domain_iff
    (method : MethodDef) (id : ActivationId) (query : ActivationDeclId) :
    query ∈ (methodActivationScopes method id).domain ↔
      query = method.activationDeclaration := by
  change query ∈
      ((FiniteStore.empty ActivationDeclId ActivationId).install
        method.activationDeclaration id).domain ↔ _
  rw [FiniteStore.mem_install_domain_iff]
  simp

def methodObjectLiteralScopes (method : MethodDef) (receiver : ObjRef) :
    FiniteStore ObjectLiteralDeclId ObjRef :=
  match method.owner with
  | .namedClass _ => FiniteStore.empty ObjectLiteralDeclId ObjRef
  | .objectLiteral declaration =>
      (FiniteStore.empty ObjectLiteralDeclId ObjRef).install declaration receiver

@[simp] theorem mem_methodObjectLiteralScopes_domain_iff
    (method : MethodDef) (receiver : ObjRef) (query : ObjectLiteralDeclId) :
    query ∈ (methodObjectLiteralScopes method receiver).domain ↔
      ∃ declaration, method.owner = .objectLiteral declaration ∧
        query = declaration := by
  cases owner : method.owner with
  | namedClass declaration =>
      simp [methodObjectLiteralScopes, owner]
  | objectLiteral declaration =>
      have scopeEq : methodObjectLiteralScopes method receiver =
          (FiniteStore.empty ObjectLiteralDeclId ObjRef).install
            declaration receiver := by
        simp [methodObjectLiteralScopes, owner]
      rw [scopeEq]
      rw [FiniteStore.mem_install_domain_iff]
      simp

namespace Program

def methodActivationDefinition (p : Program) (id : ActivationId)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (continuation : Option ActivationId) : ActivationDef :=
  { objectClass := p.activationClass
    provenance := .method method.identity
    parameters := bindParameters method.parameters message.arguments
    locals := initializeLocalCells method.locals
    currentReceiver := receiver
    currentClass := some definingClass
    continuation := continuation
    homeMethod := some id
    continuable := true
    activationScopes := methodActivationScopes method id
    objectLiteralScopes := methodObjectLiteralScopes method receiver }

/-- Deterministic method-activation allocation from Equation (8.11). -/
def allocateMethodActivation (p : Program) (state : AllocationState)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (continuation : Option ActivationId) :
    AllocationState × ActivationId :=
  let id : ActivationId := ⟨state.nextActivation⟩
  let activation := p.methodActivationDefinition id method receiver
    definingClass message continuation
  ({ state with heap := state.heap.installActivation id activation
                nextActivation := state.nextActivation + 1 },
    id)

@[simp] theorem allocateMethodActivation_reference (p : Program)
    (state : AllocationState) (method : MethodDef) (receiver : ObjRef)
    (definingClass : ClassId) (message : Message)
    (continuation : Option ActivationId) :
    (p.allocateMethodActivation state method receiver definingClass message
      continuation).2 = ⟨state.nextActivation⟩ := by
  rfl

@[simp] theorem allocateMethodActivation_installs (p : Program)
    (state : AllocationState) (method : MethodDef) (receiver : ObjRef)
    (definingClass : ClassId) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateMethodActivation state method receiver
      definingClass message continuation
    allocation.1.heap.activations allocation.2 =
      some (p.methodActivationDefinition allocation.2 method receiver
        definingClass message continuation) := by
  simp [allocateMethodActivation]

theorem allocateMethodActivation_sets_currentClass (p : Program)
    (state : AllocationState) (method : MethodDef) (receiver : ObjRef)
    (definingClass : ClassId) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateMethodActivation state method receiver
      definingClass message continuation
    ∃ activation,
      allocation.1.heap.activations allocation.2 = some activation ∧
      activation.currentReceiver = receiver ∧
      activation.currentClass = some definingClass ∧
      activation.continuation = continuation ∧
      activation.homeMethod = some allocation.2 := by
  let activation := p.methodActivationDefinition ⟨state.nextActivation⟩
    method receiver definingClass message continuation
  refine ⟨activation, ?_, rfl, rfl, rfl, rfl⟩
  simp [allocateMethodActivation, activation]

theorem allocateMethodActivation_was_fresh (_p : Program)
    {state : AllocationState} (fresh : state.ActivationSupplyFresh)
    (_method : MethodDef) (_receiver : ObjRef) (_definingClass : ClassId)
    (_message : Message) (_continuation : Option ActivationId) :
    state.heap.activations ⟨state.nextActivation⟩ = none :=
  fresh ⟨state.nextActivation⟩ (Nat.le_refl _)

theorem allocateMethodActivation_preserves_activationFreshness (p : Program)
    {state : AllocationState} (fresh : state.ActivationSupplyFresh)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateMethodActivation state method receiver definingClass message
      continuation).1.ActivationSupplyFresh := by
  intro id hid
  have hid' : state.nextActivation + 1 ≤ id.index := by
    simpa [allocateMethodActivation] using hid
  have hne : id ≠ (⟨state.nextActivation⟩ : ActivationId) := by
    intro heq
    have hindex : id.index = state.nextActivation :=
      congrArg ActivationId.index heq
    omega
  rw [show (p.allocateMethodActivation state method receiver definingClass
      message continuation).1.heap =
      state.heap.installActivation ⟨state.nextActivation⟩
        (p.methodActivationDefinition ⟨state.nextActivation⟩ method
          receiver definingClass message continuation) by rfl]
  rw [Heap.installActivation_away state.heap
    (p.methodActivationDefinition ⟨state.nextActivation⟩ method receiver
      definingClass message continuation) hne]
  exact fresh id (by omega)

theorem allocateMethodActivation_preserves_mirrorFreshness (p : Program)
    {state : AllocationState} (fresh : state.MirrorSupplyFresh)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateMethodActivation state method receiver definingClass message
      continuation).1.MirrorSupplyFresh := by
  intro id hid
  apply fresh id
  simpa [allocateMethodActivation] using hid

theorem allocateMethodActivation_preserves_closureFreshness (p : Program)
    {state : AllocationState} (fresh : state.ClosureSupplyFresh)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateMethodActivation state method receiver definingClass message
      continuation).1.ClosureSupplyFresh := by
  intro id hid
  apply fresh id
  simpa [allocateMethodActivation] using hid

theorem allocateMethodActivation_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateMethodActivation state method receiver definingClass message
      continuation).1.SuppliesFresh :=
  ⟨p.allocateMethodActivation_preserves_mirrorFreshness fresh.1 method receiver
      definingClass message continuation,
    p.allocateMethodActivation_preserves_activationFreshness fresh.2.1 method
      receiver definingClass message continuation,
    p.allocateMethodActivation_preserves_closureFreshness fresh.2.2.1 method
      receiver definingClass message continuation,
    by
      intro id bound
      exact fresh.2.2.2.1 id
        (by simpa [allocateMethodActivation] using bound),
    by
      intro id bound
      exact fresh.2.2.2.2 id
        (by simpa [allocateMethodActivation] using bound)⟩

def nonTailInvocationTarget (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId)
    (frames : EvalStack) (method : MethodDef) (receiver : ObjRef)
    (definingClass : ClassId) (message : Message)
    (locals : List LocalDeclarationGroup) (body : List Statement) :
    SequentialConfig :=
  let allocation := p.allocateMethodActivation state method receiver
    definingClass message (some current)
  ⟨allocation.1,
    .push (.push rest ⟨current, frames⟩) ⟨allocation.2, .empty⟩,
    .initialize allocation.2 locals body (.methodBody receiver)⟩

def tailInvocationTarget (p : Program) (state : AllocationState)
    (rest : ActivationStack) (currentDef : ActivationDef)
    (method : MethodDef) (receiver : ObjRef) (definingClass : ClassId)
    (message : Message) (locals : List LocalDeclarationGroup)
    (body : List Statement) : SequentialConfig :=
  let allocation := p.allocateMethodActivation state method receiver
    definingClass message currentDef.continuation
  ⟨allocation.1, .push rest ⟨allocation.2, .empty⟩,
    .initialize allocation.2 locals body (.methodBody receiver)⟩

/-- The non-tail and tail method invocation transitions (Equations 8.12 and
    8.13).  A nonempty frame list retains the caller and points the callee back
    to it.  An empty frame list replaces the caller and copies its continuation.
-/
inductive MethodInvocationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | nonTail {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {topFrame : EvalFrame}
      {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
      {message : Message} {locals : List LocalDeclarationGroup}
      {body : List Statement}
      (selectorMatches : method.selector = message.selector)
      (arityMatches : method.parameters.length = message.arguments.length)
      (currentLocals : p.methodLocals method.identity = locals)
      (currentBody : p.methodBodies method.identity = some body) :
      MethodInvocationStep p
        ⟨state, .push rest ⟨current, .push frames topFrame⟩,
          .invoke method receiver definingClass message⟩
        (p.nonTailInvocationTarget state rest current (.push frames topFrame)
          method receiver definingClass message locals body)
  | tail {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {currentDef : ActivationDef}
      {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
      {message : Message} {locals : List LocalDeclarationGroup}
      {body : List Statement}
      (currentActivation : state.heap.activations current = some currentDef)
      (selectorMatches : method.selector = message.selector)
      (arityMatches : method.parameters.length = message.arguments.length)
      (currentLocals : p.methodLocals method.identity = locals)
      (currentBody : p.methodBodies method.identity = some body) :
      MethodInvocationStep p
        ⟨state, .push rest ⟨current, .empty⟩,
          .invoke method receiver definingClass message⟩
        (p.tailInvocationTarget state rest currentDef method receiver
          definingClass message locals body)

theorem methodInvocationStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.MethodInvocationStep before after₁)
    (step₂ : p.MethodInvocationStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | nonTail _ _ locals₁ body₁ =>
      cases step₂ with
      | nonTail _ _ locals₂ body₂ =>
          have hlocals := locals₁.symm.trans locals₂
          subst hlocals
          have hbody : _ := Option.some.inj (body₁.symm.trans body₂)
          subst hbody
          rfl
  | tail currentActivation₁ _ _ locals₁ body₁ =>
      cases step₂ with
      | tail currentActivation₂ _ _ locals₂ body₂ =>
          have hcurrent : _ := Option.some.inj
            (currentActivation₁.symm.trans currentActivation₂)
          subst hcurrent
          have hlocals := locals₁.symm.trans locals₂
          subst hlocals
          have hbody : _ := Option.some.inj (body₁.symm.trans body₂)
          subst hbody
          rfl

end Program
end Newspeak
