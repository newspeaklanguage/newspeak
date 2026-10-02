import Newspeak.FactoryInitialization

namespace Newspeak

def InitializerPlan.superclassMessage : InitializerPlan → MessageTemplate
  | .body message => message
  | .appliedMixin message _ => message

def Message.matchesInitializer (message : Message) (selector : Selector)
    (parameters : List ParameterId) : Bool :=
  message.selector == selector && message.arguments.length == parameters.length

namespace Program

/-- Equation (9.18): an applied mixin runs in a fresh home activation whose
    current class is the new application, not the class supplying the mixin. -/
def mixinInitializerActivationDefinition (p : Program) (id : ActivationId)
    (mixin : MixinDef) (classId : ClassId) (object : ObjectId)
    (message : Message) (continuation : Option ActivationId) : ActivationDef :=
  { objectClass := p.activationClass
    provenance := .initializer mixin.initializerDeclaration
    parameters := bindParameters mixin.initializerParameters message.arguments
    locals := FiniteStore.empty LocalSlotId LocalCell
    currentReceiver := .ordinaryObject object
    currentClass := some classId
    continuation := continuation
    homeMethod := some id
    continuable := true
    activationScopes := initializerActivationScopes
      mixin.initializerDeclaration id
    objectLiteralScopes := FiniteStore.empty ObjectLiteralDeclId ObjRef }

def allocateMixinInitializerActivation (p : Program) (state : AllocationState)
    (mixin : MixinDef) (classId : ClassId) (object : ObjectId)
    (message : Message) (continuation : Option ActivationId) :
    AllocationState × ActivationId :=
  let id : ActivationId := ⟨state.nextActivation⟩
  let activation := p.mixinInitializerActivationDefinition id mixin classId
    object message continuation
  ({ state with
      heap := state.heap.installActivation id activation
      nextActivation := state.nextActivation + 1 }, id)

@[simp] theorem allocateMixinInitializerActivation_installs (p : Program)
    (state : AllocationState) (mixin : MixinDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateMixinInitializerActivation state mixin classId
      object message continuation
    allocation.1.heap.activations allocation.2 =
      some (p.mixinInitializerActivationDefinition allocation.2 mixin classId
        object message continuation) := by
  simp [allocateMixinInitializerActivation]

theorem allocateMixinInitializerActivation_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (mixin : MixinDef) (classId : ClassId) (object : ObjectId)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateMixinInitializerActivation state mixin classId object message
      continuation).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id bound
    exact fresh.1 id (by
      simpa [allocateMixinInitializerActivation] using bound)
  · intro id bound
    have later : state.nextActivation + 1 ≤ id.index := by
      simpa [allocateMixinInitializerActivation] using bound
    have away : id ≠ (⟨state.nextActivation⟩ : ActivationId) := by
      intro equal
      have indexEqual := congrArg ActivationId.index equal
      simp at indexEqual
      omega
    rw [show (p.allocateMixinInitializerActivation state mixin classId object
      message continuation).1.heap =
      state.heap.installActivation ⟨state.nextActivation⟩
        (p.mixinInitializerActivationDefinition ⟨state.nextActivation⟩ mixin
          classId object message continuation) by rfl]
    rw [Heap.installActivation_away _ _ away]
    exact fresh.2.1 id (by omega)
  · intro id bound
    exact fresh.2.2.1 id (by
      simpa [allocateMixinInitializerActivation] using bound)
  · intro id bound
    exact fresh.2.2.2.1 id (by
      simpa [allocateMixinInitializerActivation] using bound)
  · intro id bound
    exact fresh.2.2.2.2 id (by
      simpa [allocateMixinInitializerActivation] using bound)

theorem allocateMixinInitializerActivation_wellFormed (p : Program)
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (mixin : MixinDef)
    (classId : ClassId) (classLive : p.IsLiveClass state.heap classId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    p.WellFormed (p.allocateMixinInitializerActivation state mixin classId
        object message continuation).1.heap ∧
      (p.allocateMixinInitializerActivation state mixin classId object message
        continuation).1.SuppliesFresh := by
  constructor
  · apply wf.installActivation_wellFormed
    · simpa [mixinInitializerActivationDefinition] using
        wf.activationClassIsLive
    · simpa [mixinInitializerActivationDefinition, OptionalClassLive] using
        classLive
  · exact p.allocateMixinInitializerActivation_preserves_supplies fresh mixin
      classId object message continuation

def startSuperclassInitialization (_p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (classId : ClassId) (object : ObjectId) (original : Message)
    (factory : FactoryDef) : SequentialConfig :=
  ⟨state, .push rest ⟨current,
      .push frames (.superclassMessage classId object original)⟩,
    .evaluateMessage factory.plan.superclassMessage⟩

def invokeSuperclassInitializer (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (classId superclass : ClassId) (object : ObjectId) (original : Message)
    (factory : FactoryDef) (message : Message) : SequentialConfig :=
  let allocation := p.allocateInitializerActivation state factory superclass
    object message (some current)
  ⟨allocation.1,
    .push (.push rest
      ⟨current, .push frames (.afterSuperclass classId object original)⟩)
      ⟨allocation.2, .empty⟩,
    .initClass superclass object message⟩

def startMixinInitialization (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (classId : ClassId) (object : ObjectId) (message : MessageTemplate) :
    SequentialConfig :=
  ⟨state, .push rest ⟨current, .push frames (.mixinMessage classId object)⟩,
    .evaluateMessage message⟩

def invokeMixinInitializer (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (classId : ClassId) (object : ObjectId) (mixin : MixinDef)
    (message : Message) : SequentialConfig :=
  let allocation := p.allocateMixinInitializerActivation state mixin classId
    object message (some current)
  ⟨allocation.1,
    .push (.push rest ⟨current,
      .push frames (.afterMixin classId object)⟩)
      ⟨allocation.2, .empty⟩,
    .initializeSlotGroups object mixin.initializerGroups mixin.initializerBody⟩

theorem invokeSuperclassInitializer_wellFormed (p : Program)
    {state : AllocationState} (heapWellFormed : p.WellFormed state.heap)
    (suppliesFresh : state.SuppliesFresh) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (classId superclass : ClassId)
    (object : ObjectId) (original : Message) (factory : FactoryDef)
    (message : Message) (stackLive : StackLive state.heap
      (.push rest ⟨current, frames⟩))
    {superclassDef : ClassDef}
    (superclassLive : state.heap.classes superclass = some superclassDef) :
    SequentialWellFormed p (p.invokeSuperclassInitializer state rest current
      frames classId superclass object original factory message) := by
  let allocation := p.allocateInitializerActivation state factory superclass
    object message (some current)
  have classLive : p.IsLiveClass state.heap superclass :=
    Or.inr ⟨superclassDef, superclassLive⟩
  have allocationWellFormed := p.allocateInitializerActivation_wellFormed
    heapWellFormed suppliesFresh factory superclass classLive object message
    (some current)
  have freshId := p.allocateInitializerActivation_was_fresh
    suppliesFresh.2.1 factory superclass object message (some current)
  have retained : StackLive allocation.1.heap
      (.push rest ⟨current,
        .push frames (.afterSuperclass classId object original)⟩) :=
    stackLive_transport (by simpa [StackLive] using stackLive)
      (Heap.installActivation_fresh_retains state.heap
        ⟨state.nextActivation⟩
        (p.initializerActivationDefinition ⟨state.nextActivation⟩ factory
          superclass object message (some current)) freshId)
  have installed : allocation.1.heap.activations allocation.2 =
      some (p.initializerActivationDefinition allocation.2 factory superclass
        object message (some current)) :=
    p.allocateInitializerActivation_installs state factory superclass object
      message (some current)
  exact ⟨allocationWellFormed.1, allocationWellFormed.2,
    ⟨retained, _, installed⟩, trivial⟩

theorem invokeMixinInitializer_wellFormed (p : Program)
    {state : AllocationState} (heapWellFormed : p.WellFormed state.heap)
    (suppliesFresh : state.SuppliesFresh) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (classId : ClassId)
    (object : ObjectId) (mixin : MixinDef) (message : Message)
    (stackLive : StackLive state.heap (.push rest ⟨current, frames⟩))
    {classDef : ClassDef}
    (classLive : state.heap.classes classId = some classDef) :
    SequentialWellFormed p (p.invokeMixinInitializer state rest current frames
      classId object mixin message) := by
  let allocation := p.allocateMixinInitializerActivation state mixin classId
    object message (some current)
  have liveClass : p.IsLiveClass state.heap classId :=
    Or.inr ⟨classDef, classLive⟩
  have allocationWellFormed :=
    p.allocateMixinInitializerActivation_wellFormed heapWellFormed
      suppliesFresh mixin classId liveClass object message (some current)
  have freshId : state.heap.activations ⟨state.nextActivation⟩ = none :=
    suppliesFresh.2.1 ⟨state.nextActivation⟩ (Nat.le_refl _)
  have retained : StackLive allocation.1.heap
      (.push rest ⟨current, .push frames (.afterMixin classId object)⟩) :=
    stackLive_transport (by simpa [StackLive] using stackLive)
      (Heap.installActivation_fresh_retains state.heap
        ⟨state.nextActivation⟩
        (p.mixinInitializerActivationDefinition ⟨state.nextActivation⟩ mixin
          classId object message (some current)) freshId)
  have installed : allocation.1.heap.activations allocation.2 =
      some (p.mixinInitializerActivationDefinition allocation.2 mixin classId
        object message (some current)) :=
    p.allocateMixinInitializerActivation_installs state mixin classId object
      message (some current)
  exact ⟨allocationWellFormed.1, allocationWellFormed.2,
    ⟨retained, _, installed⟩, trivial⟩

/-- Equations (9.15)--(9.19), as one executable coordinator phase. -/
def initializationCoordinatorNext (p : Program)
    (config : SequentialConfig) : Option SequentialConfig := do
  let .push rest currentFrame := config.stack | none
  let current := currentFrame.activation
  let frames := currentFrame.frames
  match config.control with
  | .initClass classId object original => do
      let classDef ← config.allocation.heap.classes classId
      if classDef.superclass = p.top then
        some ⟨config.allocation, config.stack,
          .ownInitialization classId object original⟩
      else
        let factory ← classDef.primaryFactory
        some (p.startSuperclassInitialization config.allocation rest current
          frames classId object original factory)
  | .messageValue message =>
      match frames with
      | .push below (.superclassMessage classId object original) => do
          let classDef ← config.allocation.heap.classes classId
          let superclass := classDef.superclass
          let superclassDef ← config.allocation.heap.classes superclass
          let factory ← superclassDef.primaryFactory
          if message.matchesInitializer factory.selector factory.parameters then
            some (p.invokeSuperclassInitializer config.allocation rest current
              below classId superclass object original factory message)
          else
            some ⟨config.allocation, .push rest ⟨current, below⟩,
              .runtimeError .wrongFactory⟩
      | .push below (.mixinMessage classId object) => do
          let classDef ← config.allocation.heap.classes classId
          let mixin ← p.mixins classDef.mixin
          if message.matchesInitializer mixin.initializerSelector
              mixin.initializerParameters then
            some (p.invokeMixinInitializer config.allocation rest current below
              classId object mixin message)
          else
            some ⟨config.allocation, .push rest ⟨current, below⟩,
              .runtimeError .wrongFactory⟩
      | _ => none
  | .object (.ordinaryObject result) =>
      match frames with
      | .push below (.afterSuperclass classId object original) =>
          if result = object then
            some ⟨config.allocation, .push rest ⟨current, below⟩,
              .ownInitialization classId object original⟩
          else none
      | .push below (.afterMixin _classId object) =>
          if result = object then
            some ⟨config.allocation, .push rest ⟨current, below⟩,
              .finish (.ordinaryObject object)⟩
          else none
      | _ => none
  | .ownInitialization classId object _original => do
      let classDef ← config.allocation.heap.classes classId
      let factory ← classDef.primaryFactory
      let mixin ← p.mixins classDef.mixin
      match factory.plan with
      | .body _ =>
          some ⟨config.allocation, config.stack,
            .initializeSlotGroups object mixin.initializerGroups
              mixin.initializerBody⟩
      | .appliedMixin _ mixinMessage =>
          some (startMixinInitialization config.allocation rest current frames
            classId object mixinMessage)
  | _ => none

inductive InitializationCoordinatorStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | graph {before after : SequentialConfig}
      (next : p.initializationCoordinatorNext before = some after) :
      p.InitializationCoordinatorStep before after

theorem initializationCoordinatorStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.InitializationCoordinatorStep before after₁)
    (step₂ : p.InitializationCoordinatorStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | graph next₁ =>
      cases step₂ with
      | graph next₂ => exact Option.some.inj (next₁.symm.trans next₂)

theorem initializationCoordinatorStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.InitializationCoordinatorStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | graph next =>
      rcases before with ⟨state, stack, control⟩
      cases stack with
      | empty => simp [initializationCoordinatorNext] at next
      | push rest currentFrame =>
          rcases currentFrame with ⟨current, frames⟩
          cases control with
          | initClass classId object original =>
              cases classResult : state.heap.classes classId with
              | none =>
                  simp [initializationCoordinatorNext, classResult] at next
              | some classDef =>
                  by_cases atTop : classDef.superclass = p.top
                  · simp [initializationCoordinatorNext, classResult, atTop] at next
                    subst after
                    exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
                  · cases factoryResult : classDef.primaryFactory with
                    | none =>
                        simp [initializationCoordinatorNext, classResult, atTop,
                          factoryResult] at next
                    | some factory =>
                        simp [initializationCoordinatorNext, classResult, atTop,
                          factoryResult] at next
                        subst after
                        exact ⟨wf.heap, wf.supplies, by
                          simpa [startSuperclassInitialization, StackLive] using
                            wf.stack, trivial⟩
          | messageValue message =>
              cases frames with
              | empty => simp [initializationCoordinatorNext] at next
              | push below topFrame =>
                  cases topFrame with
                  | superclassMessage classId object original =>
                      cases classResult : state.heap.classes classId with
                      | none =>
                          simp [initializationCoordinatorNext, classResult] at next
                      | some classDef =>
                          let superclass := classDef.superclass
                          cases superclassResult : state.heap.classes superclass with
                          | none =>
                              simp [initializationCoordinatorNext, classResult,
                                superclass, superclassResult] at next
                          | some superclassDef =>
                              cases factoryResult : superclassDef.primaryFactory with
                              | none =>
                                  simp [initializationCoordinatorNext, classResult,
                                    superclass, superclassResult,
                                    factoryResult] at next
                              | some factory =>
                                  by_cases messageMatches : message.matchesInitializer
                                      factory.selector factory.parameters = true
                                  · simp [initializationCoordinatorNext, classResult,
                                      superclass, superclassResult, factoryResult,
                                      messageMatches] at next
                                    subst after
                                    apply p.invokeSuperclassInitializer_wellFormed
                                      wf.heap wf.supplies
                                    · simpa [StackLive] using wf.stack
                                    · exact superclassResult
                                  · simp [initializationCoordinatorNext, classResult,
                                      superclass, superclassResult, factoryResult,
                                      messageMatches] at next
                                    subst after
                                    exact ⟨wf.heap, wf.supplies, by
                                      simpa [StackLive] using wf.stack, trivial⟩
                  | mixinMessage classId object =>
                      cases classResult : state.heap.classes classId with
                      | none =>
                          simp [initializationCoordinatorNext, classResult] at next
                      | some classDef =>
                          cases mixinResult : p.mixins classDef.mixin with
                          | none =>
                              simp [initializationCoordinatorNext, classResult,
                                mixinResult] at next
                          | some mixin =>
                              by_cases messageMatches : message.matchesInitializer
                                  mixin.initializerSelector
                                  mixin.initializerParameters = true
                              · simp [initializationCoordinatorNext, classResult,
                                  mixinResult, messageMatches] at next
                                subst after
                                apply p.invokeMixinInitializer_wellFormed wf.heap
                                  wf.supplies
                                · simpa [StackLive] using wf.stack
                                · exact classResult
                              · simp [initializationCoordinatorNext, classResult,
                                  mixinResult, messageMatches] at next
                                subst after
                                exact ⟨wf.heap, wf.supplies, by
                                  simpa [StackLive] using wf.stack, trivial⟩
                  | receiver selector arguments =>
                      simp [initializationCoordinatorNext] at next
                  | asyncReceiver selector arguments =>
                      simp [initializationCoordinatorNext] at next
                  | arguments request selector values remaining =>
                      simp [initializationCoordinatorNext] at next
                  | initializeLocal slot remaining body target =>
                      simp [initializationCoordinatorNext] at next
                  | localWrite activation slot =>
                      simp [initializationCoordinatorNext] at next
                  | slotWrite object slot =>
                      simp [initializationCoordinatorNext] at next
                  | lazySlotStore object slot =>
                      simp [initializationCoordinatorNext] at next
                  | makeClassBody descriptor enclosingObject =>
                      simp [initializationCoordinatorNext] at next
                  | makeObjectLiteral descriptor enclosingObject =>
                      simp [initializationCoordinatorNext] at next
                  | nestedClassStore object declaration =>
                      simp [initializationCoordinatorNext] at next
                  | mixinSuperclass descriptor mixinSource =>
                      simp [initializationCoordinatorNext] at next
                  | mixinSource descriptor superclass =>
                      simp [initializationCoordinatorNext] at next
                  | messageArguments selector values remaining =>
                      simp [initializationCoordinatorNext] at next
                  | afterSuperclass classId object original =>
                      simp [initializationCoordinatorNext] at next
                  | afterMixin classId object =>
                      simp [initializationCoordinatorNext] at next
                  | storeInitializedSlot object slot declarations groups body =>
                      simp [initializationCoordinatorNext] at next
                  | simultaneousSlots code object groups body =>
                      simp [initializationCoordinatorNext] at next
                  | simultaneousLocals code activation remaining body target =>
                      simp [initializationCoordinatorNext] at next
                  | sequence target remaining =>
                      simp [initializationCoordinatorNext] at next
                  | returnFrame => simp [initializationCoordinatorNext] at next
          | object value =>
              cases value with
              | ordinaryObject result =>
                  cases frames with
                  | empty => simp [initializationCoordinatorNext] at next
                  | push below topFrame =>
                      cases topFrame with
                      | afterSuperclass classId object original =>
                          by_cases sameObject : result = object
                          · simp [initializationCoordinatorNext, sameObject] at next
                            subst after
                            exact ⟨wf.heap, wf.supplies, by
                              simpa [StackLive] using wf.stack, trivial⟩
                          · simp [initializationCoordinatorNext, sameObject] at next
                      | afterMixin classId object =>
                          by_cases sameObject : result = object
                          · simp [initializationCoordinatorNext, sameObject] at next
                            subst after
                            exact ⟨wf.heap, wf.supplies, by
                              simpa [StackLive] using wf.stack, trivial⟩
                          · simp [initializationCoordinatorNext, sameObject] at next
                      | receiver selector arguments =>
                          simp [initializationCoordinatorNext] at next
                      | asyncReceiver selector arguments =>
                          simp [initializationCoordinatorNext] at next
                      | arguments request selector values remaining =>
                          simp [initializationCoordinatorNext] at next
                      | initializeLocal slot remaining body target =>
                          simp [initializationCoordinatorNext] at next
                      | localWrite activation slot =>
                          simp [initializationCoordinatorNext] at next
                      | slotWrite object slot =>
                          simp [initializationCoordinatorNext] at next
                      | lazySlotStore object slot =>
                          simp [initializationCoordinatorNext] at next
                      | makeClassBody descriptor enclosingObject =>
                          simp [initializationCoordinatorNext] at next
                      | makeObjectLiteral descriptor enclosingObject =>
                          simp [initializationCoordinatorNext] at next
                      | nestedClassStore object declaration =>
                          simp [initializationCoordinatorNext] at next
                      | mixinSuperclass descriptor mixinSource =>
                          simp [initializationCoordinatorNext] at next
                      | mixinSource descriptor superclass =>
                          simp [initializationCoordinatorNext] at next
                      | messageArguments selector values remaining =>
                          simp [initializationCoordinatorNext] at next
                      | superclassMessage classId object original =>
                          simp [initializationCoordinatorNext] at next
                      | mixinMessage classId object =>
                          simp [initializationCoordinatorNext] at next
                      | storeInitializedSlot object slot declarations groups body =>
                          simp [initializationCoordinatorNext] at next
                      | simultaneousSlots code object groups body =>
                          simp [initializationCoordinatorNext] at next
                      | simultaneousLocals code activation remaining body target =>
                          simp [initializationCoordinatorNext] at next
                      | sequence target remaining =>
                          simp [initializationCoordinatorNext] at next
                      | returnFrame => simp [initializationCoordinatorNext] at next
              | classObject id => simp [initializationCoordinatorNext] at next
              | mixinObject id => simp [initializationCoordinatorNext] at next
              | activationObject id => simp [initializationCoordinatorNext] at next
              | closureObject id => simp [initializationCoordinatorNext] at next
              | mirrorObject id => simp [initializationCoordinatorNext] at next
              | actorObject id => simp [initializationCoordinatorNext] at next
          | ownInitialization classId object original =>
              cases classResult : state.heap.classes classId with
              | none =>
                  simp [initializationCoordinatorNext, classResult] at next
              | some classDef =>
                  cases factoryResult : classDef.primaryFactory with
                  | none =>
                      simp [initializationCoordinatorNext, classResult,
                        factoryResult] at next
                  | some factory =>
                      cases mixinResult : p.mixins classDef.mixin with
                      | none =>
                          simp [initializationCoordinatorNext, classResult,
                            factoryResult, mixinResult] at next
                      | some mixin =>
                          cases planResult : factory.plan with
                          | body superclassMessage =>
                              simp [initializationCoordinatorNext, classResult,
                                factoryResult, mixinResult, planResult] at next
                              subst after
                              exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
                          | appliedMixin superclassMessage mixinMessage =>
                              simp [initializationCoordinatorNext, classResult,
                                factoryResult, mixinResult, planResult] at next
                              subst after
                              exact ⟨wf.heap, wf.supplies, by
                                simpa [startMixinInitialization, StackLive] using
                                  wf.stack, trivial⟩
          | evaluate expression => simp [initializationCoordinatorNext] at next
          | evaluateMessage template =>
              simp [initializationCoordinatorNext] at next
          | dispatch request message => simp [initializationCoordinatorNext] at next
          | invoke method receiver definingClass message =>
              simp [initializationCoordinatorNext] at next
          | invokeClosure closure message =>
              simp [initializationCoordinatorNext] at next
          | «initialize» activation groups body target =>
              simp [initializationCoordinatorNext] at next
          | body target statements => simp [initializationCoordinatorNext] at next
          | finish value => simp [initializationCoordinatorNext] at next
          | transfer target value => simp [initializationCoordinatorNext] at next
          | halt value => simp [initializationCoordinatorNext] at next
          | abort exception => simp [initializationCoordinatorNext] at next
          | throw error => simp [initializationCoordinatorNext] at next
          | runtimeError error => simp [initializationCoordinatorNext] at next
          | initializeSlotGroups object groups body =>
              simp [initializationCoordinatorNext] at next
          | initializeSequentialSlots object declarations remaining body =>
              simp [initializationCoordinatorNext] at next

end Program
end Newspeak
