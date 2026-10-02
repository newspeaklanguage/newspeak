import Newspeak.InstanceAllocation

namespace Newspeak

/-- An initializer activation is a home activation in its own right.  Its
    declaration is visible to closures created while initialization runs. -/
def initializerActivationScopes (declaration : ActivationDeclId)
    (id : ActivationId) : FiniteStore ActivationDeclId ActivationId :=
  (FiniteStore.empty ActivationDeclId ActivationId).install declaration id

@[simp] theorem mem_initializerActivationScopes_domain_iff
    (declaration query : ActivationDeclId) (id : ActivationId) :
    query ∈ (initializerActivationScopes declaration id).domain ↔
      query = declaration := by
  change query ∈
      ((FiniteStore.empty ActivationDeclId ActivationId).install
        declaration id).domain ↔ _
  rw [FiniteStore.mem_install_domain_iff]
  simp

namespace Program

def activationParameterValues (activation : ActivationDef) :
    List ParameterId → Option (List ObjRef)
  | [] => some []
  | parameter :: remaining => do
      let value ← activation.parameters parameter
      let values ← activationParameterValues activation remaining
      some (value :: values)

theorem activationParameterValues_length {activation : ActivationDef}
    {parameters : List ParameterId} {values : List ObjRef}
    (read : activationParameterValues activation parameters = some values) :
    values.length = parameters.length := by
  induction parameters generalizing values with
  | nil => simp [activationParameterValues] at read; subst values; rfl
  | cons parameter remaining ih =>
      cases valueResult : activation.parameters parameter with
      | none => simp [activationParameterValues, valueResult] at read
      | some value =>
          cases valuesResult : activationParameterValues activation remaining with
          | none =>
              simp [activationParameterValues, valueResult, valuesResult] at read
          | some tail =>
              simp [activationParameterValues, valueResult, valuesResult] at read
              subst values
              simp [ih valuesResult]

/-- Equation (9.13): the activation that coordinates initialization of one
    class in an instance's superclass chain. -/
def initializerActivationDefinition (p : Program) (id : ActivationId)
    (factory : FactoryDef) (classId : ClassId) (object : ObjectId)
    (message : Message) (continuation : Option ActivationId) : ActivationDef :=
  { objectClass := p.activationClass
    provenance := .initializer factory.activationDeclaration
    parameters := bindParameters factory.parameters message.arguments
    locals := FiniteStore.empty LocalSlotId LocalCell
    currentReceiver := .ordinaryObject object
    currentClass := some classId
    continuation := continuation
    homeMethod := some id
    continuable := true
    activationScopes := initializerActivationScopes
      factory.activationDeclaration id
    objectLiteralScopes := FiniteStore.empty ObjectLiteralDeclId ObjRef }

def allocateInitializerActivation (p : Program) (state : AllocationState)
    (factory : FactoryDef) (classId : ClassId) (object : ObjectId)
    (message : Message) (continuation : Option ActivationId) :
    AllocationState × ActivationId :=
  let id : ActivationId := ⟨state.nextActivation⟩
  let activation := p.initializerActivationDefinition id factory classId object
    message continuation
  ({ state with
      heap := state.heap.installActivation id activation
      nextActivation := state.nextActivation + 1 }, id)

@[simp] theorem allocateInitializerActivation_reference (p : Program)
    (state : AllocationState) (factory : FactoryDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    (p.allocateInitializerActivation state factory classId object message
      continuation).2 = ⟨state.nextActivation⟩ := by
  rfl

@[simp] theorem allocateInitializerActivation_installs (p : Program)
    (state : AllocationState) (factory : FactoryDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateInitializerActivation state factory classId
      object message continuation
    allocation.1.heap.activations allocation.2 =
      some (p.initializerActivationDefinition allocation.2 factory classId
        object message continuation) := by
  simp [allocateInitializerActivation]

theorem allocateInitializerActivation_was_fresh (_p : Program)
    {state : AllocationState} (fresh : state.ActivationSupplyFresh)
    (_factory : FactoryDef) (_classId : ClassId) (_object : ObjectId)
    (_message : Message) (_continuation : Option ActivationId) :
    state.heap.activations ⟨state.nextActivation⟩ = none :=
  fresh ⟨state.nextActivation⟩ (Nat.le_refl _)

theorem allocateInitializerActivation_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (factory : FactoryDef) (classId : ClassId) (object : ObjectId)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateInitializerActivation state factory classId object message
      continuation).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id bound
    exact fresh.1 id (by
      simpa [allocateInitializerActivation] using bound)
  · intro id bound
    have later : state.nextActivation + 1 ≤ id.index := by
      simpa [allocateInitializerActivation] using bound
    have away : id ≠ (⟨state.nextActivation⟩ : ActivationId) := by
      intro equal
      have indexEqual := congrArg ActivationId.index equal
      simp at indexEqual
      omega
    rw [show (p.allocateInitializerActivation state factory classId object
      message continuation).1.heap =
      state.heap.installActivation ⟨state.nextActivation⟩
        (p.initializerActivationDefinition ⟨state.nextActivation⟩ factory
          classId object message continuation) by rfl]
    rw [Heap.installActivation_away _ _ away]
    exact fresh.2.1 id (by omega)
  · intro id bound
    exact fresh.2.2.1 id (by
      simpa [allocateInitializerActivation] using bound)
  · intro id bound
    exact fresh.2.2.2.1 id (by
      simpa [allocateInitializerActivation] using bound)
  · intro id bound
    exact fresh.2.2.2.2 id (by
      simpa [allocateInitializerActivation] using bound)

theorem allocateInitializerActivation_sets_context (p : Program)
    (state : AllocationState) (factory : FactoryDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateInitializerActivation state factory classId
      object message continuation
    ∃ activation,
      allocation.1.heap.activations allocation.2 = some activation ∧
      activation.provenance = .initializer factory.activationDeclaration ∧
      activation.currentReceiver = .ordinaryObject object ∧
      activation.currentClass = some classId ∧
      activation.continuation = continuation ∧
      activation.homeMethod = some allocation.2 ∧
      activation.activationScopes factory.activationDeclaration =
        some allocation.2 := by
  let activation := p.initializerActivationDefinition ⟨state.nextActivation⟩
    factory classId object message continuation
  refine ⟨activation, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [allocateInitializerActivation, activation]
  · simp [activation, initializerActivationDefinition,
      initializerActivationScopes]

theorem allocateInitializerActivation_returns_from_self (p : Program)
    (state : AllocationState) (factory : FactoryDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateInitializerActivation state factory classId
      object message continuation
    allocation.1.heap.returnTarget allocation.2 = some allocation.2 := by
  simp [allocateInitializerActivation, initializerActivationDefinition,
    Heap.returnTarget]

theorem allocateInitializerActivation_wellFormed (p : Program)
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (factory : FactoryDef)
    (classId : ClassId) (classLive : p.IsLiveClass state.heap classId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    p.WellFormed (p.allocateInitializerActivation state factory classId object
        message continuation).1.heap ∧
      (p.allocateInitializerActivation state factory classId object message
        continuation).1.SuppliesFresh := by
  constructor
  · apply wf.installActivation_wellFormed
    · simpa [initializerActivationDefinition] using wf.activationClassIsLive
    · simpa [initializerActivationDefinition, OptionalClassLive] using classLive
  · exact p.allocateInitializerActivation_preserves_supplies fresh factory
      classId object message continuation

/-- The two fresh identities and resulting state produced by Factory-New. -/
structure InitialInstanceAllocation where
  state : AllocationState
  object : ObjectId
  initializer : ActivationId

/-- Allocate the object first, so every physical slot exists and contains nil,
    then allocate the initializer activation that coordinates its class chain. -/
def allocateInitialInstance (p : Program) (state : AllocationState)
    (classId : ClassId) (layout : List SlotId) (factory : FactoryDef)
    (message : Message) (continuation : Option ActivationId) :
    InitialInstanceAllocation :=
  let objectAllocation := p.allocateInstance state classId layout p.nilObject
  let initializerAllocation := p.allocateInitializerActivation
    objectAllocation.1 factory classId objectAllocation.2 message continuation
  { state := initializerAllocation.1
    object := objectAllocation.2
    initializer := initializerAllocation.2 }

@[simp] theorem allocateInitialInstance_object (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (factory : FactoryDef) (message : Message)
    (continuation : Option ActivationId) :
    (p.allocateInitialInstance state classId layout factory message
      continuation).object = ⟨state.nextObject⟩ := by
  rfl

@[simp] theorem allocateInitialInstance_initializer (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (factory : FactoryDef) (message : Message)
    (continuation : Option ActivationId) :
    (p.allocateInitialInstance state classId layout factory message
      continuation).initializer = ⟨state.nextActivation⟩ := by
  rfl

theorem allocateInitialInstance_installs_object (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (factory : FactoryDef) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateInitialInstance state classId layout factory
      message continuation
    allocation.state.heap.objects allocation.object =
      some { classId := classId
             slots := slotsInitializedTo layout p.nilObject
             nestedClasses := FiniteStore.empty ClassDeclId ClassId } := by
  simp [allocateInitialInstance, allocateInitializerActivation,
    allocateInstance, Heap.installActivation]

theorem allocateInitialInstance_installs_initializer (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List SlotId)
    (factory : FactoryDef) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateInitialInstance state classId layout factory
      message continuation
    allocation.state.heap.activations allocation.initializer =
      some (p.initializerActivationDefinition allocation.initializer factory
        classId allocation.object message continuation) := by
  simp [allocateInitialInstance, allocateInitializerActivation,
    allocateInstance]

theorem allocateInitialInstance_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (classId : ClassId) (layout : List SlotId) (factory : FactoryDef)
    (message : Message) (continuation : Option ActivationId) :
    (p.allocateInitialInstance state classId layout factory message
      continuation).state.SuppliesFresh := by
  exact p.allocateInitializerActivation_preserves_supplies
    (p.allocateInstance_preserves_supplies fresh classId layout p.nilObject)
    factory classId ⟨state.nextObject⟩ message continuation

theorem allocateInitialInstance_wellFormed (p : Program)
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (classId : ClassId)
    (classLive : p.IsLiveClass state.heap classId) (layout : List SlotId)
    (factory : FactoryDef) (message : Message)
    (continuation : Option ActivationId) :
    let allocation := p.allocateInitialInstance state classId layout factory
      message continuation
    p.WellFormed allocation.state.heap ∧ allocation.state.SuppliesFresh := by
  let objectAllocation := p.allocateInstance state classId layout p.nilObject
  have objectWellFormed := p.allocateInstance_wellFormed wf fresh classId
    classLive layout p.nilObject
  have classLiveAfter :
      p.IsLiveClass objectAllocation.1.heap classId := by
    simpa [objectAllocation, allocateInstance, Program.IsLiveClass,
      Heap.installObject] using classLive
  have initializerWellFormed := p.allocateInitializerActivation_wellFormed
    objectWellFormed.1 objectWellFormed.2 factory classId classLiveAfter
    objectAllocation.2 message continuation
  simpa [allocateInitialInstance, objectAllocation] using initializerWellFormed

def factoryNewResult (p : Program) (state : AllocationState)
    (rest : ActivationStack) (factoryActivation : ActivationId)
    (frames : EvalStack) (classId : ClassId) (layout : List SlotId)
    (factory : FactoryDef) (message : Message) : SequentialConfig :=
  let allocation := p.allocateInitialInstance state classId layout factory
    message (some factoryActivation)
  ⟨allocation.state,
    .push (.push rest ⟨factoryActivation, .push frames .returnFrame⟩)
      ⟨allocation.initializer, .empty⟩,
    .initClass classId allocation.object message⟩

/-- Rule Factory-New.  The synthesized primary-factory body is the only
    source of `newInstanceCurrent`; the rule both allocates the instance and
    starts its initializer coordinator. -/
inductive FactoryNewStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | allocate {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {activation : ActivationDef} {classId : ClassId} {classDef : ClassDef}
      {factory : FactoryDef} {selector : Selector}
      {parameters : List ParameterId} {arguments : List ObjRef}
      {layout : List SlotId}
      (activationLive : state.heap.activations current = some activation)
      (receiver : activation.currentReceiver = .classObject classId)
      (classLive : state.heap.classes classId = some classDef)
      (factoryLive : classDef.primaryFactory = some factory)
      (selectorMatches : selector = factory.selector)
      (parametersMatch : parameters = factory.parameters)
      (argumentsRead : activationParameterValues activation parameters =
        some arguments)
      (layoutWitness : p.InstanceLayout state.heap classId layout) :
      FactoryNewStep p
        ⟨state, .push rest ⟨current, .push frames .returnFrame⟩,
          .evaluate (.newInstanceCurrent selector parameters)⟩
        (p.factoryNewResult state rest current frames classId layout factory
          ⟨selector, arguments⟩)

theorem factoryNewStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.FactoryNewStep before after₁)
    (step₂ : p.FactoryNewStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | @allocate state rest current frames activation₁ classId₁ classDef₁
      factory₁ selector parameters arguments₁ layout₁ activationLive₁ receiver₁
      classLive₁ factoryLive₁ selectorMatches₁ parametersMatch₁ argumentsRead₁
      layoutWitness₁ =>
      cases step₂ with
      | @allocate _ _ _ _ activation₂ classId₂ classDef₂ factory₂ _ _
          arguments₂ layout₂ activationLive₂ receiver₂ classLive₂ factoryLive₂
          selectorMatches₂ parametersMatch₂ argumentsRead₂ layoutWitness₂ =>
          have activationEqual := Option.some.inj
            (activationLive₁.symm.trans activationLive₂)
          subst activation₂
          have classEqual := ObjRef.classObject.inj
            (receiver₁.symm.trans receiver₂)
          subst classId₂
          have classDefEqual := Option.some.inj
            (classLive₁.symm.trans classLive₂)
          subst classDef₂
          have factoryEqual := Option.some.inj
            (factoryLive₁.symm.trans factoryLive₂)
          subst factory₂
          have argumentsEqual := Option.some.inj
            (argumentsRead₁.symm.trans argumentsRead₂)
          subst arguments₂
          have layoutEqual := instanceLayout_unique layoutWitness₁ layoutWitness₂
          subst layout₂
          rfl

theorem allocateInitialInstance_retains_activations (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (classId : ClassId) (layout : List SlotId) (factory : FactoryDef)
    (message : Message) (continuation : Option ActivationId) :
    ∀ id activation, state.heap.activations id = some activation →
      ∃ activation',
        (p.allocateInitialInstance state classId layout factory message
          continuation).state.heap.activations id = some activation' := by
  intro id activation live
  have initializerFresh :
      (p.allocateInstance state classId layout p.nilObject).1.heap.activations
        ⟨state.nextActivation⟩ = none := by
    simpa [allocateInstance, Heap.installObject] using
      fresh.2.1 ⟨state.nextActivation⟩ (Nat.le_refl _)
  have oldLive :
      (p.allocateInstance state classId layout p.nilObject).1.heap.activations id =
        some activation := by
    simpa [allocateInstance, Heap.installObject] using live
  exact Heap.installActivation_fresh_retains
    (p.allocateInstance state classId layout p.nilObject).1.heap
    ⟨state.nextActivation⟩
    (p.initializerActivationDefinition ⟨state.nextActivation⟩ factory classId
      ⟨state.nextObject⟩ message continuation) initializerFresh id activation
    (by simpa [allocateInitialInstance, allocateInitializerActivation,
      allocateInstance] using oldLive)

theorem factoryNewStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.FactoryNewStep before after) : SequentialWellFormed p after := by
  cases step with
  | @allocate state rest current frames activation classId classDef factory
      selector parameters arguments layout activationLive receiver classLive
      factoryLive selectorMatches parametersMatch argumentsRead layoutWitness =>
      let message : Message := ⟨selector, arguments⟩
      have liveClass : p.IsLiveClass state.heap classId :=
        Or.inr ⟨classDef, classLive⟩
      have allocatedWellFormed := p.allocateInitialInstance_wellFormed wf.heap
        wf.supplies classId liveClass layout factory message (some current)
      let allocation := p.allocateInitialInstance state classId layout factory
        message (some current)
      have oldStackLive : StackLive allocation.state.heap
          (.push rest ⟨current, .push frames .returnFrame⟩) :=
        stackLive_transport wf.stack
          (p.allocateInitialInstance_retains_activations wf.supplies classId
            layout factory message (some current))
      have initializerLive : allocation.state.heap.activations
          allocation.initializer =
          some (p.initializerActivationDefinition allocation.initializer factory
            classId allocation.object message (some current)) := by
        exact p.allocateInitialInstance_installs_initializer state classId
          layout factory message (some current)
      exact ⟨allocatedWellFormed.1, allocatedWellFormed.2,
        ⟨oldStackLive, _, initializerLive⟩, trivial⟩

/-- Factory-New allocates exactly the fresh object at the object-supply
    frontier, installs the complete nil-initialized physical layout, and
    preserves the class record selected by the factory activation. -/
theorem factoryNewStep_allocates_fresh_instance {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.FactoryNewStep before after) :
    ∃ object classId classDef layout,
      object = (⟨before.allocation.nextObject⟩ : ObjectId) ∧
      before.allocation.heap.objects object = none ∧
      before.allocation.heap.classes classId = some classDef ∧
      after.allocation.heap.classes classId = some classDef ∧
      after.allocation.heap.objects object = some
        { classId := classId
          slots := slotsInitializedTo layout p.nilObject
          nestedClasses := FiniteStore.empty ClassDeclId ClassId } := by
  cases step with
  | @allocate state rest current frames activation classId classDef factory
      selector parameters arguments layout activationLive receiver classLive
      factoryLive selectorMatches parametersMatch argumentsRead layoutWitness =>
      let message : Message := ⟨selector, arguments⟩
      let allocation := p.allocateInitialInstance state classId layout factory
        message (some current)
      refine ⟨allocation.object, classId, classDef, layout, ?_, ?_, classLive,
        ?_, ?_⟩
      · rfl
      · exact wf.supplies.2.2.2.1 allocation.object (by
          simp [allocation, allocateInitialInstance])
      · simpa [factoryNewResult, allocation, allocateInitialInstance,
          allocateInitializerActivation, allocateInstance,
          Heap.installActivation, Heap.installObject] using classLive
      · simpa [factoryNewResult, allocation] using
          p.allocateInitialInstance_installs_object state classId layout factory
            message (some current)

theorem sequentialStep_factoryNew_disjoint {p : Program}
    {before sequentialAfter factoryAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (factory : p.FactoryNewStep before factoryAfter) : False := by
  cases factory with
  | allocate =>
      cases sequential with
      | expression expression =>
          cases expression with
          | nonOrdinary requestData =>
              simp [nonOrdinaryRequest] at requestData
      | request request => cases request
      | invocation invocation => cases invocation
      | body body =>
          cases body with
          | graph next => simp [bodyMachineNext] at next
      | returns returns =>
          cases returns with
          | graph next => simp [returnMachineNext] at next
      | closure closure =>
          cases closure with
          | creation creation => cases creation
          | dispatch dispatch => cases dispatch
          | invocation invocation => cases invocation
      | objectSlots slots => cases slots
      | classes classes => cases classes
      | messages messages => cases messages

/-- The sequential relation through Factory-New.  It has a distinct name
    because subsequent initialization phases will extend it again. -/
inductive SequentialStepWithFactory (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      p.SequentialStep before after → p.SequentialStepWithFactory before after
  | factory {before after : SequentialConfig} :
      p.FactoryNewStep before after → p.SequentialStepWithFactory before after

theorem sequentialStepWithFactory_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (step₁ : p.SequentialStepWithFactory before after₁)
    (step₂ : p.SequentialStepWithFactory before after₂) : after₁ = after₂ := by
  cases step₁ with
  | prior prior₁ =>
      cases step₂ with
      | prior prior₂ => exact sequentialStep_deterministic wf prior₁ prior₂
      | factory factory₂ =>
          exact (sequentialStep_factoryNew_disjoint prior₁ factory₂).elim
  | factory factory₁ =>
      cases step₂ with
      | prior prior₂ =>
          exact (sequentialStep_factoryNew_disjoint prior₂ factory₁).elim
      | factory factory₂ => exact factoryNewStep_deterministic factory₁ factory₂

theorem sequentialStepWithFactory_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.SequentialStepWithFactory before after) :
    SequentialWellFormed p after := by
  cases step with
  | prior prior => exact sequentialStep_preserves_wellFormed wf prior
  | factory factory => exact factoryNewStep_preserves_wellFormed wf factory

end Program
end Newspeak
