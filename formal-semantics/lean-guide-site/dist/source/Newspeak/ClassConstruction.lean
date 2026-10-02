import Newspeak.ObjectSlots

namespace Newspeak

namespace Program

def inheritanceError (h : Heap) (value : ObjRef)
    (message : MessageTemplate) : Option RuntimeError :=
  match value with
  | .classObject classId =>
      match h.classes classId with
      | none => some .classExpected
      | some classDef =>
          match classDef.primaryFactory with
          | none => some .classNotInstantiable
          | some factory =>
              if factory.selector = message.selector then none
              else some .wrongFactory
  | _ => some .classExpected

def classEnclosingObject (p : Program) (h : Heap) (activation : ActivationId)
    (declaration : ClassDeclId) : Option ObjRef :=
  match p.classOwner declaration with
  | .activationOwner => some (.activationObject activation)
  | .classOwner | .objectLiteralOwner =>
      (h.activations activation).map ActivationDef.currentReceiver
  | .topOwner => some p.nilObject

def bodyFactory (descriptor : ClassBodyDescriptor) : FactoryDef :=
  { activationDeclaration := descriptor.initializerDeclaration
    selector := descriptor.factorySelector
    parameters := descriptor.factoryParameters
    plan := .body descriptor.superclassMessage }

def applicationFactory (descriptor : MixinApplicationDescriptor) : FactoryDef :=
  { activationDeclaration := descriptor.initializerDeclaration
    selector := descriptor.factorySelector
    parameters := descriptor.factoryParameters
    plan := .appliedMixin descriptor.superclassMessage descriptor.mixinMessage }

/-- Equation (9.5).  `nextClass` supplies the metaclass, and its successor the
    class proper; the returned reference is always the latter. -/
def allocateClassPair (p : Program) (state : AllocationState)
    (origin : ClassOrigin) (instanceMixin classMixin : MixinId)
    (superclass : ClassId) (enclosingObject : ObjRef)
    (factory : FactoryDef) : AllocationState × ClassId × ClassId :=
  let metaclassId : ClassId := ⟨state.nextClass⟩
  let classId : ClassId := ⟨state.nextClass + 1⟩
  let metaclassDef : ClassDef :=
    { mixin := classMixin
      superclass := p.classClass
      enclosingObject := enclosingObject
      metaclass := p.metaclassClass
      origin := origin
      primaryFactory := none }
  let classDef : ClassDef :=
    { mixin := instanceMixin
      superclass := superclass
      enclosingObject := enclosingObject
      metaclass := metaclassId
      origin := origin
      primaryFactory := some factory }
  let heap := (state.heap.installClass metaclassId metaclassDef).installClass
    classId classDef
  ({ state with heap := heap, nextClass := state.nextClass + 2 },
    classId, metaclassId)

def validTopSuperclass (p : Program) (enclosingObject : ObjRef)
    (superclassSyntax : SuperclassSyntax) (superclass : ClassId) : Bool :=
  enclosingObject != p.nilObject ||
    (superclassSyntax == .implicitSuperclass && superclass == p.object)

inductive ClassConstructionStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | bodyStart {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {declaration : ClassDeclId}
      {superclassExpression : CoreExpr} {descriptor : ClassBodyDescriptor}
      {enclosingObject : ObjRef}
      (descriptorFound : p.classBodies declaration = some descriptor)
      (enclosingFound : p.classEnclosingObject state.heap current declaration =
        some enclosingObject) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.classBody declaration superclassExpression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor enclosingObject)⟩,
          .evaluate superclassExpression⟩
  | bodyCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ClassBodyDescriptor} {enclosingObject : ObjRef}
      {superclass : ClassId} {allocation : AllocationState × ClassId × ClassId}
      (inheritanceValid :
        inheritanceError state.heap (.classObject superclass)
          descriptor.superclassMessage = none)
      (topValid : p.validTopSuperclass enclosingObject
        descriptor.superclassSyntax superclass = true)
      (allocated : allocation = p.allocateClassPair state
        (.expression (.namedClass descriptor.declaration))
        descriptor.instanceMixin descriptor.classMixin superclass enclosingObject
        (bodyFactory descriptor))
      (allocationWellFormed : p.WellFormed allocation.1.heap) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor enclosingObject)⟩,
          .object (.classObject superclass)⟩
        ⟨allocation.1, .push rest ⟨current, frames⟩,
          .object (.classObject allocation.2.1)⟩
  | bodyInheritanceError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ClassBodyDescriptor} {enclosingObject : ObjRef}
      {value : ObjRef} {error : RuntimeError}
      (invalid : inheritanceError state.heap value
        descriptor.superclassMessage = some error) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor enclosingObject)⟩, .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
  | bodyTopError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ClassBodyDescriptor} {superclass : ClassId}
      (inheritanceValid :
        inheritanceError state.heap (.classObject superclass)
          descriptor.superclassMessage = none)
      (topInvalid : p.validTopSuperclass p.nilObject
        descriptor.superclassSyntax superclass = false) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor p.nilObject)⟩,
          .object (.classObject superclass)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .runtimeError .topSuperclass⟩
  | mixinStart {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {declaration : ClassDeclId}
      {superclassExpression mixinExpression : CoreExpr}
      {descriptor : MixinApplicationDescriptor}
      (descriptorFound : p.mixinApplications declaration = some descriptor) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.mixinApply declaration superclassExpression mixinExpression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSuperclass descriptor mixinExpression)⟩,
          .evaluate superclassExpression⟩
  | mixinSuperclassDone {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {mixinExpression : CoreExpr}
      {superclass : ClassId}
      (valid : inheritanceError state.heap (.classObject superclass)
        descriptor.superclassMessage = none) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSuperclass descriptor mixinExpression)⟩,
          .object (.classObject superclass)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSource descriptor superclass)⟩,
          .evaluate mixinExpression⟩
  | mixinCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {superclass source : ClassId}
      {sourceDef : ClassDef} {sourceFactory : FactoryDef}
      {allocation : AllocationState × ClassId × ClassId}
      (sourceFound : state.heap.classes source = some sourceDef)
      (factoryFound : sourceDef.primaryFactory = some sourceFactory)
      (mixinMessageValid : sourceFactory.selector = descriptor.mixinMessage.selector)
      (factoryMatches : sourceFactory.selector = descriptor.factorySelector)
      (allocated : allocation = p.allocateClassPair state
        (.expression (.namedClass descriptor.declaration)) sourceDef.mixin
        descriptor.classMixin superclass sourceDef.enclosingObject
        (applicationFactory descriptor))
      (allocationWellFormed : p.WellFormed allocation.1.heap) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSource descriptor superclass)⟩,
          .object (.classObject source)⟩
        ⟨allocation.1, .push rest ⟨current, frames⟩,
          .object (.classObject allocation.2.1)⟩
  | mixinSuperclassError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {mixinExpression : CoreExpr}
      {value : ObjRef} {error : RuntimeError}
      (invalid : inheritanceError state.heap value
        descriptor.superclassMessage = some error) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSuperclass descriptor mixinExpression)⟩, .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
  | mixinSourceError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {superclass : ClassId}
      {value : ObjRef} {error : RuntimeError}
      (invalid : inheritanceError state.heap value descriptor.mixinMessage =
        some error) :
      ClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSource descriptor superclass)⟩, .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩

@[simp] theorem allocateClassPair_result (p : Program) (state : AllocationState)
    (origin : ClassOrigin) (instanceMixin classMixin : MixinId)
    (superclass : ClassId) (enclosingObject : ObjRef) (factory : FactoryDef) :
    (p.allocateClassPair state origin instanceMixin classMixin superclass
      enclosingObject factory).2.1 = ⟨state.nextClass + 1⟩ := by rfl

@[simp] theorem allocateClassPair_metaclass (p : Program) (state : AllocationState)
    (origin : ClassOrigin) (instanceMixin classMixin : MixinId)
    (superclass : ClassId) (enclosingObject : ObjRef) (factory : FactoryDef) :
    (p.allocateClassPair state origin instanceMixin classMixin superclass
      enclosingObject factory).2.2 = ⟨state.nextClass⟩ := by rfl

theorem allocateClassPair_fresh_distinct (state : AllocationState) :
    (⟨state.nextClass⟩ : ClassId) ≠ ⟨state.nextClass + 1⟩ := by
  intro equal
  have := congrArg ClassId.index equal
  simp at this

theorem allocateClassPair_was_fresh (p : Program) {state : AllocationState}
    (fresh : state.ClassSupplyFresh) (origin : ClassOrigin)
    (instanceMixin classMixin : MixinId) (superclass : ClassId)
    (enclosingObject : ObjRef) (factory : FactoryDef) :
    state.heap.classes
        (p.allocateClassPair state origin instanceMixin classMixin superclass
          enclosingObject factory).2.1 = none ∧
      state.heap.classes
        (p.allocateClassPair state origin instanceMixin classMixin superclass
          enclosingObject factory).2.2 = none := by
  constructor
  · exact fresh ⟨state.nextClass + 1⟩ (by simp)
  · exact fresh ⟨state.nextClass⟩ (by simp)

theorem allocateClassPair_installs (p : Program) (state : AllocationState)
    (origin : ClassOrigin) (instanceMixin classMixin : MixinId)
    (superclass : ClassId) (enclosingObject : ObjRef) (factory : FactoryDef) :
    let allocation := p.allocateClassPair state origin instanceMixin classMixin
      superclass enclosingObject factory
    allocation.1.heap.classes allocation.2.1 = some
        { mixin := instanceMixin, superclass := superclass
          enclosingObject := enclosingObject, metaclass := allocation.2.2
          origin := origin, primaryFactory := some factory } ∧
      allocation.1.heap.classes allocation.2.2 = some
        { mixin := classMixin, superclass := p.classClass
          enclosingObject := enclosingObject, metaclass := p.metaclassClass
          origin := origin, primaryFactory := none } := by
  simp [allocateClassPair, Heap.installClass]

theorem allocateClassPair_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (origin : ClassOrigin) (instanceMixin classMixin : MixinId)
    (superclass : ClassId) (enclosingObject : ObjRef) (factory : FactoryDef) :
    (p.allocateClassPair state origin instanceMixin classMixin superclass
      enclosingObject factory).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id bound
    exact fresh.1 id (by simpa [allocateClassPair] using bound)
  · intro id bound
    exact fresh.2.1 id (by simpa [allocateClassPair] using bound)
  · intro id bound
    exact fresh.2.2.1 id (by simpa [allocateClassPair] using bound)
  · intro id bound
    exact fresh.2.2.2.1 id (by simpa [allocateClassPair] using bound)
  · intro id bound
    have later : state.nextClass + 2 ≤ id.index := by
      simpa [allocateClassPair] using bound
    have awayClass : id ≠ (⟨state.nextClass + 1⟩ : ClassId) := by
      intro equal
      have indexEqual := congrArg ClassId.index equal
      simp at indexEqual
      omega
    have awayMetaclass : id ≠ (⟨state.nextClass⟩ : ClassId) := by
      intro equal
      have indexEqual := congrArg ClassId.index equal
      simp at indexEqual
      omega
    simp only [allocateClassPair]
    rw [Heap.installClass_away _ _ awayClass,
      Heap.installClass_away _ _ awayMetaclass]
    exact fresh.2.2.2.2 id (by omega)

theorem classConstructionStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ClassConstructionStep before after₁)
    (step₂ : p.ClassConstructionStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | bodyStart descriptor₁ enclosing₁ =>
      cases step₂ with
      | bodyStart descriptor₂ enclosing₂ =>
          have descriptorEqual := Option.some.inj
            (descriptor₁.symm.trans descriptor₂)
          subst descriptorEqual
          have enclosingEqual := Option.some.inj
            (enclosing₁.symm.trans enclosing₂)
          subst enclosingEqual
          rfl
  | bodyCommit valid₁ top₁ allocated₁ wf₁ =>
      cases step₂ with
      | bodyCommit valid₂ top₂ allocated₂ wf₂ =>
          rw [allocated₁, allocated₂]
      | bodyInheritanceError invalid₂ =>
          rw [valid₁] at invalid₂
          contradiction
      | bodyTopError valid₂ top₂ =>
          rw [top₁] at top₂
          contradiction
  | bodyInheritanceError invalid₁ =>
      cases step₂ with
      | bodyCommit valid₂ top₂ allocated₂ wf₂ =>
          rw [valid₂] at invalid₁
          contradiction
      | bodyInheritanceError invalid₂ =>
          have errorEqual := Option.some.inj (invalid₁.symm.trans invalid₂)
          subst errorEqual
          rfl
      | bodyTopError valid₂ top₂ =>
          rw [valid₂] at invalid₁
          contradiction
  | bodyTopError valid₁ top₁ =>
      cases step₂ with
      | bodyCommit valid₂ top₂ allocated₂ wf₂ =>
          rw [top₂] at top₁
          contradiction
      | bodyInheritanceError invalid₂ =>
          rw [valid₁] at invalid₂
          contradiction
      | bodyTopError valid₂ top₂ => rfl
  | mixinStart descriptor₁ =>
      cases step₂ with
      | mixinStart descriptor₂ =>
          have descriptorEqual := Option.some.inj
            (descriptor₁.symm.trans descriptor₂)
          subst descriptorEqual
          rfl
  | mixinSuperclassDone valid₁ =>
      cases step₂ with
      | mixinSuperclassDone valid₂ => rfl
      | mixinSuperclassError invalid₂ =>
          rw [valid₁] at invalid₂
          contradiction
  | mixinCommit source₁ factory₁ message₁ matches₁ allocated₁ wf₁ =>
      cases step₂ with
      | mixinCommit source₂ factory₂ message₂ matches₂ allocated₂ wf₂ =>
          have sourceEqual := Option.some.inj (source₁.symm.trans source₂)
          subst sourceEqual
          have factoryEqual := Option.some.inj
            (factory₁.symm.trans factory₂)
          subst factoryEqual
          rw [allocated₁, allocated₂]
      | mixinSourceError invalid₂ =>
          simp [inheritanceError, source₁, factory₁, message₁] at invalid₂
  | mixinSuperclassError invalid₁ =>
      cases step₂ with
      | mixinSuperclassDone valid₂ =>
          rw [valid₂] at invalid₁
          contradiction
      | mixinSuperclassError invalid₂ =>
          have errorEqual := Option.some.inj (invalid₁.symm.trans invalid₂)
          subst errorEqual
          rfl
  | mixinSourceError invalid₁ =>
      cases step₂ with
      | mixinCommit source₂ factory₂ message₂ matches₂ allocated₂ wf₂ =>
          simp [inheritanceError, source₂, factory₂, message₂] at invalid₁
      | mixinSourceError invalid₂ =>
          have errorEqual := Option.some.inj (invalid₁.symm.trans invalid₂)
          subst errorEqual
          rfl

end Program
end Newspeak
