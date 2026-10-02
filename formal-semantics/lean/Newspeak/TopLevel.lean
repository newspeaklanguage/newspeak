import Newspeak.CompoundLiterals

namespace Newspeak
namespace Program

/-- The least predicate of Equation (13.8).  There are deliberately no clauses
    for patterns or for implicit, self, outer, or super sends. -/
inductive TopLevelExpression (p : Program) : CoreExpr → Prop where
  | atom (payload : AtomPayload) :
      p.TopLevelExpression (.atom payload)
  | closure (declaration : ActivationDeclId) :
      p.TopLevelExpression (.closureLiteral declaration)
  | tuple {site : SiteId} {descriptor : CascadeDescriptor}
      {elements : List CoreExpr} :
      (∀ expression, expression ∈ elements →
        p.TopLevelExpression expression) →
      p.TopLevelExpression (.tuple site descriptor elements)
  | objectLiteral {declaration : ObjectLiteralDeclId}
      {superclass : CoreExpr} :
      p.objectLiteralOwner declaration = .topOwner →
      p.TopLevelExpression (.objectLiteral declaration superclass)
  | classBody {declaration : ClassDeclId} {superclass : CoreExpr} :
      p.classOwner declaration = .topOwner →
      p.TopLevelExpression (.classBody declaration superclass)
  | mixinApply {declaration : ClassDeclId}
      {superclass mixinSource : CoreExpr} :
      p.classOwner declaration = .topOwner →
      p.TopLevelExpression (.mixinApply declaration superclass mixinSource)
  | ordinarySend {receiver : CoreExpr} {selector : Selector}
      {arguments : List CoreExpr} :
      p.TopLevelExpression receiver →
      (∀ expression, expression ∈ arguments →
        p.TopLevelExpression expression) →
      p.TopLevelExpression (.ordinarySend receiver selector arguments)

/-- Equation (13.9): top-level code has a distinguished activation with no
    parameters, locals, runtime current class, continuation, home method, or
    lexical bindings.  Its current receiver is the language's nil object. -/
def topLevelActivationDefinition (p : Program) : ActivationDef :=
  { objectClass := p.activationClass
    provenance := .top
    parameters := FiniteStore.empty ParameterId ObjRef
    locals := FiniteStore.empty LocalSlotId LocalCell
    currentReceiver := p.nilObject
    currentClass := none
    continuation := none
    homeMethod := none
    continuable := true
    activationScopes := FiniteStore.empty ActivationDeclId ActivationId
    objectLiteralScopes := FiniteStore.empty ObjectLiteralDeclId ObjRef }

def allocateTopLevelActivation (p : Program) (state : AllocationState) :
    AllocationState × ActivationId :=
  let id : ActivationId := ⟨state.nextActivation⟩
  ({ state with
      heap := state.heap.installActivation id p.topLevelActivationDefinition
      nextActivation := state.nextActivation + 1 }, id)

@[simp] theorem allocateTopLevelActivation_reference (p : Program)
    (state : AllocationState) :
    (p.allocateTopLevelActivation state).2 = ⟨state.nextActivation⟩ := by
  rfl

@[simp] theorem allocateTopLevelActivation_installs (p : Program)
    (state : AllocationState) :
    let allocation := p.allocateTopLevelActivation state
    allocation.1.heap.activations allocation.2 =
      some p.topLevelActivationDefinition := by
  simp [allocateTopLevelActivation]

theorem allocateTopLevelActivation_was_fresh (_p : Program)
    {state : AllocationState} (fresh : state.ActivationSupplyFresh) :
    state.heap.activations ⟨state.nextActivation⟩ = none :=
  fresh ⟨state.nextActivation⟩ (Nat.le_refl _)

theorem allocateTopLevelActivation_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh) :
    (p.allocateTopLevelActivation state).1.SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id bound
    exact fresh.1 id (by simpa [allocateTopLevelActivation] using bound)
  · intro id bound
    have later : state.nextActivation + 1 ≤ id.index := by
      simpa [allocateTopLevelActivation] using bound
    have away : id ≠ (⟨state.nextActivation⟩ : ActivationId) := by
      intro equal
      have indexEqual := congrArg ActivationId.index equal
      simp at indexEqual
      omega
    rw [show (p.allocateTopLevelActivation state).1.heap =
      state.heap.installActivation ⟨state.nextActivation⟩
        p.topLevelActivationDefinition by rfl]
    rw [Heap.installActivation_away _ _ away]
    exact fresh.2.1 id (by omega)
  · intro id bound
    exact fresh.2.2.1 id (by
      simpa [allocateTopLevelActivation] using bound)
  · intro id bound
    exact fresh.2.2.2.1 id (by
      simpa [allocateTopLevelActivation] using bound)
  · intro id bound
    exact fresh.2.2.2.2 id (by
      simpa [allocateTopLevelActivation] using bound)

theorem allocateTopLevelActivation_wellFormed (p : Program)
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) :
    p.WellFormed (p.allocateTopLevelActivation state).1.heap ∧
      (p.allocateTopLevelActivation state).1.SuppliesFresh := by
  constructor
  · apply wf.installActivation_wellFormed
    · simpa [topLevelActivationDefinition] using wf.activationClassIsLive
    · simp [topLevelActivationDefinition, OptionalClassLive]
  · exact p.allocateTopLevelActivation_preserves_supplies fresh

/-- Equation (13.10), represented as a relation so the static top-level
    judgment remains explicit evidence rather than a Boolean side condition. -/
inductive TopLevelEntry (p : Program) :
    AllocationState → CoreExpr → SequentialConfig → Prop where
  | run {state : AllocationState} {expression : CoreExpr}
      (topLevel : p.TopLevelExpression expression) :
      TopLevelEntry p state expression
        ⟨(p.allocateTopLevelActivation state).1,
          .push .empty
            ⟨(p.allocateTopLevelActivation state).2, .empty⟩,
          .evaluate expression⟩

theorem topLevelEntry_deterministic {p : Program}
    {state : AllocationState} {expression : CoreExpr}
    {first second : SequentialConfig}
    (left : p.TopLevelEntry state expression first)
    (right : p.TopLevelEntry state expression second) : first = second := by
  cases left
  cases right
  rfl

theorem topLevelEntry_wellFormed {p : Program}
    {state : AllocationState} {expression : CoreExpr} {initial : SequentialConfig}
    (wf : p.WellFormed state.heap) (fresh : state.SuppliesFresh)
    (entry : p.TopLevelEntry state expression initial) :
    SequentialWellFormed p initial := by
  cases entry with
  | run topLevel =>
      have allocationWellFormed := p.allocateTopLevelActivation_wellFormed
        wf fresh
      exact ⟨allocationWellFormed.1, allocationWellFormed.2,
        ⟨trivial, p.topLevelActivationDefinition,
          p.allocateTopLevelActivation_installs state⟩, trivial⟩

def stopTopLevelActivation (state : AllocationState) (id : ActivationId)
    (activation : ActivationDef) : AllocationState :=
  { state with
    heap := state.heap.installActivation id
      (markActivationUncontinuable activation) }

theorem stopTopLevelActivation_preserves_supplies
    {state : AllocationState} (fresh : state.SuppliesFresh)
    {id : ActivationId} {activation : ActivationDef}
    (live : state.heap.activations id = some activation) :
    (stopTopLevelActivation state id activation).SuppliesFresh := by
  have idBelow : id.index < state.nextActivation := by
    by_cases below : id.index < state.nextActivation
    · exact below
    · have absent := fresh.2.1 id (Nat.le_of_not_gt below)
      rw [live] at absent
      contradiction
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fresh.1
  · intro candidate bound
    have originalBound : state.nextActivation ≤ candidate.index := by
      simpa [stopTopLevelActivation] using bound
    have away : candidate ≠ id := by
      intro equal
      subst candidate
      omega
    simpa [stopTopLevelActivation, Heap.installActivation, away] using
      fresh.2.1 candidate originalBound
  · exact fresh.2.2.1
  · exact fresh.2.2.2.1
  · exact fresh.2.2.2.2

theorem stopTopLevelActivation_wellFormed {p : Program}
    {state : AllocationState} (wf : p.WellFormed state.heap)
    {id : ActivationId} {activation : ActivationDef}
    (live : state.heap.activations id = some activation) :
    p.WellFormed (stopTopLevelActivation state id activation).heap := by
  have objectClassLive : p.IsLiveClass state.heap activation.objectClass :=
    wf.objectClassesAreLive (.activationObject id) activation.objectClass (by
      simp [Heap.classOf, live])
  have currentClassLive :=
    wf.activationCurrentClassesAreLive id activation live
  change p.WellFormed (state.heap.installActivation id
    (markActivationUncontinuable activation))
  apply wf.installActivation_wellFormed
  · simpa [markActivationUncontinuable] using objectClassLive
  · simpa [markActivationUncontinuable] using currentClassLive

/-- Rule Top-Halt.  The distinguished activation is made uncontinuable and
    removed from the materialized stack; no class or activation sentinel is
    used for either absent context field. -/
inductive TopLevelHaltStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | halt {state : AllocationState} {current : ActivationId}
      {activation : ActivationDef} {value : ObjRef}
      (live : state.heap.activations current = some activation)
      (top : activation.provenance = .top) :
      TopLevelHaltStep p
        ⟨state, .push .empty ⟨current, .empty⟩, .object value⟩
        ⟨stopTopLevelActivation state current activation, .empty, .halt value⟩

theorem topLevelHaltStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (left : p.TopLevelHaltStep before after₁)
    (right : p.TopLevelHaltStep before after₂) : after₁ = after₂ := by
  cases left with
  | halt live₁ top₁ =>
      cases right with
      | halt live₂ top₂ =>
          have activationEqual := Option.some.inj (live₁.symm.trans live₂)
          subst activationEqual
          rfl

theorem topLevelHaltStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.TopLevelHaltStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | halt live top =>
      exact ⟨stopTopLevelActivation_wellFormed wf.heap live,
        stopTopLevelActivation_preserves_supplies wf.supplies live,
        trivial, trivial⟩

theorem sequentialStep_topLevelHalt_disjoint {p : Program}
    {before sequentialAfter haltAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases halt
  cases sequential with
  | expression expression => cases expression
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

theorem instanceInitializationStep_topLevelHalt_disjoint {p : Program}
    {before initializationAfter haltAfter : SequentialConfig}
    (initialization : p.InstanceInitializationStep before initializationAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases halt with
  | @halt state current activation value live top =>
      cases initialization with
      | factory factory => cases factory
      | coordinator coordinator =>
          cases coordinator with
          | graph next =>
              cases value <;> simp [initializationCoordinatorNext] at next
      | slots slots =>
          cases slots with
          | graph next => simp [slotInitializationNext] at next

theorem objectAndNestedClassStep_topLevelHalt_disjoint {p : Program}
    {before objectAfter haltAfter : SequentialConfig}
    (objects : p.ObjectAndNestedClassStep before objectAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases halt
  cases objects with
  | objectLiteral objectLiteral => cases objectLiteral
  | nestedClass nestedClass => cases nestedClass

theorem sequentialStepWithObjects_topLevelHalt_disjoint {p : Program}
    {before sequentialAfter haltAfter : SequentialConfig}
    (sequential : p.SequentialStepWithObjects before sequentialAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases sequential with
  | prior prior =>
      cases prior with
      | prior sequential =>
          exact sequentialStep_topLevelHalt_disjoint sequential halt
      | initialization initialization =>
          exact instanceInitializationStep_topLevelHalt_disjoint
            initialization halt
  | objects objects =>
      exact objectAndNestedClassStep_topLevelHalt_disjoint objects halt

theorem exceptionBoundaryStep_topLevelHalt_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before boundaryAfter haltAfter : SequentialConfig}
    (boundary : p.ExceptionBoundaryStep reifier before boundaryAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases halt
  cases boundary

theorem sequentialStepWithExceptions_topLevelHalt_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before sequentialAfter haltAfter : SequentialConfig}
    (sequential : p.SequentialStepWithExceptions reifier before sequentialAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases sequential with
  | prior prior =>
      exact sequentialStepWithObjects_topLevelHalt_disjoint prior halt
  | exception exception =>
      exact exceptionBoundaryStep_topLevelHalt_disjoint exception halt

theorem compoundLiteralStep_topLevelHalt_disjoint {p : Program}
    {before literalAfter haltAfter : SequentialConfig}
    (literal : p.CompoundLiteralStep before literalAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases halt
  cases literal

theorem sequentialStepWithLiterals_topLevelHalt_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before sequentialAfter haltAfter : SequentialConfig}
    (sequential : p.SequentialStepWithLiterals reifier before sequentialAfter)
    (halt : p.TopLevelHaltStep before haltAfter) : False := by
  cases sequential with
  | prior prior =>
      exact sequentialStepWithExceptions_topLevelHalt_disjoint prior halt
  | compoundLiteral literal =>
      exact compoundLiteralStep_topLevelHalt_disjoint literal halt

/-- Sequential execution through exact top-level termination. -/
inductive SequentialStepWithTopLevel (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      p.SequentialStepWithLiterals reifier before after →
        p.SequentialStepWithTopLevel reifier before after
  | topHalt {before after : SequentialConfig} :
      p.TopLevelHaltStep before after →
        p.SequentialStepWithTopLevel reifier before after

theorem sequentialStepWithTopLevel_deterministic {p : Program}
    {reifier : ErrorReifier p} {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (left : p.SequentialStepWithTopLevel reifier before after₁)
    (right : p.SequentialStepWithTopLevel reifier before after₂) :
    after₁ = after₂ := by
  cases left with
  | prior prior₁ =>
      cases right with
      | prior prior₂ =>
          exact sequentialStepWithLiterals_deterministic wf prior₁ prior₂
      | topHalt halt₂ =>
          exact (sequentialStepWithLiterals_topLevelHalt_disjoint
            prior₁ halt₂).elim
  | topHalt halt₁ =>
      cases right with
      | prior prior₂ =>
          exact (sequentialStepWithLiterals_topLevelHalt_disjoint
            prior₂ halt₁).elim
      | topHalt halt₂ =>
          exact topLevelHaltStep_deterministic halt₁ halt₂

theorem sequentialStepWithTopLevel_preserves_wellFormed {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (wf : SequentialWellFormed p before)
    (step : p.SequentialStepWithTopLevel reifier before after) :
    SequentialWellFormed p after := by
  cases step with
  | prior prior =>
      exact sequentialStepWithLiterals_preserves_wellFormed wf prior
  | topHalt halt => exact topLevelHaltStep_preserves_wellFormed wf halt

end Program
end Newspeak
