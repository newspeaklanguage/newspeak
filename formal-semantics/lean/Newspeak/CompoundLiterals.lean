import Newspeak.ExceptionBoundary

namespace Newspeak

def tupleNewSelector : Selector := ⟨"new:"⟩
def tupleFromArraySelector : Selector := ⟨"fromArray:"⟩
def tupleAtPutSelector : Selector := ⟨"at:put:"⟩
def tupleYourselfSelector : Selector := ⟨"yourself"⟩
def patternBindingSelector : Selector := ⟨"Pattern"⟩
def patternWildcardSelector : Selector := ⟨"wildcard"⟩
def patternLiteralSelector : Selector := ⟨"literal:"⟩
def patternKeywordsSelector : Selector := ⟨"keywords:patterns:"⟩

def naturalAtom (value : Nat) : CoreExpr :=
  .atom (.integer value)

def tuplePutClauses : Nat → List CoreExpr →
    List (Selector × List CoreExpr)
  | _, [] => [(tupleYourselfSelector, [])]
  | index, expression :: remaining =>
      (tupleAtPutSelector, [naturalAtom index, expression]) ::
        tuplePutClauses (index + 1) remaining

namespace Program

/-- Equations (12.2)--(12.3).  A nonempty tuple deliberately retains the
    cascade node so its receiver is subsequently expanded through the exact
    one-argument closure translation. -/
def tupleExpansion (p : Program) (_site : SiteId)
    (descriptor : CascadeDescriptor)
    (elements : List CoreExpr) : Option CoreExpr := do
  let readOnlyTuple ← p.platform .readOnlyTuple
  match elements with
  | [] =>
      pure (.ordinarySend (.value readOnlyTuple) tupleNewSelector
        [naturalAtom 0])
  | _ :: _ =>
      let array ← p.platform .array
      let arrayCreation :=
        CoreExpr.ordinarySend (.value array) tupleNewSelector
          [naturalAtom elements.length]
      let cascade :=
        CoreExpr.cascade descriptor arrayCreation (tuplePutClauses 1 elements)
      pure (.ordinarySend (.value readOnlyTuple) tupleFromArraySelector
        [cascade])

/-- Equation (4.39), specialized only by taking already-elaborated clauses.
    The clause list is carried into `cascadeClosure`, so an in-flight term
    retains its materialized code across reflective program installation. -/
def cascadeExpansion (descriptor : CascadeDescriptor)
    (receiver : CoreExpr) (clauses : List (Selector × List CoreExpr)) : CoreExpr :=
  .ordinarySend (.cascadeClosure descriptor clauses)
    (valueSelector 1) [receiver]

mutual
  def patternExpansion (p : Program) (annotation : Option ScopeDecl)
      (immediate : Option ClassDeclId) : CorePattern → Option CoreExpr
    | .wildcard =>
        some (.ordinarySend
          (.implicitSend patternBindingSelector [] annotation immediate)
          patternWildcardSelector [])
    | .literal expression =>
        some (.ordinarySend
          (.implicitSend patternBindingSelector [] annotation immediate)
          patternLiteralSelector [expression])
    | .variable site => p.patternVariable site
    | .nested value => some (.pattern value annotation immediate)
    | .keyword keywordTupleSite keywordTupleCascade componentTupleSite
        componentTupleCascade pairs => do
        let components ← patternComponentExpansions p annotation immediate pairs
        let keywords := pairs.map fun pair =>
          CoreExpr.atom (.symbol pair.1.spelling)
        pure (.ordinarySend
          (.implicitSend patternBindingSelector [] annotation immediate)
          patternKeywordsSelector
          [.tuple keywordTupleSite keywordTupleCascade keywords,
           .tuple componentTupleSite componentTupleCascade components])

  def patternComponentExpansions (p : Program)
      (annotation : Option ScopeDecl) (immediate : Option ClassDeclId) :
      List (Selector × CorePattern) → Option (List CoreExpr)
    | [] => some []
    | pair :: remaining => do
        let first ← patternExpansion p annotation immediate pair.2
        let rest ← patternComponentExpansions p annotation immediate remaining
        pure (first :: rest)
end

/-- Exact dynamic expansion rules for tuples, cascades, and patterns. -/
inductive CompoundLiteralStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | tuple {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {site : SiteId}
      {descriptor : CascadeDescriptor}
      {elements : List CoreExpr} {expansion : CoreExpr}
      (expanded : p.tupleExpansion site descriptor elements = some expansion) :
      CompoundLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.tuple site descriptor elements)⟩
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expansion⟩
  | cascade {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {receiver : CoreExpr} {clauses : List (Selector × List CoreExpr)}
      {descriptor : CascadeDescriptor} :
      CompoundLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.cascade descriptor receiver clauses)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (cascadeExpansion descriptor receiver clauses)⟩
  | pattern {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {value : CorePattern}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {expansion : CoreExpr}
      (expanded : p.patternExpansion annotation immediate value = some expansion) :
      CompoundLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.pattern value annotation immediate)⟩
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expansion⟩

theorem compoundLiteralStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (left : p.CompoundLiteralStep before after₁)
    (right : p.CompoundLiteralStep before after₂) : after₁ = after₂ := by
  cases left with
  | tuple expanded₁ =>
      cases right with
      | tuple expanded₂ =>
          have equal := Option.some.inj (expanded₁.symm.trans expanded₂)
          subst equal
          rfl
  | cascade =>
      cases right with
      | cascade => rfl
  | pattern expanded₁ =>
      cases right with
      | pattern expanded₂ =>
          have equal := Option.some.inj (expanded₁.symm.trans expanded₂)
          subst equal
          rfl

theorem compoundLiteralStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.CompoundLiteralStep before after) :
    SequentialWellFormed p after := by
  cases step <;> exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩

theorem sequentialStep_compoundLiteral_disjoint {p : Program}
    {before sequentialAfter literalAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (literal : p.CompoundLiteralStep before literalAfter) : False := by
  cases literal <;> cases sequential with
  | expression expression => cases expression with
    | nonOrdinary data => simp [nonOrdinaryRequest] at data
  | request request => cases request
  | invocation invocation => cases invocation
  | body body => cases body with
    | graph next => simp [bodyMachineNext] at next
  | returns returns => cases returns with
    | graph next => simp [returnMachineNext] at next
  | closure closure => cases closure with
    | creation creation => cases creation
    | dispatch dispatch => cases dispatch
    | invocation invocation => cases invocation
  | objectSlots slots => cases slots
  | classes classes => cases classes
  | messages messages => cases messages

theorem instanceInitializationStep_compoundLiteral_disjoint {p : Program}
    {before initializationAfter literalAfter : SequentialConfig}
    (initialization : p.InstanceInitializationStep before initializationAfter)
    (literal : p.CompoundLiteralStep before literalAfter) : False := by
  cases literal <;> cases initialization with
  | factory factory => cases factory
  | coordinator coordinator => cases coordinator with
    | graph next => simp [initializationCoordinatorNext] at next
  | slots slots => cases slots with
    | graph next => simp [slotInitializationNext] at next

theorem objectAndNestedClassStep_compoundLiteral_disjoint {p : Program}
    {before objectAfter literalAfter : SequentialConfig}
    (objects : p.ObjectAndNestedClassStep before objectAfter)
    (literal : p.CompoundLiteralStep before literalAfter) : False := by
  cases literal <;> cases objects with
  | objectLiteral objectLiteral => cases objectLiteral
  | nestedClass nestedClass => cases nestedClass

theorem sequentialStepWithExceptions_compoundLiteral_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before sequentialAfter literalAfter : SequentialConfig}
    (sequential : p.SequentialStepWithExceptions reifier before sequentialAfter)
    (literal : p.CompoundLiteralStep before literalAfter) : False := by
  cases sequential with
  | prior objects =>
      cases objects with
      | prior initialization =>
          cases initialization with
          | prior base => exact sequentialStep_compoundLiteral_disjoint base literal
          | initialization step =>
              exact instanceInitializationStep_compoundLiteral_disjoint step literal
      | objects step =>
          exact objectAndNestedClassStep_compoundLiteral_disjoint step literal
  | exception exception => cases literal <;> cases exception

/-- Sequential execution including exact compound-literal expansion. -/
inductive SequentialStepWithLiterals (p : Program) (reifier : ErrorReifier p) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      p.SequentialStepWithExceptions reifier before after →
        p.SequentialStepWithLiterals reifier before after
  | compoundLiteral {before after : SequentialConfig} :
      p.CompoundLiteralStep before after →
        p.SequentialStepWithLiterals reifier before after

theorem sequentialStepWithLiterals_deterministic {p : Program}
    {reifier : ErrorReifier p} {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (left : p.SequentialStepWithLiterals reifier before after₁)
    (right : p.SequentialStepWithLiterals reifier before after₂) :
    after₁ = after₂ := by
  cases left with
  | prior prior₁ =>
      cases right with
      | prior prior₂ =>
          exact sequentialStepWithExceptions_deterministic wf prior₁ prior₂
      | compoundLiteral literal₂ =>
          exact (sequentialStepWithExceptions_compoundLiteral_disjoint
            prior₁ literal₂).elim
  | compoundLiteral literal₁ =>
      cases right with
      | prior prior₂ =>
          exact (sequentialStepWithExceptions_compoundLiteral_disjoint
            prior₂ literal₁).elim
      | compoundLiteral literal₂ =>
          exact compoundLiteralStep_deterministic literal₁ literal₂

theorem sequentialStepWithLiterals_preserves_wellFormed {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (wf : SequentialWellFormed p before)
    (step : p.SequentialStepWithLiterals reifier before after) :
    SequentialWellFormed p after := by
  cases step with
  | prior prior =>
      exact sequentialStepWithExceptions_preserves_wellFormed wf prior
  | compoundLiteral literal =>
      exact compoundLiteralStep_preserves_wellFormed wf literal

end Program
end Newspeak
