import Newspeak.StaticElaboration
import Newspeak.PrologPEGCorrespondence

/-!
# Graph correspondence for the recursive static elaborator

The Prolog source expands these graphs into one Horn clause per successful
surface constructor.  This module fixes the semantic target of every graph:
the existing executable, fuel-bounded Lean elaboration functions.  The graph
relations deliberately expose failure by absence of a constructor.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologElaborationContextBind (context : ElaborationContext)
    (name : String) : Option ScopeDecl → Prop where
  | witness {result : Option ScopeDecl} : context.bind name = result →
      PrologElaborationContextBind context name result

theorem prologElaborationContextBind_iff {context name result} :
    PrologElaborationContextBind context name result ↔
      context.bind name = result := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologSelectorBindingAnnotation (services : ElaborationServices)
    (context : ElaborationContext) (selector : Selector) :
    Option ScopeDecl → Prop where
  | witness {result : Option ScopeDecl} :
      selectorBindingAnnotation services context selector = result →
      PrologSelectorBindingAnnotation services context selector result

theorem prologSelectorBindingAnnotation_iff {services context selector result} :
    PrologSelectorBindingAnnotation services context selector result ↔
      selectorBindingAnnotation services context selector = result := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologSurfaceReceiverKind (context : ElaborationContext)
    (receiver : SurfaceExpression) : Option SurfaceReceiverKind → Prop where
  | witness {result : Option SurfaceReceiverKind} :
      surfaceReceiverKind context receiver = result →
      PrologSurfaceReceiverKind context receiver result

theorem prologSurfaceReceiverKind_iff {context receiver result} :
    PrologSurfaceReceiverKind context receiver result ↔
      surfaceReceiverKind context receiver = result := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologElaborateExpressionWithFuel (services : ElaborationServices)
    (context : ElaborationContext) (fuel : Nat) (surface : SurfaceExpression) :
    CoreExpr → Prop where
  | result {core : CoreExpr} :
      elaborateExpressionWithFuel services context fuel surface = some core →
      PrologElaborateExpressionWithFuel services context fuel surface core

theorem prologElaborateExpressionWithFuel_iff
    {services context fuel surface core} :
    PrologElaborateExpressionWithFuel services context fuel surface core ↔
      elaborateExpressionWithFuel services context fuel surface = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateExpressionListWithFuel
    (services : ElaborationServices) (context : ElaborationContext)
    (fuel : Nat) (surface : List SurfaceExpression) : List CoreExpr → Prop where
  | result {core : List CoreExpr} :
      elaborateExpressionListWithFuel services context fuel surface = some core →
      PrologElaborateExpressionListWithFuel services context fuel surface core

theorem prologElaborateExpressionListWithFuel_iff
    {services context fuel surface core} :
    PrologElaborateExpressionListWithFuel services context fuel surface core ↔
      elaborateExpressionListWithFuel services context fuel surface = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologMakeElaboratedSendWithFuel (services : ElaborationServices)
    (context : ElaborationContext) (fuel : Nat) (receiver : SurfaceExpression)
    (selector : Selector) (arguments : List CoreExpr) : CoreExpr → Prop where
  | result {core : CoreExpr} :
      makeElaboratedSendWithFuel services context fuel receiver selector arguments =
        some core →
      PrologMakeElaboratedSendWithFuel services context fuel receiver selector
        arguments core

theorem prologMakeElaboratedSendWithFuel_iff
    {services context fuel receiver selector arguments core} :
    PrologMakeElaboratedSendWithFuel services context fuel receiver selector
      arguments core ↔
      makeElaboratedSendWithFuel services context fuel receiver selector arguments =
        some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateClauseListWithFuel (services : ElaborationServices)
    (context : ElaborationContext) (fuel : Nat) (surface : List SurfaceClause) :
    List (Selector × List CoreExpr) → Prop where
  | result {core : List (Selector × List CoreExpr)} :
      elaborateClauseListWithFuel services context fuel surface = some core →
      PrologElaborateClauseListWithFuel services context fuel surface core

theorem prologElaborateClauseListWithFuel_iff
    {services context fuel surface core} :
    PrologElaborateClauseListWithFuel services context fuel surface core ↔
      elaborateClauseListWithFuel services context fuel surface = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaboratePatternWithFuel (services : ElaborationServices)
    (context : ElaborationContext) (fuel : Nat) (surface : SurfacePattern) :
    CorePattern → Prop where
  | result {core : CorePattern} :
      elaboratePatternWithFuel services context fuel surface = some core →
      PrologElaboratePatternWithFuel services context fuel surface core

theorem prologElaboratePatternWithFuel_iff
    {services context fuel surface core} :
    PrologElaboratePatternWithFuel services context fuel surface core ↔
      elaboratePatternWithFuel services context fuel surface = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaboratePatternPairsWithFuel (services : ElaborationServices)
    (context : ElaborationContext) (fuel : Nat)
    (surface : List (Selector × Option SurfacePattern)) :
    List (Selector × CorePattern) → Prop where
  | result {core : List (Selector × CorePattern)} :
      elaboratePatternPairsWithFuel services context fuel surface = some core →
      PrologElaboratePatternPairsWithFuel services context fuel surface core

theorem prologElaboratePatternPairsWithFuel_iff
    {services context fuel surface core} :
    PrologElaboratePatternPairsWithFuel services context fuel surface core ↔
      elaboratePatternPairsWithFuel services context fuel surface = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateObjectSuperclassWithFuel
    (services : ElaborationServices) (context : ElaborationContext)
    (fuel : Nat) (header : SurfaceObjectHeader) : CoreExpr → Prop where
  | result {core : CoreExpr} :
      elaborateObjectSuperclassWithFuel services context fuel header = some core →
      PrologElaborateObjectSuperclassWithFuel services context fuel header core

theorem prologElaborateObjectSuperclassWithFuel_iff
    {services context fuel header core} :
    PrologElaborateObjectSuperclassWithFuel services context fuel header core ↔
      elaborateObjectSuperclassWithFuel services context fuel header =
        some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateClassSuperclassWithFuel
    (services : ElaborationServices) (context : ElaborationContext)
    (fuel : Nat) (declaration : SurfaceDeclaration) : CoreExpr → Prop where
  | result {core : CoreExpr} :
      elaborateClassSuperclassWithFuel services context fuel declaration =
        some core →
      PrologElaborateClassSuperclassWithFuel services context fuel declaration
        core

theorem prologElaborateClassSuperclassWithFuel_iff
    {services context fuel declaration core} :
    PrologElaborateClassSuperclassWithFuel services context fuel declaration
      core ↔
      elaborateClassSuperclassWithFuel services context fuel declaration =
        some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateExpression (services : ElaborationServices)
    (context : ElaborationContext) (surface : SurfaceExpression) :
    CoreExpr → Prop where
  | result {core : CoreExpr} :
      elaborateExpression services context surface = some core →
      PrologElaborateExpression services context surface core

theorem prologElaborateExpression_iff {services context surface core} :
    PrologElaborateExpression services context surface core ↔
      elaborateExpression services context surface = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

theorem PrologElaborateExpression.deterministic
    {services context surface first second}
    (firstRun : PrologElaborateExpression services context surface first)
    (secondRun : PrologElaborateExpression services context surface second) :
    first = second :=
  elaborateExpression_deterministic
    (prologElaborateExpression_iff.mp firstRun)
    (prologElaborateExpression_iff.mp secondRun)

end PrologBridge
end Newspeak
