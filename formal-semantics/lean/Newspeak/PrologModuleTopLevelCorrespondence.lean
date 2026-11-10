import Newspeak.Modules
import Newspeak.TopLevel
import Newspeak.PrologLookupCorrespondence

/-!
# Correspondence for modules and top-level entry

This file mirrors the Horn clauses for Equations `module-definition`,
`module-instance`, `top-level-expression`, `run-program`, and
`application-object`.  The list relation is explicit because the Prolog
source spells out recursive traversal rather than hiding it in a host-language
universal quantifier.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologModuleDefinition (p : Program) (heap : Heap) : ClassId → Prop where
  | definition {classId : ClassId} {definition : ClassDef}
      {declaration : ClassDeclId} {factory : FactoryDef} :
      heap.classes classId = some definition →
      definition.primaryFactory = some factory →
      definition.origin = .expression (.namedClass declaration) →
      p.classOwner declaration = .topOwner →
      PrologModuleDefinition p heap classId

theorem prologModuleDefinition_iff {p : Program} {heap : Heap}
    {classId : ClassId} :
    PrologModuleDefinition p heap classId ↔
      p.ModuleDefinition heap classId := by
  constructor
  · intro derivation
    cases derivation with
    | definition present factory origin owner =>
        exact ⟨_, _, _, present, factory, origin, owner⟩
  · rintro ⟨definition, declaration, factory, present, hasFactory, origin, owner⟩
    exact .definition present hasFactory origin owner

inductive PrologModuleInstance (p : Program) (heap : Heap) : ObjRef → Prop where
  | object {object : ObjRef} {classId : ClassId} :
      heap.classOf object = some classId →
      PrologModuleDefinition p heap classId →
      PrologModuleInstance p heap object

theorem prologModuleInstance_iff {p : Program} {heap : Heap}
    {object : ObjRef} :
    PrologModuleInstance p heap object ↔ p.ModuleInstance heap object := by
  constructor
  · intro derivation
    cases derivation with
    | object classOf moduleDefinition =>
        exact ⟨_, classOf, prologModuleDefinition_iff.mp moduleDefinition⟩
  · rintro ⟨classId, classOf, moduleDefinition⟩
    exact .object classOf (prologModuleDefinition_iff.mpr moduleDefinition)

inductive PrologTopLevelExpression (p : Program) : CoreExpr → Prop where
    | atom (payload : AtomPayload) :
        PrologTopLevelExpression p (.atom payload)
    | closure (declaration : ActivationDeclId) :
        PrologTopLevelExpression p (.closureLiteral declaration)
    | tuple {site : SiteId} {descriptor : CascadeDescriptor}
        {elements : List CoreExpr} :
        (∀ expression, expression ∈ elements →
          PrologTopLevelExpression p expression) →
        PrologTopLevelExpression p (.tuple site descriptor elements)
    | objectLiteral {declaration : ObjectLiteralDeclId}
        {superclass : CoreExpr} :
        p.objectLiteralOwner declaration = .topOwner →
        PrologTopLevelExpression p (.objectLiteral declaration superclass)
    | classBody {declaration : ClassDeclId} {superclass : CoreExpr} :
        p.classOwner declaration = .topOwner →
        PrologTopLevelExpression p (.classBody declaration superclass)
    | mixinApply {declaration : ClassDeclId}
        {superclass mixinSource : CoreExpr} :
        p.classOwner declaration = .topOwner →
        PrologTopLevelExpression p
          (.mixinApply declaration superclass mixinSource)
    | ordinarySend {receiver : CoreExpr} {selector : Selector}
        {arguments : List CoreExpr} :
        PrologTopLevelExpression p receiver →
        (∀ expression, expression ∈ arguments →
          PrologTopLevelExpression p expression) →
        PrologTopLevelExpression p (.ordinarySend receiver selector arguments)

def PrologTopLevelExpressionList (p : Program)
    (expressions : List CoreExpr) : Prop :=
  ∀ expression, expression ∈ expressions →
    PrologTopLevelExpression p expression

theorem prologTopLevelExpression_sound {p : Program} {expression : CoreExpr}
      (derivation : PrologTopLevelExpression p expression) :
      p.TopLevelExpression expression := by
    induction derivation with
    | atom payload => exact .atom payload
    | closure declaration => exact .closure declaration
    | tuple elements ih => exact .tuple ih
    | objectLiteral owner => exact .objectLiteral owner
    | classBody owner => exact .classBody owner
    | mixinApply owner => exact .mixinApply owner
    | ordinarySend receiver arguments receiverSound argumentsSound =>
        exact .ordinarySend receiverSound argumentsSound

theorem prologTopLevelExpressionList_sound {p : Program}
      {expressions : List CoreExpr}
      (derivation : PrologTopLevelExpressionList p expressions) :
      ∀ expression, expression ∈ expressions →
        p.TopLevelExpression expression := by
  intro expression member
  exact prologTopLevelExpression_sound (derivation expression member)

theorem prologTopLevelExpressionList_of_all {p : Program}
    {expressions : List CoreExpr}
    (all : ∀ expression, expression ∈ expressions →
      PrologTopLevelExpression p expression) :
    PrologTopLevelExpressionList p expressions := all

theorem prologTopLevelExpression_complete {p : Program}
    {expression : CoreExpr} (derivation : p.TopLevelExpression expression) :
    PrologTopLevelExpression p expression := by
  induction derivation with
  | atom payload => exact .atom payload
  | closure declaration => exact .closure declaration
  | tuple all ih => exact .tuple (prologTopLevelExpressionList_of_all ih)
  | objectLiteral owner => exact .objectLiteral owner
  | classBody owner => exact .classBody owner
  | mixinApply owner => exact .mixinApply owner
  | ordinarySend receiver all receiverComplete allComplete =>
      exact .ordinarySend receiverComplete
        (prologTopLevelExpressionList_of_all allComplete)

theorem prologTopLevelExpression_iff {p : Program} {expression : CoreExpr} :
    PrologTopLevelExpression p expression ↔
      p.TopLevelExpression expression :=
  ⟨prologTopLevelExpression_sound, prologTopLevelExpression_complete⟩

theorem prologTopLevelExpressionList_iff {p : Program}
    {expressions : List CoreExpr} :
    PrologTopLevelExpressionList p expressions ↔
      ∀ expression, expression ∈ expressions →
        p.TopLevelExpression expression := by
  constructor
  · exact prologTopLevelExpressionList_sound
  · intro all
    exact prologTopLevelExpressionList_of_all fun expression member =>
      prologTopLevelExpression_complete (all expression member)

inductive PrologTopLevelEntry (p : Program) :
    AllocationState → CoreExpr → SequentialConfig → Prop where
  | run {state : AllocationState} {expression : CoreExpr} :
      PrologTopLevelExpression p expression →
      PrologTopLevelEntry p state expression
        ⟨(p.allocateTopLevelActivation state).1,
          .push .empty
            ⟨(p.allocateTopLevelActivation state).2, .empty⟩,
          .evaluate expression⟩

theorem prologTopLevelEntry_iff {p : Program} {state : AllocationState}
    {expression : CoreExpr} {configuration : SequentialConfig} :
    PrologTopLevelEntry p state expression configuration ↔
      p.TopLevelEntry state expression configuration := by
  constructor
  · intro derivation
    cases derivation with
    | run topLevel => exact .run (prologTopLevelExpression_sound topLevel)
  · intro derivation
    cases derivation with
    | run topLevel => exact .run (prologTopLevelExpression_complete topLevel)

inductive PrologApplicationObject (p : Program) (heap : Heap) :
    ObjRef → Prop where
  | application {object : ObjRef} {classId : ClassId}
      {result : LookupResult} :
      heap.classOf object = some classId →
      PrologPublicLookup p heap Program.applicationMainSelector classId (some result) →
      result.method.parameters.length = 2 →
      PrologApplicationObject p heap object

theorem prologApplicationObject_iff {p : Program} {heap : Heap}
    {object : ObjRef} :
    PrologApplicationObject p heap object ↔
      p.ApplicationObject heap object := by
  constructor
  · intro derivation
    cases derivation with
    | application classOf lookup arity =>
        exact ⟨_, _, classOf, prologPublic_iff_rules.mp lookup, arity⟩
  · rintro ⟨classId, result, classOf, lookup, arity⟩
    exact .application classOf (prologPublic_iff_rules.mpr lookup) arity

end PrologBridge
end Newspeak
