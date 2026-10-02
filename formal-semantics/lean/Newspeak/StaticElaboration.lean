import Newspeak.NewspeakSurfaceActions

namespace Newspeak

inductive EnclosingActivationKind where
  | topLevel
  | method
  | closure
deriving Repr, DecidableEq, BEq

structure ElaborationContext where
  enclosingClassBody : Option ClassBodyDecl
  enclosingActivation : Option ActivationDeclId
  activationKind : EnclosingActivationKind
  immediateClass : Option ClassDeclId
  binders : List (FiniteStore String ScopeDecl)
  localReturnPermitted : Bool
  nonlocalReturnPermitted : Bool

/-- Typed identities selected by stable AST identification.  Synthetic
    tuple/pattern/cascade nodes are assigned once here and are then retained in
    the core, so later reflective source changes cannot silently renumber them. -/
structure ElaborationIdentities where
  expressionSite : SourceSpan → String → Option SiteId
  closureDeclaration : SourceSpan → Option ActivationDeclId
  classDeclaration : SourceSpan → Option ClassDeclId
  objectLiteralDeclaration : SourceSpan → Option ObjectLiteralDeclId
  cascadeDescriptor : SourceSpan → Option ClassDeclId → Option CascadeDescriptor
  tupleDescriptor : SourceSpan → Option ClassDeclId →
    Option (SiteId × CascadeDescriptor)
  variablePatternSite : SourceSpan → Option SiteId
  keywordPatternDescriptors : SourceSpan → Option ClassDeclId →
    Option (SiteId × CascadeDescriptor × SiteId × CascadeDescriptor)

structure ElaborationServices where
  identities : ElaborationIdentities
  isUnarySelector : Selector → Bool
  defaultSuperclass : ElaborationContext → CoreExpr
  fuel : Nat

def bindInScopes : List (FiniteStore String ScopeDecl) → String → Option ScopeDecl
  | [], _ => none
  | scope :: remaining, name =>
      match scope name with
      | some declaration => some declaration
      | none => bindInScopes remaining name

def ElaborationContext.bind (context : ElaborationContext) (name : String) :
    Option ScopeDecl :=
  bindInScopes context.binders name

def ElaborationContext.classBind (context : ElaborationContext)
    (name : String) : Option ClassDeclId :=
  match context.bind name with
  | some (.classDecl declaration) => some declaration
  | _ => none

def selectorBindingAnnotation (services : ElaborationServices)
    (context : ElaborationContext) (selector : Selector) : Option ScopeDecl :=
  if services.isUnarySelector selector then context.bind selector.spelling else none

inductive SurfaceReceiverKind where
  | selfReceiver (immediate : ClassDeclId)
  | outerReceiver (target immediate : ClassDeclId)
  | superReceiver
  | ordinaryReceiver
deriving Repr, DecidableEq

def surfaceReceiverKind (context : ElaborationContext) :
    SurfaceExpression → Option SurfaceReceiverKind
  | .parenthesized _ receiver => surfaceReceiverKind context receiver
  | .selfValue _ => context.immediateClass.map .selfReceiver
  | .outer _ name => do
      let target ← context.classBind name
      let immediate ← context.immediateClass
      pure (.outerReceiver target immediate)
  | .superValue _ =>
      if context.activationKind = .method then some .superReceiver else none
  | _ => some .ordinaryReceiver

mutual
  def elaborateExpressionWithFuel (services : ElaborationServices)
      (context : ElaborationContext) : Nat → SurfaceExpression → Option CoreExpr
    | 0, _ => none
    | fuel + 1, expression =>
      match expression with
      | .atom _ payload => some (.atom payload)
      | .identifier _ name =>
          some (.implicitSend ⟨name⟩ [] (context.bind name) context.immediateClass)
      | .selfValue _ => some .selfValue
      | .outer _ _ => none
      | .superValue _ => none
      | .parenthesized _ nested =>
          elaborateExpressionWithFuel services context fuel nested
      | .implicitSend _ selector arguments => do
          let coreArguments ← elaborateExpressionListWithFuel services context fuel arguments
          pure (.implicitSend selector coreArguments
            (selectorBindingAnnotation services context selector)
            context.immediateClass)
      | .messageSend _ receiver selector arguments => do
          let coreArguments ← elaborateExpressionListWithFuel services context fuel arguments
          makeElaboratedSendWithFuel services context fuel receiver selector coreArguments
      | .eventualSend _ receiver selector arguments => do
          let coreReceiver ← elaborateExpressionWithFuel services context fuel receiver
          let coreArguments ← elaborateExpressionListWithFuel services context fuel arguments
          pure (.eventualSend coreReceiver selector coreArguments)
      | .cascade span receiver initial subsequent => do
          let descriptor ← services.identities.cascadeDescriptor span
            context.immediateClass
          let coreReceiver ← elaborateExpressionWithFuel services context fuel receiver
          let initialClauses ← elaborateClauseListWithFuel services context fuel initial
          let subsequentClauses ← elaborateClauseListWithFuel services context fuel subsequent
          pure (.cascade descriptor coreReceiver (initialClauses ++ subsequentClauses))
      | .setter span _ expression => do
          let descriptor ← services.identities.cascadeDescriptor span
            context.immediateClass
          let argument ← elaborateExpressionWithFuel services context fuel expression
          pure (.ordinarySend (.closureLiteral descriptor.closureDeclaration)
            ⟨"value:"⟩ [argument])
      | .tuple span elements => do
          let descriptor ← services.identities.tupleDescriptor span
            context.immediateClass
          let coreElements ← elaborateExpressionListWithFuel services context fuel elements
          pure (.tuple descriptor.1 descriptor.2 coreElements)
      | .pattern _ pattern => do
          let corePattern ← elaboratePatternWithFuel services context fuel pattern
          pure (.pattern corePattern (context.bind "Pattern") context.immediateClass)
      | .closure span _parameters _locals _body => do
          let declaration ← services.identities.closureDeclaration span
          pure (.closureLiteral declaration)
      | .objectLiteral span header => do
          let declaration ← services.identities.objectLiteralDeclaration span
          let superclass ← elaborateObjectSuperclassWithFuel services context fuel header
          pure (.objectLiteral declaration superclass)
      | .classExpression span declaration => do
          let classIdentity ← services.identities.classDeclaration span
          let superclass ← elaborateClassSuperclassWithFuel services context fuel declaration
          pure (.classBody classIdentity superclass)
      | .sequence _ statements =>
          match statements with
          | [.expression _ nested] =>
              elaborateExpressionWithFuel services context fuel nested
          | _ => none

  def elaborateExpressionListWithFuel (services : ElaborationServices)
      (context : ElaborationContext) :
      Nat → List SurfaceExpression → Option (List CoreExpr)
    | 0, _ => none
    | _, [] => some []
    | fuel + 1, expression :: remaining => do
        let first ← elaborateExpressionWithFuel services context fuel expression
        let rest ← elaborateExpressionListWithFuel services context fuel remaining
        pure (first :: rest)

  def makeElaboratedSendWithFuel (services : ElaborationServices)
      (context : ElaborationContext) :
      Nat → SurfaceExpression → Selector → List CoreExpr → Option CoreExpr
    | 0, _, _, _ => none
    | fuel + 1, receiver, selector, arguments => do
      let kind ← surfaceReceiverKind context receiver
      match kind with
      | .selfReceiver immediate => pure (.selfSend selector arguments immediate)
      | .outerReceiver target immediate =>
          pure (.outerSend selector arguments target immediate)
      | .superReceiver => pure (.superSend selector arguments)
      | .ordinaryReceiver => do
          let coreReceiver ← elaborateExpressionWithFuel services context fuel receiver
          pure (.ordinarySend coreReceiver selector arguments)

  def elaborateClauseListWithFuel (services : ElaborationServices)
      (context : ElaborationContext) :
      Nat → List SurfaceClause → Option (List (Selector × List CoreExpr))
    | 0, _ => none
    | _, [] => some []
    | fuel + 1, .clause _ selector arguments :: remaining => do
        let coreArguments ← elaborateExpressionListWithFuel services context fuel arguments
        let coreRemaining ← elaborateClauseListWithFuel services context fuel remaining
        pure ((selector, coreArguments) :: coreRemaining)

  def elaboratePatternWithFuel (services : ElaborationServices)
      (context : ElaborationContext) : Nat → SurfacePattern → Option CorePattern
    | 0, _ => none
    | fuel + 1, pattern =>
      match pattern with
      | .wildcard _ => some .wildcard
      | .literal _ expression => do
          pure (.literal (← elaborateExpressionWithFuel services context fuel expression))
      | .variable span _ => do
          pure (.variable (← services.identities.variablePatternSite span))
      | .nested _ nested => do
          pure (.nested (← elaboratePatternWithFuel services context fuel nested))
      | .keyword span pairs => do
          let descriptors ← services.identities.keywordPatternDescriptors span
            context.immediateClass
          let corePairs ← elaboratePatternPairsWithFuel services context fuel pairs
          pure (.keyword descriptors.1 descriptors.2.1 descriptors.2.2.1
            descriptors.2.2.2 corePairs)

  def elaboratePatternPairsWithFuel (services : ElaborationServices)
      (context : ElaborationContext) : Nat →
      List (Selector × Option SurfacePattern) →
        Option (List (Selector × CorePattern))
    | 0, _ => none
    | _, [] => some []
    | fuel + 1, (selector, pattern) :: remaining => do
        let corePattern ←
          match pattern with
          | none => some .wildcard
          | some value => elaboratePatternWithFuel services context fuel value
        let coreRemaining ← elaboratePatternPairsWithFuel services context fuel remaining
        pure ((selector, corePattern) :: coreRemaining)

  def elaborateObjectSuperclassWithFuel (services : ElaborationServices)
      (context : ElaborationContext) : Nat → SurfaceObjectHeader → Option CoreExpr
    | 0, _ => none
    | _ + 1, .implicitHeader _ _ => some (services.defaultSuperclass context)
    | fuel + 1, .explicitHeader _ receiver _ _ =>
        elaborateExpressionWithFuel services context fuel receiver

  def elaborateClassSuperclassWithFuel (services : ElaborationServices)
      (context : ElaborationContext) : Nat → SurfaceDeclaration → Option CoreExpr
    | 0, _ => none
    | _ + 1, .classDeclaration _ _ _ _ (.defaultInheritance _ _) =>
        some (services.defaultSuperclass context)
    | fuel + 1,
        .classDeclaration _ _ _ _ (.explicitInheritance _ receiver _ _) =>
        elaborateExpressionWithFuel services context fuel receiver
    | fuel + 1, .classDeclaration _ _ _ _ (.mixinChain _ receiver _ _ _) =>
        elaborateExpressionWithFuel services context fuel receiver
    | _ + 1, _ => none
end

def elaborateExpression (services : ElaborationServices)
    (context : ElaborationContext) (expression : SurfaceExpression) :
    Option CoreExpr :=
  elaborateExpressionWithFuel services context services.fuel expression

def elaborateExpressionList (services : ElaborationServices)
    (context : ElaborationContext) (expressions : List SurfaceExpression) :
    Option (List CoreExpr) :=
  elaborateExpressionListWithFuel services context
    services.fuel expressions

def makeElaboratedSend (services : ElaborationServices)
    (context : ElaborationContext) (receiver : SurfaceExpression)
    (selector : Selector) (arguments : List CoreExpr) : Option CoreExpr :=
  makeElaboratedSendWithFuel services context services.fuel
    receiver selector arguments

def elaborateStatement (services : ElaborationServices)
    (context : ElaborationContext) : SurfaceStatement → Option Statement
  | .expression _ expression => do
      pure (.expression (← elaborateExpression services context expression))
  | .returnStatement _ expression =>
      if context.localReturnPermitted || context.nonlocalReturnPermitted then do
        pure (.return (← elaborateExpression services context expression))
      else none

def elaborateStatements (services : ElaborationServices)
    (context : ElaborationContext) :
    List SurfaceStatement → Option (List Statement)
  | [] => some []
  | statement :: remaining => do
      let first ← elaborateStatement services context statement
      let rest ← elaborateStatements services context remaining
      pure (first :: rest)

theorem elaborateExpression_deterministic
    {services : ElaborationServices} {context : ElaborationContext}
    {surface : SurfaceExpression} {first second : CoreExpr}
    (firstResult : elaborateExpression services context surface = some first)
    (secondResult : elaborateExpression services context surface = some second) :
    first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

theorem elaborateStatements_deterministic
    {services : ElaborationServices} {context : ElaborationContext}
    {surface : List SurfaceStatement} {first second : List Statement}
    (firstResult : elaborateStatements services context surface = some first)
    (secondResult : elaborateStatements services context surface = some second) :
    first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
