import Newspeak.DirectProgramDerivation
import Newspeak.FrontEnd
import Newspeak.SurfaceWellFormed

namespace Newspeak

/-- The Specification deliberately leaves the representation of `?x`
    patterns to the Pattern library.  Program derivation therefore receives
    precisely that missing constructor protocol, rather than baking a library
    class into the language semantics. -/
structure EmbeddedArtifactConfig where
  variablePattern : String → CoreExpr
  fuel : Nat

def installDescriptorClosure (image : DerivedProgramImage)
    (descriptor : CascadeDescriptor) : Option DerivedProgramImage :=
  image.addClosure descriptor.closureDeclaration
    [descriptor.receiverParameter] [] []

def setterClosureBody (descriptor : CascadeDescriptor) (name : String) :
    List Statement :=
  let parameterRead : CoreExpr :=
    .implicitSend descriptor.receiverSelector []
      (some (.activationDecl descriptor.closureDeclaration))
      descriptor.immediateClass
  [.expression (.implicitSend (setterSelector name) [parameterRead]
      none descriptor.immediateClass),
   .expression parameterRead]

mutual
  def deriveExpressionArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        SurfaceExpression → Option DerivedProgramImage
    | 0, _, _ => none
    | fuel + 1, image, expression =>
      match expression with
      | .atom _ _ | .identifier _ _ | .selfValue _ | .outer _ _
      | .superValue _ => some image
      | .parenthesized _ nested =>
          deriveExpressionArtifactsWithFuel config identification services
            context fuel image nested
      | .implicitSend _ _ arguments =>
          deriveExpressionListArtifactsWithFuel config identification services
            context fuel image arguments
      | .messageSend _ receiver _ arguments
      | .eventualSend _ receiver _ arguments => do
          let afterReceiver ← deriveExpressionArtifactsWithFuel config
            identification services context fuel image receiver
          deriveExpressionListArtifactsWithFuel config identification services
            context fuel afterReceiver arguments
      | .cascade span receiver initial subsequent => do
          let descriptor ← services.identities.cascadeDescriptor span
            context.immediateClass
          let afterClosure ← installDescriptorClosure image descriptor
          let afterReceiver ← deriveExpressionArtifactsWithFuel config
            identification services context fuel afterClosure receiver
          let afterInitial ← deriveClauseListArtifactsWithFuel config
            identification services context fuel afterReceiver initial
          deriveClauseListArtifactsWithFuel config identification services
            context fuel afterInitial subsequent
      | .setter span name value => do
          let descriptor ← services.identities.cascadeDescriptor span
            context.immediateClass
          let withClosure ← image.addClosure descriptor.closureDeclaration
            [descriptor.receiverParameter] [] (setterClosureBody descriptor name)
          deriveExpressionArtifactsWithFuel config identification services
            context fuel withClosure value
      | .tuple span elements => do
          let descriptor ← services.identities.tupleDescriptor span
            context.immediateClass
          let withClosure ← installDescriptorClosure image descriptor.2
          deriveExpressionListArtifactsWithFuel config identification services
            context fuel withClosure elements
      | .pattern _ pattern =>
          derivePatternArtifactsWithFuel config identification services context
            fuel image pattern
      | .closure span parameters localGroups body => do
          let declaration ← services.identities.closureDeclaration span
          let parameterIds ← formalParameterIds identification parameters
          let declarations := parameters ++ surfaceGroupsDeclarations localGroups
          let binder := binderForDeclarations (.activationDecl declaration)
            declarations
          let closureContext : ElaborationContext :=
            { context with
              enclosingActivation := some declaration
              activationKind := .closure
              binders := binder :: context.binders
              localReturnPermitted := false
              nonlocalReturnPermitted :=
                context.localReturnPermitted || context.nonlocalReturnPermitted }
          let locals ← elaborateLocalGroups identification services
            closureContext localGroups
          let coreBody ← elaborateStatements services closureContext body
          let withClosure ← image.addClosure declaration parameterIds locals coreBody
          let withMembers := addActivationMembers withClosure declaration declarations
          let afterLocals ← deriveSlotGroupListArtifactsWithFuel config
            identification services closureContext fuel withMembers localGroups
          deriveStatementListArtifactsWithFuel config identification services
            closureContext fuel afterLocals body
      | .objectLiteral _ _ | .classExpression _ _ => some image
      | .sequence _ statements =>
          deriveStatementListArtifactsWithFuel config identification services
            context fuel image statements

  def deriveExpressionListArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        List SurfaceExpression → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, [] => some image
    | fuel + 1, image, expression :: remaining => do
        let next ← deriveExpressionArtifactsWithFuel config identification
          services context fuel image expression
        deriveExpressionListArtifactsWithFuel config identification services
          context fuel next remaining

  def deriveClauseArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        SurfaceClause → Option DerivedProgramImage
    | 0, _, _ => none
    | fuel + 1, image, .clause _ _ arguments =>
        deriveExpressionListArtifactsWithFuel config identification services
          context fuel image arguments

  def deriveClauseListArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        List SurfaceClause → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, [] => some image
    | fuel + 1, image, clause :: remaining => do
        let next ← deriveClauseArtifactsWithFuel config identification services
          context fuel image clause
        deriveClauseListArtifactsWithFuel config identification services
          context fuel next remaining

  def derivePatternArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        SurfacePattern → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, .wildcard _ => some image
    | fuel + 1, image, .literal _ expression =>
        deriveExpressionArtifactsWithFuel config identification services context
          fuel image expression
    | _, image, .variable span name => do
        let site ← services.identities.variablePatternSite span
        image.addPatternVariable site (config.variablePattern name)
    | fuel + 1, image, .nested _ pattern =>
        derivePatternArtifactsWithFuel config identification services context
          fuel image pattern
    | fuel + 1, image, .keyword span pairs => do
        let descriptors ← services.identities.keywordPatternDescriptors span
          context.immediateClass
        let withKeywords ← installDescriptorClosure image descriptors.2.1
        let withComponents ← installDescriptorClosure withKeywords
          descriptors.2.2.2
        derivePatternPairListArtifactsWithFuel config identification services
          context fuel withComponents pairs

  def derivePatternPairListArtifactsWithFuel
      (config : EmbeddedArtifactConfig) (identification : IdentificationOutput)
      (services : ElaborationServices) (context : ElaborationContext) : Nat →
        DerivedProgramImage → List (Selector × Option SurfacePattern) →
        Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, [] => some image
    | fuel + 1, image, (_, none) :: remaining =>
        derivePatternPairListArtifactsWithFuel config identification services
          context fuel image remaining
    | fuel + 1, image, (_, some pattern) :: remaining => do
        let next ← derivePatternArtifactsWithFuel config identification services
          context fuel image pattern
        derivePatternPairListArtifactsWithFuel config identification services
          context fuel next remaining

  def deriveStatementArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        SurfaceStatement → Option DerivedProgramImage
    | 0, _, _ => none
    | fuel + 1, image, .expression _ expression
    | fuel + 1, image, .returnStatement _ expression =>
        deriveExpressionArtifactsWithFuel config identification services context
          fuel image expression

  def deriveStatementListArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        List SurfaceStatement → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, [] => some image
    | fuel + 1, image, statement :: remaining => do
        let next ← deriveStatementArtifactsWithFuel config identification services
          context fuel image statement
        deriveStatementListArtifactsWithFuel config identification services
          context fuel next remaining

  def deriveDeclarationArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        SurfaceDeclaration → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, .formal _ _ => some image
    | _ + 1, image, .slot _ _ _ _ none => some image
    | fuel + 1, image, .slot _ _ _ _ (some expression)
    | fuel + 1, image, .lazySlot _ _ _ _ expression =>
        deriveExpressionArtifactsWithFuel config identification services context
          fuel image expression
    | fuel + 1, image, .method span _ _ formals locals body => do
        let declaration ← declarationIdAt identification span "method"
        let activation := declarationActivationIdentity declaration
        let declarations := formals ++ surfaceGroupsDeclarations locals
        let binder := binderForDeclarations (.activationDecl activation) declarations
        let methodContext : ElaborationContext :=
          { context with
            enclosingActivation := some activation
            activationKind := .method
            binders := binder :: context.binders
            localReturnPermitted := true
            nonlocalReturnPermitted := false }
        let afterLocals ← deriveSlotGroupListArtifactsWithFuel config
          identification services methodContext fuel image locals
        deriveStatementListArtifactsWithFuel config identification services
          methodContext fuel afterLocals body
    | _, image, .nestedClass _ _ _ => some image
    | _, image, .classDeclaration _ _ _ _ _ => some image

  def deriveDeclarationListArtifactsWithFuel
      (config : EmbeddedArtifactConfig) (identification : IdentificationOutput)
      (services : ElaborationServices) (context : ElaborationContext) : Nat →
        DerivedProgramImage → List SurfaceDeclaration → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, [] => some image
    | fuel + 1, image, declaration :: remaining => do
        let next ← deriveDeclarationArtifactsWithFuel config identification
          services context fuel image declaration
        deriveDeclarationListArtifactsWithFuel config identification services
          context fuel next remaining

  def deriveSlotGroupArtifactsWithFuel (config : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (services : ElaborationServices)
      (context : ElaborationContext) : Nat → DerivedProgramImage →
        SurfaceSlotGroup → Option DerivedProgramImage
    | 0, _, _ => none
    | fuel + 1, image, .sequential _ declarations
    | fuel + 1, image, .simultaneous _ declarations =>
        deriveDeclarationListArtifactsWithFuel config identification services
          context fuel image declarations

  def deriveSlotGroupListArtifactsWithFuel
      (config : EmbeddedArtifactConfig) (identification : IdentificationOutput)
      (services : ElaborationServices) (context : ElaborationContext) : Nat →
        DerivedProgramImage → List SurfaceSlotGroup → Option DerivedProgramImage
    | 0, _, _ => none
    | _, image, [] => some image
    | fuel + 1, image, group :: remaining => do
        let next ← deriveSlotGroupArtifactsWithFuel config identification services
          context fuel image group
        deriveSlotGroupListArtifactsWithFuel config identification services
          context fuel next remaining
end

def deriveExpressionArtifacts (config : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (image : DerivedProgramImage)
    (expression : SurfaceExpression) : Option DerivedProgramImage :=
  deriveExpressionArtifactsWithFuel config identification services context
    config.fuel image expression

def deriveDirectClassArtifacts (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (unit : SurfaceCompilationUnit)
    (image : DerivedProgramImage) : Option DerivedProgramImage := do
  let (.classDeclaration span _ _ factoryFormals inheritance) :=
    unit.declaration | none
  let classDeclIdentity ← declarationIdAt identification span "classDeclaration"
  let classIdentity : ClassDeclId := ⟨classDeclIdentity.index⟩
  let classStructure ← directClassStructure inheritance
  let (.structure _ headerLocals headerStatements instanceDeclarations
    classDeclarations) := classStructure
  let owner : ClassBodyDecl := .namedClass classIdentity
  let initializer := synthesizedActivationIdentity classDeclIdentity 2
  let services := directElaborationServices config identification
  let headerDeclarations :=
    match headerLocals with
    | none => []
    | some group => surfaceGroupDeclarations group
  let classBinder := binderForDeclarations (.classDecl classIdentity)
    (headerDeclarations ++ instanceDeclarations ++ classDeclarations)
  let initializerBinder := binderForDeclarations (.activationDecl initializer)
    factoryFormals
  let classContext : ElaborationContext :=
    { enclosingClassBody := some owner
      enclosingActivation := none
      activationKind := .topLevel
      immediateClass := some classIdentity
      binders := [classBinder]
      localReturnPermitted := false
      nonlocalReturnPermitted := false }
  let initializerContext : ElaborationContext :=
    { classContext with
      enclosingActivation := some initializer
      activationKind := .method
      binders := initializerBinder :: classContext.binders }
  let afterSuperclass ←
    match inheritance with
    | .defaultInheritance _ _ => some image
    | .explicitInheritance _ receiver initializer _ => do
        let afterReceiver ← deriveExpressionArtifactsWithFuel artifactConfig
          identification services topElaborationContext artifactConfig.fuel image
          receiver
        deriveExpressionListArtifactsWithFuel artifactConfig identification
          services initializerContext artifactConfig.fuel afterReceiver
          initializer.arguments
    | .mixinChain _ _ _ _ _ => none
  let afterHeaderLocals ←
    match headerLocals with
    | none => some afterSuperclass
    | some group =>
        deriveSlotGroupArtifactsWithFuel artifactConfig identification services
          initializerContext artifactConfig.fuel afterSuperclass group
  let afterHeader ← deriveStatementListArtifactsWithFuel artifactConfig
    identification services initializerContext artifactConfig.fuel
    afterHeaderLocals headerStatements
  let afterInstance ← deriveDeclarationListArtifactsWithFuel artifactConfig
    identification services classContext artifactConfig.fuel afterHeader
    instanceDeclarations
  deriveDeclarationListArtifactsWithFuel artifactConfig identification services
    classContext artifactConfig.fuel afterInstance classDeclarations

def deriveCompleteDirectProgram (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Option (Program × CoreExpr) := do
  let (image, expression) ← deriveDirectClass config identification unit
  let complete ← deriveDirectClassArtifacts config artifactConfig identification
    unit image
  pure (complete.install config.baseProgram, expression)

def completeDirectProgramDerivationServices (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat) :
    ProgramDerivationServices :=
  { deriveProgram := deriveCompleteDirectProgram config artifactConfig
    surfaceOK := fun unit _ => surfaceCompilationUnitShapeOK unit
    coreFuel := coreFuel }

theorem deriveCompleteDirectProgram_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {first second : Program × CoreExpr}
    (firstResult : deriveCompleteDirectProgram config artifactConfig unit
      identification = some first)
    (secondResult : deriveCompleteDirectProgram config artifactConfig unit
      identification = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

theorem deriveExpressionArtifacts_deterministic
    {config : EmbeddedArtifactConfig} {identification : IdentificationOutput}
    {services : ElaborationServices} {context : ElaborationContext}
    {image first second : DerivedProgramImage} {expression : SurfaceExpression}
    (firstResult : deriveExpressionArtifacts config identification services
      context image expression = some first)
    (secondResult : deriveExpressionArtifacts config identification services
      context image expression = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
