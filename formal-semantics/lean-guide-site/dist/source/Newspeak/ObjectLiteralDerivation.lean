import Newspeak.MixinChainDerivation

namespace Newspeak

def objectLiteralOwnerFromContext (context : ElaborationContext) : ClassOwner :=
  match context.enclosingActivation, context.enclosingClassBody with
  | some _, _ => .activationOwner
  | none, some (.namedClass _) => .classOwner
  | none, some (.objectLiteral _) => .objectLiteralOwner
  | none, none => .topOwner

def objectHeaderStructure : SurfaceObjectHeader → SurfaceClassStructure
  | .implicitHeader _ classStructure
  | .explicitHeader _ _ _ classStructure => classStructure

def objectHeaderSuperclassSyntax : SurfaceObjectHeader → SuperclassSyntax
  | .implicitHeader _ _ => .implicitSuperclass
  | .explicitHeader _ _ _ _ => .explicitSuperclass

def objectHeaderSuperclass (services : ElaborationServices)
    (context : ElaborationContext) : SurfaceObjectHeader → Option CoreExpr
  | .implicitHeader _ _ => some (services.defaultSuperclass context)
  | .explicitHeader _ receiver _ _ =>
      elaborateExpression services context receiver

def objectHeaderSuperclassMessage (services : ElaborationServices)
    (context : ElaborationContext) : SurfaceObjectHeader → Option MessageTemplate
  | .implicitHeader _ _ => some ⟨⟨"new"⟩, []⟩
  | .explicitHeader _ _ initializer _ =>
      elaborateMessageTemplate services context initializer

def deriveObjectLiteralInto (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (context : ElaborationContext)
    (image : DerivedProgramImage) (span : SourceSpan)
    (header : SurfaceObjectHeader) :
    Option (DerivedProgramImage × CoreExpr) := do
  let services := directElaborationServices config identification
  let literal ← services.identities.objectLiteralDeclaration span
  let syntheticDecl : DeclId := ⟨cantorPairNat literal.index 500⟩
  let owner : ClassBodyDecl := .objectLiteral literal
  let instanceMixin := objectLiteralMixinIdentity literal false
  let classMixin := objectLiteralMixinIdentity literal true
  let initializer := synthesizedActivationIdentity syntheticDecl 2
  let classInitializer := synthesizedActivationIdentity syntheticDecl 3
  let (.structure _ headerLocals headerStatements instanceDeclarations
    classDeclarations) := objectHeaderStructure header
  let headerDeclarations :=
    match headerLocals with
    | none => []
    | some group => surfaceGroupDeclarations group
  let objectBinder := binderForDeclarations (.objectLiteralDecl literal)
    (headerDeclarations ++ instanceDeclarations ++ classDeclarations)
  let objectContext : ElaborationContext :=
    { context with
      enclosingClassBody := some owner
      enclosingActivation := context.enclosingActivation
      binders := objectBinder :: context.binders }
  let initializerContext : ElaborationContext :=
    { objectContext with
      enclosingActivation := some initializer
      activationKind := .method
      localReturnPermitted := false
      nonlocalReturnPermitted := false }
  let groups ← elaborateInitializerGroups identification services
    initializerContext headerLocals
  let body ← elaborateStatements services initializerContext headerStatements
  let slots ← physicalSlotIds identification headerDeclarations
  let instanceDefinition := emptyMixinDefinition owner initializer ⟨"new"⟩ []
    slots groups body
  let classDefinition := emptyMixinDefinition owner classInitializer ⟨"new"⟩
    [] [] [] []
  let image₁ ← image.addMixin instanceMixin instanceDefinition
  let image₂ ← image₁.addMixin classMixin classDefinition
  let image₂ ← addDerivedMethods image₂ classMixin
    [primaryFactoryMethod syntheticDecl owner ⟨"new"⟩ []]
  let image₃ :=
    { image₂ with
      declarationMixins := image₂.declarationMixins.install owner instanceMixin }
  let image₄ ← deriveMemberDeclarations identification services initializerContext
    owner instanceMixin image₃ headerDeclarations
  let image₅ ← deriveMemberDeclarations identification services objectContext owner
    instanceMixin image₄ instanceDeclarations
  let image₆ ← deriveMemberDeclarations identification services objectContext owner
    classMixin image₅ classDeclarations
  let superclassMessage ← objectHeaderSuperclassMessage services
    initializerContext header
  let descriptor : ObjectLiteralDescriptor :=
    { declaration := literal
      superclassSyntax := objectHeaderSuperclassSyntax header
      instanceMixin := instanceMixin
      classMixin := classMixin
      initializerDeclaration := initializer
      superclassMessage := superclassMessage }
  let image₇ ← image₆.addObjectLiteral descriptor
    (objectLiteralOwnerFromContext context)
  let afterHeaderLocals ←
    match headerLocals with
    | none => some image₇
    | some group =>
        deriveSlotGroupArtifactsWithFuel artifactConfig identification services
          initializerContext artifactConfig.fuel image₇ group
  let afterHeader ← deriveStatementListArtifactsWithFuel artifactConfig
    identification services initializerContext artifactConfig.fuel
    afterHeaderLocals headerStatements
  let afterInstance ← deriveDeclarationListArtifactsWithFuel artifactConfig
    identification services objectContext artifactConfig.fuel afterHeader
    instanceDeclarations
  let afterClass ← deriveDeclarationListArtifactsWithFuel artifactConfig
    identification services objectContext artifactConfig.fuel afterInstance
    classDeclarations
  let afterInstanceNested ← deriveNestedClassDeclarationsWithFuel config
    artifactConfig identification artifactConfig.fuel objectContext owner
    instanceMixin afterClass instanceDeclarations
  let complete ← deriveNestedClassDeclarationsWithFuel config artifactConfig
    identification artifactConfig.fuel objectContext owner classMixin
    afterInstanceNested classDeclarations
  let superclass ← objectHeaderSuperclass services context header
  pure (complete, .objectLiteral literal superclass)

theorem deriveObjectLiteralInto_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {identification : IdentificationOutput} {context : ElaborationContext}
    {image : DerivedProgramImage} {first second : DerivedProgramImage × CoreExpr}
    {span : SourceSpan}
    {header : SurfaceObjectHeader}
    (firstResult : deriveObjectLiteralInto config artifactConfig identification
      context image span header = some first)
    (secondResult : deriveObjectLiteralInto config artifactConfig identification
      context image span header = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
