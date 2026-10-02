import Newspeak.ObjectLiteralDerivation

namespace Newspeak

mutual
  partial def deriveStructuralExpressionArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : SurfaceExpression → Option DerivedProgramImage
    | .atom _ _ | .identifier _ _ | .selfValue _ | .outer _ _
    | .superValue _ => some image
    | .parenthesized _ expression | .setter _ _ expression =>
        deriveStructuralExpressionArtifacts config artifactConfig identification
          context image expression
    | .implicitSend _ _ arguments | .tuple _ arguments =>
        deriveStructuralExpressionListArtifacts config artifactConfig
          identification context image arguments
    | .messageSend _ receiver _ arguments
    | .eventualSend _ receiver _ arguments => do
        let next ← deriveStructuralExpressionArtifacts config artifactConfig
          identification context image receiver
        deriveStructuralExpressionListArtifacts config artifactConfig
          identification context next arguments
    | .cascade _ receiver initial subsequent => do
        let next ← deriveStructuralExpressionArtifacts config artifactConfig
          identification context image receiver
        let next ← deriveStructuralClauseListArtifacts config artifactConfig
          identification context next initial
        deriveStructuralClauseListArtifacts config artifactConfig identification
          context next subsequent
    | .pattern _ pattern =>
        deriveStructuralPatternArtifacts config artifactConfig identification
          context image pattern
    | .closure span parameters locals body => do
        let services := directElaborationServices config identification
        let declaration ← services.identities.closureDeclaration span
        let declarations := parameters ++ surfaceGroupsDeclarations locals
        let binder := binderForDeclarations (.activationDecl declaration) declarations
        let closureContext : ElaborationContext :=
          { context with
            enclosingActivation := some declaration
            activationKind := .closure
            binders := binder :: context.binders
            localReturnPermitted := false
            nonlocalReturnPermitted :=
              context.localReturnPermitted || context.nonlocalReturnPermitted }
        let next ← deriveStructuralSlotGroupListArtifacts config artifactConfig
          identification closureContext image locals
        deriveStructuralStatementListArtifacts config artifactConfig identification
          closureContext next body
    | .objectLiteral span header => do
        let (next, _) ← deriveObjectLiteralInto config artifactConfig
          identification context image span header
        deriveStructuralObjectHeaderArtifacts config artifactConfig identification
          context next span header
    | .classExpression _ declaration => do
        let owner := objectLiteralOwnerFromContext context
        let (next, _) ← match declaration with
          | .classDeclaration _ _ _ _ (.mixinChain _ _ _ _ none) =>
              deriveBodylessMixinChainInto config artifactConfig identification
                context owner image declaration
          | _ =>
              deriveClassDeclarationIntoWithFuel config artifactConfig
                identification artifactConfig.fuel context owner image declaration
        deriveStructuralClassDeclarationContents config artifactConfig
          identification context next declaration
    | .sequence _ statements =>
        deriveStructuralStatementListArtifacts config artifactConfig identification
          context image statements

  partial def deriveStructuralExpressionListArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : List SurfaceExpression →
      Option DerivedProgramImage
    | [] => some image
    | expression :: remaining => do
        let next ← deriveStructuralExpressionArtifacts config artifactConfig
          identification context image expression
        deriveStructuralExpressionListArtifacts config artifactConfig
          identification context next remaining

  partial def deriveStructuralClauseArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : SurfaceClause → Option DerivedProgramImage
    | .clause _ _ arguments =>
        deriveStructuralExpressionListArtifacts config artifactConfig
          identification context image arguments

  partial def deriveStructuralClauseListArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : List SurfaceClause →
      Option DerivedProgramImage
    | [] => some image
    | clause :: remaining => do
        let next ← deriveStructuralClauseArtifacts config artifactConfig
          identification context image clause
        deriveStructuralClauseListArtifacts config artifactConfig identification
          context next remaining

  partial def deriveStructuralPatternArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : SurfacePattern → Option DerivedProgramImage
    | .wildcard _ | .variable _ _ => some image
    | .literal _ expression =>
        deriveStructuralExpressionArtifacts config artifactConfig identification
          context image expression
    | .nested _ pattern =>
        deriveStructuralPatternArtifacts config artifactConfig identification
          context image pattern
    | .keyword _ pairs =>
        pairs.foldlM
          (fun next pair => match pair.2 with
            | none => some next
            | some pattern => deriveStructuralPatternArtifacts config
                artifactConfig identification context next pattern)
          image

  partial def deriveStructuralStatementListArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : List SurfaceStatement →
      Option DerivedProgramImage
    | [] => some image
    | statement :: remaining => do
        let expression := match statement with
          | .expression _ value | .returnStatement _ value => value
        let next ← deriveStructuralExpressionArtifacts config artifactConfig
          identification context image expression
        deriveStructuralStatementListArtifacts config artifactConfig
          identification context next remaining

  partial def deriveStructuralDeclarationArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : SurfaceDeclaration →
      Option DerivedProgramImage
    | .formal _ _ | .slot _ _ _ _ none => some image
    | .slot _ _ _ _ (some expression) | .lazySlot _ _ _ _ expression =>
        deriveStructuralExpressionArtifacts config artifactConfig identification
          context image expression
    | .method span _ _ formals locals body => do
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
        let next ← deriveStructuralSlotGroupListArtifacts config artifactConfig
          identification methodContext image locals
        deriveStructuralStatementListArtifacts config artifactConfig
          identification methodContext next body
    | .nestedClass _ _ declaration =>
        deriveStructuralClassDeclarationContents config artifactConfig
          identification context image declaration
    | declaration@(.classDeclaration _ _ _ _ _) =>
        deriveStructuralClassDeclarationContents config artifactConfig
          identification context image declaration

  partial def deriveStructuralDeclarationListArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : List SurfaceDeclaration →
      Option DerivedProgramImage
    | [] => some image
    | declaration :: remaining => do
        let next ← deriveStructuralDeclarationArtifacts config artifactConfig
          identification context image declaration
        deriveStructuralDeclarationListArtifacts config artifactConfig
          identification context next remaining

  partial def deriveStructuralSlotGroupArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : SurfaceSlotGroup → Option DerivedProgramImage
    | .sequential _ declarations | .simultaneous _ declarations =>
        deriveStructuralDeclarationListArtifacts config artifactConfig
          identification context image declarations

  partial def deriveStructuralSlotGroupListArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (context : ElaborationContext)
      (image : DerivedProgramImage) : List SurfaceSlotGroup →
      Option DerivedProgramImage
    | [] => some image
    | group :: remaining => do
        let next ← deriveStructuralSlotGroupArtifacts config artifactConfig
          identification context image group
        deriveStructuralSlotGroupListArtifacts config artifactConfig
          identification context next remaining

  partial def deriveStructuralClassStructureArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput)
      (classContext initializerContext : ElaborationContext)
      (image : DerivedProgramImage) : SurfaceClassStructure →
      Option DerivedProgramImage
    | .structure _ headerLocals headerStatements instanceDeclarations
        classDeclarations => do
      let next ← match headerLocals with
        | none => some image
        | some group =>
            deriveStructuralSlotGroupArtifacts config artifactConfig
              identification initializerContext image group
      let next ← deriveStructuralStatementListArtifacts config artifactConfig
        identification initializerContext next headerStatements
      let next ← deriveStructuralDeclarationListArtifacts config artifactConfig
        identification classContext next instanceDeclarations
      deriveStructuralDeclarationListArtifacts config artifactConfig
        identification classContext next classDeclarations

  partial def deriveStructuralClassDeclarationContents
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (parentContext : ElaborationContext)
      (image : DerivedProgramImage) : SurfaceDeclaration →
      Option DerivedProgramImage
    | .classDeclaration span _ _ factoryFormals inheritance => do
      let declaration ← declarationIdAt identification span "classDeclaration"
      let classIdentity : ClassDeclId := ⟨declaration.index⟩
      let owner : ClassBodyDecl := .namedClass classIdentity
      let classStructure := match inheritance with
        | .defaultInheritance _ body | .explicitInheritance _ _ _ body => body
        | .mixinChain inheritanceSpan _ _ _ body =>
            body.getD (.structure inheritanceSpan none [] [] [])
      let (.structure _ headerLocals _ instanceDeclarations classDeclarations) :=
        classStructure
      let headerDeclarations := headerLocals.map surfaceGroupDeclarations |>.getD []
      let binder := binderForDeclarations (.classDecl classIdentity)
        (headerDeclarations ++ instanceDeclarations ++ classDeclarations)
      let classContext : ElaborationContext :=
        { parentContext with
          enclosingClassBody := some owner
          immediateClass := some classIdentity
          binders := binder :: parentContext.binders }
      let initializer := synthesizedActivationIdentity declaration 2
      let initializerBinder := binderForDeclarations
        (.activationDecl initializer) factoryFormals
      let initializerContext : ElaborationContext :=
        { classContext with
          enclosingActivation := some initializer
          activationKind := .method
          binders := initializerBinder :: classContext.binders
          localReturnPermitted := false
          nonlocalReturnPermitted := false }
      let next ← match inheritance with
        | .defaultInheritance _ _ => some image
        | .explicitInheritance _ receiver clause _ => do
            let next ← deriveStructuralExpressionArtifacts config artifactConfig
              identification parentContext image receiver
            deriveStructuralClauseArtifacts config artifactConfig identification
              initializerContext next clause
        | .mixinChain _ receiver clause additional _ => do
            let next ← deriveStructuralExpressionArtifacts config artifactConfig
              identification parentContext image receiver
            let next ← deriveStructuralClauseArtifacts config artifactConfig
              identification initializerContext next clause
            additional.foldlM (fun current head => do
              let current ← deriveStructuralExpressionArtifacts config
                artifactConfig identification parentContext current head.receiver
              deriveStructuralClauseArtifacts config artifactConfig identification
                initializerContext current head.initializer) next
      deriveStructuralClassStructureArtifacts config artifactConfig identification
        classContext initializerContext next classStructure
    | _ => none

  partial def deriveStructuralObjectHeaderArtifacts
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) (parentContext : ElaborationContext)
      (image : DerivedProgramImage) (span : SourceSpan)
      (header : SurfaceObjectHeader) : Option DerivedProgramImage := do
    let services := directElaborationServices config identification
    let literal ← services.identities.objectLiteralDeclaration span
    let syntheticDecl : DeclId := ⟨cantorPairNat literal.index 500⟩
    let owner : ClassBodyDecl := .objectLiteral literal
    let classStructure := objectHeaderStructure header
    let (.structure _ headerLocals _ instanceDeclarations classDeclarations) :=
      classStructure
    let headerDeclarations := headerLocals.map surfaceGroupDeclarations |>.getD []
    let binder := binderForDeclarations (.objectLiteralDecl literal)
      (headerDeclarations ++ instanceDeclarations ++ classDeclarations)
    let objectContext : ElaborationContext :=
      { parentContext with
        enclosingClassBody := some owner
        binders := binder :: parentContext.binders }
    let initializerContext : ElaborationContext :=
      { objectContext with
        enclosingActivation := some (synthesizedActivationIdentity syntheticDecl 2)
        activationKind := .method
        localReturnPermitted := false
        nonlocalReturnPermitted := false }
    let next ← match header with
      | .implicitHeader _ _ => some image
      | .explicitHeader _ receiver clause _ => do
          let next ← deriveStructuralExpressionArtifacts config artifactConfig
            identification parentContext image receiver
          deriveStructuralClauseArtifacts config artifactConfig identification
            initializerContext next clause
    deriveStructuralClassStructureArtifacts config artifactConfig identification
      objectContext initializerContext next classStructure
end

def deriveClassProgramWithStructuralArtifacts
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) :
    Option (Program × CoreExpr) := do
  let (image, expression) ← deriveClassDeclarationIntoWithFuel config
    artifactConfig identification artifactConfig.fuel topElaborationContext
    .topOwner DerivedProgramImage.empty unit.declaration
  let complete ← deriveStructuralClassDeclarationContents config artifactConfig
    identification topElaborationContext image unit.declaration
  pure (complete.install config.baseProgram, expression)

theorem deriveClassProgramWithStructuralArtifacts_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {first second : Program × CoreExpr}
    (firstResult : deriveClassProgramWithStructuralArtifacts config artifactConfig
      unit identification = some first)
    (secondResult : deriveClassProgramWithStructuralArtifacts config artifactConfig
      unit identification = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
