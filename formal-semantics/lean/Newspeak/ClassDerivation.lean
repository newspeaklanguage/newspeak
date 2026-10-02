import Newspeak.EmbeddedArtifacts

namespace Newspeak

def nestedClassGetter (wrapper : DeclId) (owner : ClassBodyDecl)
    (access : Access) (name : String) (child : ClassDeclId)
    (classExpression : CoreExpr) : DerivedMethod :=
  { definition :=
      { identity := synthesizedMethodIdentity wrapper 10
        activationDeclaration := synthesizedActivationIdentity wrapper 10
        selector := ⟨name⟩
        access := access
        parameters := []
        locals := []
        owner := owner
        body := ⟨wrapper.index⟩ }
    locals := []
    body := [.return (.nestedClass child classExpression)] }

def addActorSeedIfTop (image : DerivedProgramImage) (owner : ClassOwner)
    (instanceMixin : MixinId) (descriptor : ClassBodyDescriptor) :
    Option DerivedProgramImage :=
  match owner with
  | .topOwner => do
      guard ((image.actorSeeds instanceMixin).isNone)
      pure { image with
        actorSeeds := image.actorSeeds.install instanceMixin
          { declaration := descriptor.declaration
            classMixin := descriptor.classMixin
            factorySelector := descriptor.factorySelector
            factoryParameters := descriptor.factoryParameters
            initializerDeclaration := descriptor.initializerDeclaration
            superclassMessage := descriptor.superclassMessage } }
  | _ => some image

def selectorArity (isUnary : Selector → Bool) (selector : Selector) : Nat :=
  let keywordArity := selector.spelling.toList.count ':'
  if keywordArity > 0 then keywordArity
  else if isUnary selector then 0 else 1

def applicationDeclarationIdentity (enclosing : DeclId) (position : Nat) :
    ClassDeclId :=
  ⟨cantorPairNat enclosing.index (100 + position)⟩

def applicationInitializerIdentity (enclosing : DeclId) (position : Nat) :
    ActivationDeclId :=
  synthesizedActivationIdentity enclosing (100 + position)

def applicationParameterIdentities (enclosing : DeclId) (position arity : Nat) :
    List ParameterId :=
  (List.range arity).map fun index =>
    synthesizedParameterIdentity enclosing
      (cantorPairNat (100 + position) index)

def elaborateMessageTemplate (services : ElaborationServices)
    (context : ElaborationContext) (clause : SurfaceClause) :
    Option MessageTemplate := do
  pure ⟨clause.selector,
    (← elaborateExpressionList services context clause.arguments)⟩

def installApplicationClassMixin (enclosing : DeclId) (position : Nat)
    (declaration : ClassDeclId) (owner : ClassBodyDecl) (selector : Selector)
    (parameters : List ParameterId) (image : DerivedProgramImage) :
    Option (DerivedProgramImage × MixinId × ActivationDeclId) := do
  let mixin := applicationClassMixinIdentity declaration
  let initializer := applicationInitializerIdentity enclosing position
  let definition := emptyMixinDefinition owner initializer ⟨"new"⟩ [] [] [] []
  let withMixin ← image.addMixin mixin definition
  let withFactory ← addDerivedMethods withMixin mixin
    [primaryFactoryMethod ⟨declaration.index⟩ owner selector parameters]
  pure (withFactory, mixin, initializer)

def deriveAnonymousApplication (config : DirectDerivationConfig)
    (identification : IdentificationOutput) (enclosing : DeclId)
    (position : Nat) (ownerKind : ClassOwner) (context : ElaborationContext)
    (image : DerivedProgramImage) (superclass : CoreExpr)
    (superclassInitializer : SurfaceClause) (head : SurfaceInheritanceHead) :
    Option (DerivedProgramImage × CoreExpr × SurfaceClause) := do
  let services := directElaborationServices config identification
  let declaration := applicationDeclarationIdentity enclosing position
  let owner : ClassBodyDecl := .namedClass declaration
  let arity := selectorArity config.isUnarySelector head.initializer.selector
  let parameters := applicationParameterIdentities enclosing position arity
  let (withMixin, classMixin, initializer) ← installApplicationClassMixin
    enclosing position declaration owner head.initializer.selector parameters image
  let superclassMessage ← elaborateMessageTemplate services context
    superclassInitializer
  let mixinMessage ← elaborateMessageTemplate services context head.initializer
  let descriptor : MixinApplicationDescriptor :=
    { declaration := declaration
      factorySelector := head.initializer.selector
      factoryParameters := parameters
      classMixin := classMixin
      initializerDeclaration := initializer
      superclassMessage := superclassMessage
      mixinMessage := mixinMessage }
  let installed ← withMixin.addMixinApplication descriptor ownerKind
  let source ← elaborateExpression services context head.receiver
  pure (installed, .mixinApply declaration superclass source, head.initializer)

def foldAnonymousApplications (config : DirectDerivationConfig)
    (identification : IdentificationOutput) (enclosing : DeclId)
    (ownerKind : ClassOwner) (context : ElaborationContext) : Nat →
    DerivedProgramImage → CoreExpr → SurfaceClause →
    List SurfaceInheritanceHead →
    Option (DerivedProgramImage × CoreExpr × SurfaceClause)
  | _, image, superclass, initializer, [] =>
      some (image, superclass, initializer)
  | position, image, superclass, initializer, head :: remaining => do
      let (nextImage, nextSuperclass, nextInitializer) ←
        deriveAnonymousApplication config identification enclosing position
          ownerKind context image superclass initializer head
      foldAnonymousApplications config identification enclosing ownerKind context
        (position + 1) nextImage nextSuperclass nextInitializer remaining

def deriveBodylessMixinChainInto (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (context : ElaborationContext)
    (ownerKind : ClassOwner) (image : DerivedProgramImage)
    (declaration : SurfaceDeclaration) :
    Option (DerivedProgramImage × CoreExpr) := do
  let (.classDeclaration span _ factorySelector factoryFormals
    (.mixinChain _ baseReceiver baseInitializer additional none)) :=
      declaration | none
  let enclosing ← declarationIdAt identification span "classDeclaration"
  let namedDeclaration : ClassDeclId := ⟨enclosing.index⟩
  let services := directElaborationServices config identification
  let base ← elaborateExpression services context baseReceiver
  let last ← additional.getLast?
  guard (last.initializer.selector == factorySelector)
  let prefixHeads := additional.dropLast
  let (prefixImage, prefixClass, precedingInitializer) ←
    foldAnonymousApplications config identification enclosing ownerKind context 1
      image base baseInitializer prefixHeads
  let factoryParameters ← formalParameterIds identification factoryFormals
  let owner : ClassBodyDecl := .namedClass namedDeclaration
  let (withMixin, classMixin, initializer) ← installApplicationClassMixin
    enclosing (prefixHeads.length + 1) namedDeclaration owner factorySelector
    factoryParameters prefixImage
  let superclassMessage ← elaborateMessageTemplate services context
    precedingInitializer
  let mixinMessage ← elaborateMessageTemplate services context last.initializer
  let descriptor : MixinApplicationDescriptor :=
    { declaration := namedDeclaration
      factorySelector := factorySelector
      factoryParameters := factoryParameters
      classMixin := classMixin
      initializerDeclaration := initializer
      superclassMessage := superclassMessage
      mixinMessage := mixinMessage }
  let installed ← withMixin.addMixinApplication descriptor ownerKind
  let installed ← match context.immediateClass with
    | none => some installed
    | some parent => installed.addLexicalParent namedDeclaration parent
  let source ← elaborateExpression services context last.receiver
  let expression := CoreExpr.mixinApply namedDeclaration prefixClass source
  let afterBaseArtifacts ← deriveExpressionArtifacts artifactConfig identification
    services context installed baseReceiver
  let afterPrefixArtifacts ← prefixHeads.foldlM
    (fun current head => do
      let afterReceiver ← deriveExpressionArtifacts artifactConfig identification
        services context current head.receiver
      deriveExpressionListArtifactsWithFuel artifactConfig identification services
        context artifactConfig.fuel afterReceiver head.initializer.arguments)
    afterBaseArtifacts
  let afterLastReceiver ← deriveExpressionArtifacts artifactConfig identification
    services context afterPrefixArtifacts last.receiver
  let complete ← deriveExpressionListArtifactsWithFuel artifactConfig
    identification services context artifactConfig.fuel afterLastReceiver
    last.initializer.arguments
  pure (complete, expression)

mutual
  def deriveClassDeclarationIntoWithFuel (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) : Nat → ElaborationContext →
        ClassOwner → DerivedProgramImage → SurfaceDeclaration →
        Option (DerivedProgramImage × CoreExpr)
    | 0, _, _, _, _ => none
    | fuel + 1, parentContext, ownerKind, image,
        .classDeclaration span _name factorySelector factoryFormals inheritance => do
      let classDeclIdentity ← declarationIdAt identification span "classDeclaration"
      let classIdentity : ClassDeclId := ⟨classDeclIdentity.index⟩
      let classStructure ← match inheritance with
        | .defaultInheritance _ body | .explicitInheritance _ _ _ body =>
            some body
        | .mixinChain _ _ _ _ body => body
      let (.structure _ headerLocals headerStatements instanceDeclarations
        classDeclarations) := classStructure
      let owner : ClassBodyDecl := .namedClass classIdentity
      let instanceMixin := declarationMixinIdentity classIdentity false
      let classMixin := declarationMixinIdentity classIdentity true
      let factoryParameters ← formalParameterIds identification factoryFormals
      let initializer := synthesizedActivationIdentity classDeclIdentity 2
      let services := directElaborationServices config identification
      let headerDeclarations :=
        match headerLocals with
        | none => []
        | some group => surfaceGroupDeclarations group
      let classBinder := binderForDeclarations (.classDecl classIdentity)
        (headerDeclarations ++ instanceDeclarations ++ classDeclarations)
      let classContext : ElaborationContext :=
        { enclosingClassBody := some owner
          enclosingActivation := parentContext.enclosingActivation
          activationKind := parentContext.activationKind
          immediateClass := some classIdentity
          binders := classBinder :: parentContext.binders
          localReturnPermitted := parentContext.localReturnPermitted
          nonlocalReturnPermitted := parentContext.nonlocalReturnPermitted }
      let initializerBinder := binderForDeclarations (.activationDecl initializer)
        factoryFormals
      let initializerContext : ElaborationContext :=
        { classContext with
          enclosingActivation := some initializer
          activationKind := .method
          binders := initializerBinder :: classContext.binders
          localReturnPermitted := false
          nonlocalReturnPermitted := false }
      let initializerGroups ← elaborateInitializerGroups identification services
        initializerContext headerLocals
      let initializerBody ← elaborateStatements services initializerContext
        headerStatements
      let instanceSlots ← physicalSlotIds identification headerDeclarations
      let instanceDefinition := emptyMixinDefinition owner initializer
        factorySelector factoryParameters instanceSlots initializerGroups
        initializerBody
      let classInitializer := synthesizedActivationIdentity classDeclIdentity 3
      let classDefinition := emptyMixinDefinition owner classInitializer ⟨"new"⟩
        [] [] [] []
      let image₁ ← image.addMixin instanceMixin instanceDefinition
      let image₂ ← image₁.addMixin classMixin classDefinition
      let image₂ ← addDerivedMethods image₂ classMixin
        [primaryFactoryMethod classDeclIdentity owner factorySelector
          factoryParameters]
      let image₃ :=
        { image₂ with
          declarationMixins := image₂.declarationMixins.install owner instanceMixin }
      let image₃ := addActivationMembers image₃ initializer factoryFormals
      let image₄ ← deriveMemberDeclarations identification services
        initializerContext owner instanceMixin image₃ headerDeclarations
      let image₅ ← deriveMemberDeclarations identification services classContext
        owner instanceMixin image₄ instanceDeclarations
      let image₆ ← deriveMemberDeclarations identification services classContext
        owner classMixin image₅ classDeclarations
      let superclassMessage ← match inheritance with
        | .defaultInheritance _ _ | .explicitInheritance _ _ _ _ =>
            directSuperclassMessage services initializerContext inheritance
        | .mixinChain _ _ initializer _ _ =>
            elaborateMessageTemplate services initializerContext initializer
      let descriptor : ClassBodyDescriptor :=
        { declaration := classIdentity
          superclassSyntax := match inheritance with
            | .defaultInheritance _ _ => .implicitSuperclass
            | .explicitInheritance _ _ _ _ | .mixinChain _ _ _ _ _ =>
                .explicitSuperclass
          factorySelector := factorySelector
          factoryParameters := factoryParameters
          instanceMixin := instanceMixin
          classMixin := classMixin
          initializerDeclaration := initializer
          superclassMessage := superclassMessage }
      let image₇ ← image₆.addClassBody descriptor ownerKind
      let image₈ ← addActorSeedIfTop image₇ ownerKind instanceMixin descriptor
      let image₉ ←
        match parentContext.immediateClass with
        | none => some image₈
        | some parent => image₈.addLexicalParent classIdentity parent
      let afterSuperclass ←
        match inheritance with
        | .defaultInheritance _ _ => some image₉
        | .explicitInheritance _ receiver clause _ => do
            let afterReceiver ← deriveExpressionArtifactsWithFuel artifactConfig
              identification services parentContext fuel image₉ receiver
            deriveExpressionListArtifactsWithFuel artifactConfig identification
              services initializerContext fuel afterReceiver clause.arguments
        | .mixinChain _ receiver clause additional _ => do
            let afterReceiver ← deriveExpressionArtifactsWithFuel artifactConfig
              identification services parentContext fuel image₉ receiver
            let afterBase ← deriveExpressionListArtifactsWithFuel artifactConfig
              identification services initializerContext fuel afterReceiver
              clause.arguments
            additional.foldlM (fun current head => do
              let afterHead ← deriveExpressionArtifactsWithFuel artifactConfig
                identification services parentContext fuel current head.receiver
              deriveExpressionListArtifactsWithFuel artifactConfig identification
                services initializerContext fuel afterHead head.initializer.arguments)
              afterBase
      let afterHeaderLocals ←
        match headerLocals with
        | none => some afterSuperclass
        | some group =>
            deriveSlotGroupArtifactsWithFuel artifactConfig identification
              services initializerContext fuel afterSuperclass group
      let afterHeader ← deriveStatementListArtifactsWithFuel artifactConfig
        identification services initializerContext fuel afterHeaderLocals
        headerStatements
      let afterInstanceArtifacts ← deriveDeclarationListArtifactsWithFuel
        artifactConfig identification services classContext fuel afterHeader
        instanceDeclarations
      let afterClassArtifacts ← deriveDeclarationListArtifactsWithFuel
        artifactConfig identification services classContext fuel
        afterInstanceArtifacts classDeclarations
      let afterInstanceNested ← deriveNestedClassDeclarationsWithFuel config
        artifactConfig identification fuel classContext owner instanceMixin
        afterClassArtifacts instanceDeclarations
      let afterClassNested ← deriveNestedClassDeclarationsWithFuel config
        artifactConfig identification fuel classContext owner classMixin
        afterInstanceNested classDeclarations
      let superclass ← match inheritance with
        | .defaultInheritance _ _ | .explicitInheritance _ _ _ _ =>
            directSuperclassExpression services parentContext inheritance
        | .mixinChain _ receiver _ _ _ =>
            elaborateExpression services parentContext receiver
      match inheritance with
      | .mixinChain _ _ baseInitializer additional (some _) => do
          let (foldedImage, foldedCore, finalInitializer) ←
            foldAnonymousApplications config identification classDeclIdentity
              ownerKind parentContext 1 afterClassNested superclass
              baseInitializer additional
          let finalMessage ← elaborateMessageTemplate services initializerContext
            finalInitializer
          let complete ← foldedImage.replaceClassBodySuperclassMessage
            classIdentity finalMessage
          pure (complete, .classBody classIdentity foldedCore)
      | _ => pure (afterClassNested, .classBody classIdentity superclass)
    | _ + 1, _, _, _, _ => none

  def deriveNestedClassDeclarationsWithFuel
      (config : DirectDerivationConfig)
      (artifactConfig : EmbeddedArtifactConfig)
      (identification : IdentificationOutput) : Nat → ElaborationContext →
        ClassBodyDecl → MixinId → DerivedProgramImage →
        List SurfaceDeclaration → Option DerivedProgramImage
    | 0, _, _, _, _, _ => none
    | _, _, _, _, image, [] => some image
    | fuel + 1, classContext, owner, mixin, image,
        .nestedClass wrapperSpan access childDeclaration :: remaining => do
      let wrapper ← declarationIdAt identification wrapperSpan "nestedClass"
      let (.classDeclaration childSpan childName _ _ _) := childDeclaration
        | none
      let childDecl ← declarationIdAt identification childSpan "classDeclaration"
      let child : ClassDeclId := ⟨childDecl.index⟩
      let (withChild, childExpression) ← match childDeclaration with
        | .classDeclaration _ _ _ _ (.mixinChain _ _ _ _ none) =>
            deriveBodylessMixinChainInto config artifactConfig identification
              classContext .classOwner image childDeclaration
        | _ =>
            deriveClassDeclarationIntoWithFuel config artifactConfig
              identification fuel classContext .classOwner image childDeclaration
      let withGetter ← withChild.addMethod mixin
        (nestedClassGetter wrapper owner (accessOrProtected access) childName child
          childExpression).definition
        (nestedClassGetter wrapper owner (accessOrProtected access) childName child
          childExpression).locals
        (nestedClassGetter wrapper owner (accessOrProtected access) childName child
          childExpression).body
      let withNested ← withGetter.addNestedDeclaration mixin child
      deriveNestedClassDeclarationsWithFuel config artifactConfig identification
        fuel classContext owner mixin withNested remaining
    | fuel + 1, classContext, owner, mixin, image, _ :: remaining =>
      deriveNestedClassDeclarationsWithFuel config artifactConfig identification
        fuel classContext owner mixin image remaining
end

def deriveClassProgram (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Option (Program × CoreExpr) := do
  let (image, expression) ← deriveClassDeclarationIntoWithFuel config
    artifactConfig identification artifactConfig.fuel topElaborationContext
    .topOwner DerivedProgramImage.empty unit.declaration
  pure (image.install config.baseProgram, expression)

def classProgramDerivationServices (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat) :
    ProgramDerivationServices :=
  { deriveProgram := deriveClassProgram config artifactConfig
    surfaceOK := fun unit _ => surfaceCompilationUnitShapeOK unit
    coreFuel := coreFuel }

theorem deriveClassProgram_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {first second : Program × CoreExpr}
    (firstResult : deriveClassProgram config artifactConfig unit identification =
      some first)
    (secondResult : deriveClassProgram config artifactConfig unit identification =
      some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
