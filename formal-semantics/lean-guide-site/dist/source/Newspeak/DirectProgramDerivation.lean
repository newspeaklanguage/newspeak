import Newspeak.DerivedProgramImage
import Newspeak.IdentificationElaboration
import Newspeak.SynthesizedDeclarations

namespace Newspeak

structure DirectDerivationConfig where
  baseProgram : Program
  isUnarySelector : Selector → Bool
  fuel : Nat

def declarationMixinIdentity (declaration : ClassDeclId)
    (classSide : Bool) : MixinId :=
  ⟨2 * cantorPairNat declaration.index 0 + (if classSide then 1 else 0)⟩

def objectLiteralMixinIdentity (declaration : ObjectLiteralDeclId)
    (classSide : Bool) : MixinId :=
  ⟨2 * cantorPairNat declaration.index 1 + (if classSide then 1 else 0)⟩

def applicationClassMixinIdentity (declaration : ClassDeclId) : MixinId :=
  ⟨2 * cantorPairNat declaration.index 2 + 1⟩

def declarationIdAt (identification : IdentificationOutput)
    (span : SourceSpan) (kind : String) : Option DeclId :=
  findDeclarationIdentity identification.nodes span kind

def formalParameterId (identification : IdentificationOutput) :
    SurfaceDeclaration → Option ParameterId
  | .formal span _ => do
      pure (declarationParameterIdentity
        (← declarationIdAt identification span "formal"))
  | _ => none

def formalParameterIds (identification : IdentificationOutput) :
    List SurfaceDeclaration → Option (List ParameterId)
  | [] => some []
  | formal :: remaining => do
      pure ((← formalParameterId identification formal) ::
        (← formalParameterIds identification remaining))

def surfaceDeclarationName : SurfaceDeclaration → Option String
  | .formal _ name | .slot _ _ name _ _ | .lazySlot _ _ name _ _ => some name
  | .method _ _ selector _ _ _ => some selector.spelling
  | .nestedClass _ _ (.classDeclaration _ name _ _ _) => some name
  | .classDeclaration _ name _ _ _ => some name
  | _ => none

def surfaceGroupDeclarations : SurfaceSlotGroup → List SurfaceDeclaration
  | .sequential _ declarations | .simultaneous _ declarations => declarations

def surfaceGroupsDeclarations (groups : List SurfaceSlotGroup) :
    List SurfaceDeclaration :=
  groups.flatMap surfaceGroupDeclarations

def binderForDeclarations (scope : ScopeDecl)
    (declarations : List SurfaceDeclaration) : FiniteStore String ScopeDecl :=
  declarations.foldl (fun binder declaration =>
    match surfaceDeclarationName declaration with
    | none => binder
    | some name => binder.install name scope)
    (FiniteStore.empty String ScopeDecl)

def topElaborationContext : ElaborationContext :=
  { enclosingClassBody := none
    enclosingActivation := none
    activationKind := .topLevel
    immediateClass := none
    binders := []
    localReturnPermitted := false
    nonlocalReturnPermitted := false }

def directElaborationServices (config : DirectDerivationConfig)
    (identification : IdentificationOutput) : ElaborationServices :=
  elaborationServicesFrom identification config.isUnarySelector
    (fun context =>
      match context.enclosingClassBody with
      | none => .value (.classObject config.baseProgram.object)
      | some _ => .implicitSend ⟨"Object"⟩ [] (context.bind "Object")
          context.immediateClass)
    config.fuel

def localDeclarationId (identification : IdentificationOutput) :
    SurfaceDeclaration → Option (DeclId × String)
  | .slot span _ name _ _ => do
      pure (← declarationIdAt identification span "slot", name)
  | .lazySlot span _ name _ _ => do
      pure (← declarationIdAt identification span "lazySlot", name)
  | _ => none

def elaborateLocalDeclaration (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    SurfaceDeclaration → Option LocalDeclaration
  | declaration@(.slot _ _ _ mutability initializer) => do
      let (identity, _) ← localDeclarationId identification declaration
      let slot := declarationLocalIdentity identity
      match mutability, initializer with
      | .immutable, some expression =>
          pure (.immutable slot
            (← elaborateExpression services context expression))
      | .immutable, none => none
      | .mutable, some expression =>
          pure (.mutableInitialized slot
            (← elaborateExpression services context expression))
      | .mutable, none => pure (.mutableUninitialized slot)
  | declaration@(.lazySlot _ _ _ mutability initializer) => do
      let (identity, _) ← localDeclarationId identification declaration
      let slot := declarationLocalIdentity identity
      let expression ← elaborateExpression services context initializer
      match mutability with
      | .immutable => pure (.lazyImmutable slot expression)
      | .mutable => pure (.lazyMutable slot expression)
  | _ => none

def elaborateLocalDeclarationList (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    List SurfaceDeclaration → Option (List LocalDeclaration)
  | [] => some []
  | declaration :: remaining => do
      pure ((← elaborateLocalDeclaration identification services context declaration) ::
        (← elaborateLocalDeclarationList identification services context remaining))

def elaborateLocalGroups (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    List SurfaceSlotGroup → Option (List LocalDeclarationGroup)
  | [] => some []
  | .sequential _ declarations :: remaining => do
      let locals ←
        elaborateLocalDeclarationList identification services context declarations
      let rest ← elaborateLocalGroups identification services context remaining
      pure (locals.map .sequential ++ rest)
  | .simultaneous _ declarations :: remaining => do
      let locals ←
        elaborateLocalDeclarationList identification services context declarations
      let rest ← elaborateLocalGroups identification services context remaining
      pure (.simultaneous locals :: rest)

def localIdentityList (identification : IdentificationOutput)
    (groups : List SurfaceSlotGroup) : Option (List LocalSlotId) := do
  let pairs ← collect (surfaceGroupsDeclarations groups)
  pure (pairs.map fun pair => declarationLocalIdentity pair.1)
where
  collect : List SurfaceDeclaration → Option (List (DeclId × String))
    | [] => some []
    | declaration :: remaining => do
        pure ((← localDeclarationId identification declaration) ::
          (← collect remaining))

def addActivationMembers (image : DerivedProgramImage)
    (activation : ActivationDeclId) (declarations : List SurfaceDeclaration) :
    DerivedProgramImage :=
  declarations.foldl (fun current declaration =>
    match surfaceDeclarationName declaration with
    | none => current
    | some name => current.addDeclaredMember (.activationDecl activation) ⟨name⟩)
    image

def deriveExplicitMethod (identification : IdentificationOutput)
    (services : ElaborationServices) (classContext : ElaborationContext)
    (owner : ClassBodyDecl) (mixin : MixinId)
    (image : DerivedProgramImage) :
    SurfaceDeclaration → Option DerivedProgramImage
  | .method span access selector formals localGroups body => do
      let declaration ← declarationIdAt identification span "method"
      let method := declarationMethodIdentity declaration
      let activation := declarationActivationIdentity declaration
      let parameters ← formalParameterIds identification formals
      let locals ← localIdentityList identification localGroups
      let directDeclarations := formals ++ surfaceGroupsDeclarations localGroups
      let activationBinder :=
        binderForDeclarations (.activationDecl activation) directDeclarations
      let methodContext : ElaborationContext :=
        { classContext with
          enclosingActivation := some activation
          activationKind := .method
          binders := activationBinder :: classContext.binders
          localReturnPermitted := true
          nonlocalReturnPermitted := false }
      let elaboratedLocals ←
        elaborateLocalGroups identification services methodContext localGroups
      let elaboratedBody ← elaborateStatements services methodContext body
      let definition : MethodDef :=
        { identity := method
          activationDeclaration := activation
          selector := selector
          access := accessOrProtected access
          parameters := parameters
          locals := locals
          owner := owner
          body := ⟨declaration.index⟩ }
      let installed ← image.addMethod mixin definition elaboratedLocals elaboratedBody
      pure (addActivationMembers installed activation directDeclarations)
  | _ => none

def addDerivedMethods (image : DerivedProgramImage) (mixin : MixinId)
    (methods : List DerivedMethod) : Option DerivedProgramImage :=
  methods.foldlM
    (fun current method =>
      current.addMethod mixin method.definition method.locals method.body)
    image

def deriveMemberDeclaration (identification : IdentificationOutput)
    (services : ElaborationServices) (classContext : ElaborationContext)
    (owner : ClassBodyDecl) (mixin : MixinId) :
    DerivedProgramImage → SurfaceDeclaration → Option DerivedProgramImage
  | image, declaration@(.method _ _ _ _ _ _) =>
      deriveExplicitMethod identification services classContext owner mixin image
        declaration
  | image, .slot span access name mutability _ => do
      let declaration ← declarationIdAt identification span "slot"
      addDerivedMethods image mixin
        (ordinarySlotMethods declaration owner name (accessOrProtected access)
          mutability)
  | image, .lazySlot span access name mutability initializer => do
      let declaration ← declarationIdAt identification span "lazySlot"
      let coreInitializer ← elaborateExpression services classContext initializer
      addDerivedMethods image mixin
        (lazySlotMethods declaration owner name (accessOrProtected access)
          mutability coreInitializer)
  | image, .nestedClass _ _ _ => some image
  | _, _ => none

def deriveMemberDeclarations (identification : IdentificationOutput)
    (services : ElaborationServices) (classContext : ElaborationContext)
    (owner : ClassBodyDecl) (mixin : MixinId) :
    DerivedProgramImage → List SurfaceDeclaration → Option DerivedProgramImage
  | image, [] => some image
  | image, declaration :: remaining => do
      let next ← deriveMemberDeclaration identification services classContext owner
        mixin image declaration
      deriveMemberDeclarations identification services classContext owner mixin
        next remaining

def physicalSlotIds (identification : IdentificationOutput) :
    List SurfaceDeclaration → Option (List SlotId)
  | [] => some []
  | .slot span _ _ _ _ :: remaining => do
      let declaration ← declarationIdAt identification span "slot"
      pure (declarationSlotIdentity declaration ::
        (← physicalSlotIds identification remaining))
  | .lazySlot span _ _ _ _ :: remaining => do
      let declaration ← declarationIdAt identification span "lazySlot"
      pure (declarationSlotIdentity declaration ::
        (← physicalSlotIds identification remaining))
  | _ :: remaining => physicalSlotIds identification remaining

def elaborateEagerSlotDeclaration (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    SurfaceDeclaration → Option (Option SlotDeclaration)
  | .slot span _ _ mutability initializer => do
      let declaration ← declarationIdAt identification span "slot"
      let slot := declarationSlotIdentity declaration
      let thunk := synthesizedActivationIdentity declaration 2
      match mutability, initializer with
      | .immutable, some expression =>
          pure (some (.immutable slot
            (← elaborateExpression services context expression) thunk))
      | .immutable, none => none
      | .mutable, some expression =>
          pure (some (.mutableInitialized slot
            (← elaborateExpression services context expression) thunk))
      | .mutable, none => pure (some (.mutableUninitialized slot))
  | .lazySlot _ _ _ _ _ => some none
  | _ => none

def elaborateEagerSlotDeclarations (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    List SurfaceDeclaration → Option (List SlotDeclaration)
  | [] => some []
  | declaration :: remaining => do
      let current ← elaborateEagerSlotDeclaration identification services context
        declaration
      let rest ← elaborateEagerSlotDeclarations identification services context
        remaining
      pure (current.toList ++ rest)

def elaborateInitializerGroup (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    SurfaceSlotGroup → Option SlotDeclarationGroup
  | .sequential _ declarations => do
      pure (.sequential
        (← elaborateEagerSlotDeclarations identification services context
          declarations))
  | .simultaneous _ declarations => do
      pure (.simultaneous
        (← elaborateEagerSlotDeclarations identification services context
          declarations))

def elaborateInitializerGroups (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext) :
    Option SurfaceSlotGroup → Option (List SlotDeclarationGroup)
  | none => some []
  | some group => do pure [← elaborateInitializerGroup identification services context group]

def emptyMixinDefinition (declaration : ClassBodyDecl)
    (initializer : ActivationDeclId) (selector : Selector)
    (parameters : List ParameterId) (ownSlots : List SlotId)
    (initializerGroups : List SlotDeclarationGroup)
    (initializerBody : List Statement) : MixinDef :=
  { declaration := declaration
    methods := FiniteStore.empty Selector MethodDef
    ownSlots := ownSlots
    nestedDeclarations := []
    initializerDeclaration := initializer
    initializerSelector := selector
    initializerParameters := parameters
    initializerGroups := initializerGroups
    initializerBody := initializerBody }

def directClassStructure : SurfaceInheritance → Option SurfaceClassStructure
  | .defaultInheritance _ classStructure => some classStructure
  | .explicitInheritance _ _ _ classStructure => some classStructure
  | .mixinChain _ _ _ _ _ => none

def directSuperclassSyntax : SurfaceInheritance → SuperclassSyntax
  | .defaultInheritance _ _ => .implicitSuperclass
  | _ => .explicitSuperclass

def directSuperclassMessage (services : ElaborationServices)
    (context : ElaborationContext) : SurfaceInheritance → Option MessageTemplate
  | .defaultInheritance _ _ => some ⟨⟨"new"⟩, []⟩
  | .explicitInheritance _ _ initializer _
  | .mixinChain _ _ initializer _ _ => do
      pure ⟨initializer.selector,
        (← elaborateExpressionList services context initializer.arguments)⟩

def directSuperclassExpression (services : ElaborationServices)
    (context : ElaborationContext) : SurfaceInheritance → Option CoreExpr
  | .defaultInheritance _ _ => some (services.defaultSuperclass context)
  | .explicitInheritance _ receiver _ _
  | .mixinChain _ receiver _ _ _ =>
      elaborateExpression services context receiver

def deriveDirectClass (config : DirectDerivationConfig)
    (identification : IdentificationOutput)
    (unit : SurfaceCompilationUnit) : Option (DerivedProgramImage × CoreExpr) := do
  let (.classDeclaration span _name factorySelector factoryFormals inheritance) :=
    unit.declaration | none
  let classDeclIdentity ← declarationIdAt identification span "classDeclaration"
  let classIdentity : ClassDeclId := ⟨classDeclIdentity.index⟩
  let classStructure ← directClassStructure inheritance
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
  let initializerGroups ← elaborateInitializerGroups identification services
    initializerContext headerLocals
  let initializerBody ←
    elaborateStatements services initializerContext headerStatements
  let instanceSlots ← physicalSlotIds identification headerDeclarations
  let instanceDefinition := emptyMixinDefinition owner initializer factorySelector
    factoryParameters instanceSlots initializerGroups initializerBody
  let classInitializer := synthesizedActivationIdentity classDeclIdentity 3
  let classDefinition := emptyMixinDefinition owner classInitializer ⟨"new"⟩ [] [] [] []
  let image₁ ← DerivedProgramImage.empty.addMixin instanceMixin instanceDefinition
  let image₂ ← image₁.addMixin classMixin classDefinition
  let image₂ ← addDerivedMethods image₂ classMixin
    [primaryFactoryMethod classDeclIdentity owner factorySelector factoryParameters]
  let image₃ :=
    { image₂ with
      declarationMixins := image₂.declarationMixins.install owner instanceMixin }
  let image₃ := addActivationMembers image₃ initializer factoryFormals
  let image₄ ← deriveMemberDeclarations identification services initializerContext
    owner instanceMixin image₃ headerDeclarations
  let image₄ ← deriveMemberDeclarations identification services classContext owner
    instanceMixin image₄ instanceDeclarations
  let image₅ ← deriveMemberDeclarations identification services classContext owner
    classMixin image₄ classDeclarations
  let superclassMessage ←
    directSuperclassMessage services initializerContext inheritance
  let descriptor : ClassBodyDescriptor :=
    { declaration := classIdentity
      superclassSyntax := directSuperclassSyntax inheritance
      factorySelector := factorySelector
      factoryParameters := factoryParameters
      instanceMixin := instanceMixin
      classMixin := classMixin
      initializerDeclaration := initializer
      superclassMessage := superclassMessage }
  let image₆ ← image₅.addClassBody descriptor .topOwner
  let superclass ← directSuperclassExpression services topElaborationContext inheritance
  pure (image₆, .classBody classIdentity superclass)

def deriveDirectProgram (config : DirectDerivationConfig)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) :
    Option (Program × CoreExpr) := do
  let (image, expression) ← deriveDirectClass config identification unit
  pure (image.install config.baseProgram, expression)

theorem deriveDirectProgram_deterministic
    {config : DirectDerivationConfig} {unit : SurfaceCompilationUnit}
    {identification : IdentificationOutput} {first second : Program × CoreExpr}
    (firstResult : deriveDirectProgram config unit identification = some first)
    (secondResult : deriveDirectProgram config unit identification = some second) :
    first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
