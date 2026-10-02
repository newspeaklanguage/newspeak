import Newspeak.Program

namespace Newspeak

/-- All source-derived Program projections in finite, independently
    checkable form.  Installing an image leaves only VM/platform constants and
    host-provided atom mappings from the base Program. -/
structure DerivedProgramImage where
  mixins : FiniteStore MixinId MixinDef
  methodBodies : FiniteStore MethodId (List Statement)
  methodLocals : FiniteStore MethodId (List LocalDeclarationGroup)
  closureParameters : FiniteStore ActivationDeclId (List ParameterId)
  closureLocals : FiniteStore ActivationDeclId (List LocalDeclarationGroup)
  closureBodies : FiniteStore ActivationDeclId (List Statement)
  patternVariables : FiniteStore SiteId CoreExpr
  classBodies : FiniteStore ClassDeclId ClassBodyDescriptor
  mixinApplications : FiniteStore ClassDeclId MixinApplicationDescriptor
  objectLiterals : FiniteStore ObjectLiteralDeclId ObjectLiteralDescriptor
  actorSeeds : FiniteStore MixinId ActorSeedDescriptor
  classOwners : FiniteStore ClassDeclId ClassOwner
  objectLiteralOwners : FiniteStore ObjectLiteralDeclId ClassOwner
  declarationMixins : FiniteStore ClassBodyDecl MixinId
  lexicalParents : FiniteStore ClassDeclId ClassDeclId
  scopeChains : FiniteStore SiteId (List ScopeDecl)
  declaredMembers : FiniteStore (ScopeDecl × Selector) Unit

namespace DerivedProgramImage

def empty : DerivedProgramImage :=
  { mixins := FiniteStore.empty MixinId MixinDef
    methodBodies := FiniteStore.empty MethodId (List Statement)
    methodLocals := FiniteStore.empty MethodId (List LocalDeclarationGroup)
    closureParameters := FiniteStore.empty ActivationDeclId (List ParameterId)
    closureLocals := FiniteStore.empty ActivationDeclId (List LocalDeclarationGroup)
    closureBodies := FiniteStore.empty ActivationDeclId (List Statement)
    patternVariables := FiniteStore.empty SiteId CoreExpr
    classBodies := FiniteStore.empty ClassDeclId ClassBodyDescriptor
    mixinApplications :=
      FiniteStore.empty ClassDeclId MixinApplicationDescriptor
    objectLiterals := FiniteStore.empty ObjectLiteralDeclId ObjectLiteralDescriptor
    actorSeeds := FiniteStore.empty MixinId ActorSeedDescriptor
    classOwners := FiniteStore.empty ClassDeclId ClassOwner
    objectLiteralOwners := FiniteStore.empty ObjectLiteralDeclId ClassOwner
    declarationMixins := FiniteStore.empty ClassBodyDecl MixinId
    lexicalParents := FiniteStore.empty ClassDeclId ClassDeclId
    scopeChains := FiniteStore.empty SiteId (List ScopeDecl)
    declaredMembers := FiniteStore.empty (ScopeDecl × Selector) Unit }

def install (image : DerivedProgramImage) (base : Program) : Program :=
  { base with
    mixins := image.mixins
    methodBodies := image.methodBodies
    methodLocals := fun method => (image.methodLocals method).getD []
    closureParameters := fun declaration =>
      (image.closureParameters declaration).getD []
    closureLocals := fun declaration =>
      (image.closureLocals declaration).getD []
    closureBodies := image.closureBodies
    patternVariable := image.patternVariables
    classBodies := image.classBodies
    mixinApplications := image.mixinApplications
    objectLiterals := image.objectLiterals
    actorSeeds := image.actorSeeds
    classOwner := fun declaration =>
      (image.classOwners declaration).getD .topOwner
    objectLiteralOwner := fun declaration =>
      (image.objectLiteralOwners declaration).getD .topOwner
    declMixin := image.declarationMixins
    lexParent := image.lexicalParents
    scopeChain := fun site => (image.scopeChains site).getD []
    declares := fun scope selector =>
      (image.declaredMembers (scope, selector)).isSome }

def addMixin (image : DerivedProgramImage) (identity : MixinId)
    (definition : MixinDef) : Option DerivedProgramImage := do
  guard ((image.mixins identity).isNone)
  pure { image with mixins := image.mixins.install identity definition }

def addMethod (image : DerivedProgramImage) (mixinIdentity : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) : Option DerivedProgramImage := do
  let mixin ← image.mixins mixinIdentity
  guard ((mixin.methods definition.selector).isNone)
  guard ((image.methodBodies definition.identity).isNone)
  guard ((image.methodLocals definition.identity).isNone)
  guard (decide (definition.owner = mixin.declaration))
  let updatedMixin :=
    { mixin with
      methods := mixin.methods.install definition.selector definition }
  pure { image with
    mixins := image.mixins.install mixinIdentity updatedMixin
    methodBodies := image.methodBodies.install definition.identity body
    methodLocals := image.methodLocals.install definition.identity locals }

def addClosure (image : DerivedProgramImage) (identity : ActivationDeclId)
    (parameters : List ParameterId) (locals : List LocalDeclarationGroup)
    (body : List Statement) : Option DerivedProgramImage := do
  guard ((image.closureBodies identity).isNone)
  pure { image with
    closureParameters := image.closureParameters.install identity parameters
    closureLocals := image.closureLocals.install identity locals
    closureBodies := image.closureBodies.install identity body }

def addDeclaredMember (image : DerivedProgramImage) (scope : ScopeDecl)
    (selector : Selector) : DerivedProgramImage :=
  { image with
    declaredMembers := image.declaredMembers.install (scope, selector) () }

def addClassBody (image : DerivedProgramImage) (descriptor : ClassBodyDescriptor)
    (owner : ClassOwner) : Option DerivedProgramImage := do
  guard ((image.classBodies descriptor.declaration).isNone)
  pure { image with
    classBodies := image.classBodies.install descriptor.declaration descriptor
    classOwners := image.classOwners.install descriptor.declaration owner }

def addMixinApplication (image : DerivedProgramImage)
    (descriptor : MixinApplicationDescriptor) (owner : ClassOwner) :
    Option DerivedProgramImage := do
  guard ((image.mixinApplications descriptor.declaration).isNone)
  pure { image with
    mixinApplications :=
      image.mixinApplications.install descriptor.declaration descriptor
    classOwners := image.classOwners.install descriptor.declaration owner }

def addObjectLiteral (image : DerivedProgramImage)
    (descriptor : ObjectLiteralDescriptor) (owner : ClassOwner) :
    Option DerivedProgramImage := do
  guard ((image.objectLiterals descriptor.declaration).isNone)
  pure { image with
    objectLiterals := image.objectLiterals.install descriptor.declaration descriptor
    objectLiteralOwners :=
      image.objectLiteralOwners.install descriptor.declaration owner }

def addPatternVariable (image : DerivedProgramImage) (site : SiteId)
    (expression : CoreExpr) : Option DerivedProgramImage := do
  guard ((image.patternVariables site).isNone)
  pure { image with
    patternVariables := image.patternVariables.install site expression }

def addNestedDeclaration (image : DerivedProgramImage) (mixin : MixinId)
    (declaration : ClassDeclId) : Option DerivedProgramImage := do
  let definition ← image.mixins mixin
  guard (!(definition.nestedDeclarations.contains declaration))
  pure { image with
    mixins := image.mixins.install mixin
      { definition with
        nestedDeclarations := definition.nestedDeclarations ++ [declaration] } }

def addLexicalParent (image : DerivedProgramImage) (child parent : ClassDeclId) :
    Option DerivedProgramImage := do
  guard ((image.lexicalParents child).isNone)
  pure { image with
    lexicalParents := image.lexicalParents.install child parent }

def replaceClassBodySuperclassMessage (image : DerivedProgramImage)
    (declaration : ClassDeclId) (message : MessageTemplate) :
    Option DerivedProgramImage := do
  let descriptor ← image.classBodies declaration
  pure { image with
    classBodies := image.classBodies.install declaration
      { descriptor with superclassMessage := message } }

@[simp] theorem install_mixins (image : DerivedProgramImage) (base : Program) :
    (image.install base).mixins = image.mixins := by
  rfl

@[simp] theorem install_methodBodies (image : DerivedProgramImage)
    (base : Program) :
    (image.install base).methodBodies = image.methodBodies := by
  rfl

@[simp] theorem install_classBodies (image : DerivedProgramImage)
    (base : Program) :
    (image.install base).classBodies = image.classBodies := by
  rfl

@[simp] theorem install_mixinApplications (image : DerivedProgramImage)
    (base : Program) :
    (image.install base).mixinApplications = image.mixinApplications := by
  rfl

@[simp] theorem install_objectLiterals (image : DerivedProgramImage)
    (base : Program) :
    (image.install base).objectLiterals = image.objectLiterals := by
  rfl

@[simp] theorem install_declMixin (image : DerivedProgramImage)
    (base : Program) :
    (image.install base).declMixin = image.declarationMixins := by
  rfl

@[simp] theorem install_declares (image : DerivedProgramImage) (base : Program)
    (scope : ScopeDecl) (selector : Selector) :
    (image.install base).declares scope selector =
      (image.declaredMembers (scope, selector)).isSome := by
  rfl

end DerivedProgramImage

end Newspeak
