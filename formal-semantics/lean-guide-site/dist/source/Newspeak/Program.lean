import Newspeak.Syntax
import Newspeak.FiniteStore

namespace Newspeak

/-- Static mixin data.  Its method dictionary has an exact executable domain
    for reflection and artifact validation. -/
structure MixinDef where
  declaration : ClassBodyDecl
  methods : FiniteStore Selector MethodDef
  ownSlots : List SlotId
  /-- Stable identities of the mixin's directly declared nested classes.
      Their run-time class objects remain lazily memoized per enclosing
      object; reflection uses this list to discard obsolete cache entries. -/
  nestedDeclarations : List ClassDeclId
  initializerDeclaration : ActivationDeclId
  initializerSelector : Selector
  initializerParameters : List ParameterId
  initializerGroups : List SlotDeclarationGroup
  initializerBody : List Statement

theorem MixinDef.method_at_selector_unique {mixin : MixinDef}
    {selector : Selector} {first second : MethodDef}
    (firstFound : mixin.methods selector = some first)
    (secondFound : mixin.methods selector = some second) : first = second := by
  rw [firstFound] at secondFound
  exact Option.some.inj secondFound

structure Program where
  top : ClassId
  object : ClassId
  classClass : ClassId
  metaclassClass : ClassId
  messageMirrorClass : ClassId
  activationClass : ClassId
  closureClass : ClassId
  nilObject : ObjRef
  mixins : FiniteStore MixinId MixinDef
  methodBodies : FiniteStore MethodId (List Statement)
  methodLocals : MethodId → List LocalDeclarationGroup
  closureParameters : ActivationDeclId → List ParameterId
  closureLocals : ActivationDeclId → List LocalDeclarationGroup
  closureBodies : FiniteStore ActivationDeclId (List Statement)
  pastFutureExpression : ActivationId → CoreExpr
  atoms : AtomPayload → ObjRef
  platform : FiniteStore PlatformName ObjRef
  patternVariable : FiniteStore SiteId CoreExpr
  classBodies : FiniteStore ClassDeclId ClassBodyDescriptor
  mixinApplications : FiniteStore ClassDeclId MixinApplicationDescriptor
  objectLiterals : FiniteStore ObjectLiteralDeclId ObjectLiteralDescriptor
  actorSeeds : FiniteStore MixinId ActorSeedDescriptor
  classOwner : ClassDeclId → ClassOwner
  objectLiteralOwner : ObjectLiteralDeclId → ClassOwner
  declMixin : FiniteStore ClassBodyDecl MixinId
  lexParent : FiniteStore ClassDeclId ClassDeclId
  scopeChain : SiteId → List ScopeDecl
  declares : ScopeDecl → Selector → Bool

namespace Program

/-- Programs are lookup-equivalent when every semantic projection agrees.
    Finite-store domain order is excluded: it is an implementation detail and
    can differ after commuting independent fresh reflective additions. -/
structure LookupEquivalent (left right : Program) : Prop where
  top : left.top = right.top
  object : left.object = right.object
  classClass : left.classClass = right.classClass
  metaclassClass : left.metaclassClass = right.metaclassClass
  messageMirrorClass : left.messageMirrorClass = right.messageMirrorClass
  activationClass : left.activationClass = right.activationClass
  closureClass : left.closureClass = right.closureClass
  nilObject : left.nilObject = right.nilObject
  mixins : left.mixins.LookupEquivalent right.mixins
  methodBodies : left.methodBodies.LookupEquivalent right.methodBodies
  methodLocals : ∀ method, left.methodLocals method = right.methodLocals method
  closureParameters : ∀ declaration,
    left.closureParameters declaration = right.closureParameters declaration
  closureLocals : ∀ declaration,
    left.closureLocals declaration = right.closureLocals declaration
  closureBodies : left.closureBodies.LookupEquivalent right.closureBodies
  pastFutureExpression : ∀ activation,
    left.pastFutureExpression activation = right.pastFutureExpression activation
  atoms : ∀ payload, left.atoms payload = right.atoms payload
  platform : left.platform.LookupEquivalent right.platform
  patternVariable : left.patternVariable.LookupEquivalent right.patternVariable
  classBodies : left.classBodies.LookupEquivalent right.classBodies
  mixinApplications :
    left.mixinApplications.LookupEquivalent right.mixinApplications
  objectLiterals : left.objectLiterals.LookupEquivalent right.objectLiterals
  actorSeeds : left.actorSeeds.LookupEquivalent right.actorSeeds
  classOwner : ∀ declaration,
    left.classOwner declaration = right.classOwner declaration
  objectLiteralOwner : ∀ declaration,
    left.objectLiteralOwner declaration = right.objectLiteralOwner declaration
  declMixin : left.declMixin.LookupEquivalent right.declMixin
  lexParent : left.lexParent.LookupEquivalent right.lexParent
  scopeChain : ∀ site, left.scopeChain site = right.scopeChain site
  declares : ∀ scope selector,
    left.declares scope selector = right.declares scope selector

theorem LookupEquivalent.refl (program : Program) :
    program.LookupEquivalent program :=
  { top := rfl
    object := rfl
    classClass := rfl
    metaclassClass := rfl
    messageMirrorClass := rfl
    activationClass := rfl
    closureClass := rfl
    nilObject := rfl
    mixins := FiniteStore.LookupEquivalent.refl program.mixins
    methodBodies := FiniteStore.LookupEquivalent.refl program.methodBodies
    methodLocals := fun _ => rfl
    closureParameters := fun _ => rfl
    closureLocals := fun _ => rfl
    closureBodies := FiniteStore.LookupEquivalent.refl program.closureBodies
    pastFutureExpression := fun _ => rfl
    atoms := fun _ => rfl
    platform := FiniteStore.LookupEquivalent.refl program.platform
    patternVariable := FiniteStore.LookupEquivalent.refl program.patternVariable
    classBodies := FiniteStore.LookupEquivalent.refl program.classBodies
    mixinApplications :=
      FiniteStore.LookupEquivalent.refl program.mixinApplications
    objectLiterals := FiniteStore.LookupEquivalent.refl program.objectLiterals
    actorSeeds := FiniteStore.LookupEquivalent.refl program.actorSeeds
    classOwner := fun _ => rfl
    objectLiteralOwner := fun _ => rfl
    declMixin := FiniteStore.LookupEquivalent.refl program.declMixin
    lexParent := FiniteStore.LookupEquivalent.refl program.lexParent
    scopeChain := fun _ => rfl
    declares := fun _ _ => rfl }

theorem LookupEquivalent.symm {left right : Program}
    (equivalent : left.LookupEquivalent right) :
    right.LookupEquivalent left :=
  { top := equivalent.top.symm
    object := equivalent.object.symm
    classClass := equivalent.classClass.symm
    metaclassClass := equivalent.metaclassClass.symm
    messageMirrorClass := equivalent.messageMirrorClass.symm
    activationClass := equivalent.activationClass.symm
    closureClass := equivalent.closureClass.symm
    nilObject := equivalent.nilObject.symm
    mixins := equivalent.mixins.symm
    methodBodies := equivalent.methodBodies.symm
    methodLocals := fun method => (equivalent.methodLocals method).symm
    closureParameters := fun declaration =>
      (equivalent.closureParameters declaration).symm
    closureLocals := fun declaration =>
      (equivalent.closureLocals declaration).symm
    closureBodies := equivalent.closureBodies.symm
    pastFutureExpression := fun activation =>
      (equivalent.pastFutureExpression activation).symm
    atoms := fun payload => (equivalent.atoms payload).symm
    platform := equivalent.platform.symm
    patternVariable := equivalent.patternVariable.symm
    classBodies := equivalent.classBodies.symm
    mixinApplications := equivalent.mixinApplications.symm
    objectLiterals := equivalent.objectLiterals.symm
    actorSeeds := equivalent.actorSeeds.symm
    classOwner := fun declaration => (equivalent.classOwner declaration).symm
    objectLiteralOwner := fun declaration =>
      (equivalent.objectLiteralOwner declaration).symm
    declMixin := equivalent.declMixin.symm
    lexParent := equivalent.lexParent.symm
    scopeChain := fun site => (equivalent.scopeChain site).symm
    declares := fun scope selector => (equivalent.declares scope selector).symm }

theorem LookupEquivalent.trans {first second third : Program}
    (left : first.LookupEquivalent second)
    (right : second.LookupEquivalent third) :
    first.LookupEquivalent third :=
  { top := left.top.trans right.top
    object := left.object.trans right.object
    classClass := left.classClass.trans right.classClass
    metaclassClass := left.metaclassClass.trans right.metaclassClass
    messageMirrorClass :=
      left.messageMirrorClass.trans right.messageMirrorClass
    activationClass := left.activationClass.trans right.activationClass
    closureClass := left.closureClass.trans right.closureClass
    nilObject := left.nilObject.trans right.nilObject
    mixins := left.mixins.trans right.mixins
    methodBodies := left.methodBodies.trans right.methodBodies
    methodLocals := fun method =>
      (left.methodLocals method).trans (right.methodLocals method)
    closureParameters := fun declaration =>
      (left.closureParameters declaration).trans
        (right.closureParameters declaration)
    closureLocals := fun declaration =>
      (left.closureLocals declaration).trans (right.closureLocals declaration)
    closureBodies := left.closureBodies.trans right.closureBodies
    pastFutureExpression := fun activation =>
      (left.pastFutureExpression activation).trans
        (right.pastFutureExpression activation)
    atoms := fun payload => (left.atoms payload).trans (right.atoms payload)
    platform := left.platform.trans right.platform
    patternVariable := left.patternVariable.trans right.patternVariable
    classBodies := left.classBodies.trans right.classBodies
    mixinApplications := left.mixinApplications.trans right.mixinApplications
    objectLiterals := left.objectLiterals.trans right.objectLiterals
    actorSeeds := left.actorSeeds.trans right.actorSeeds
    classOwner := fun declaration =>
      (left.classOwner declaration).trans (right.classOwner declaration)
    objectLiteralOwner := fun declaration =>
      (left.objectLiteralOwner declaration).trans
        (right.objectLiteralOwner declaration)
    declMixin := left.declMixin.trans right.declMixin
    lexParent := left.lexParent.trans right.lexParent
    scopeChain := fun site =>
      (left.scopeChain site).trans (right.scopeChain site)
    declares := fun scope selector =>
      (left.declares scope selector).trans (right.declares scope selector) }

end Program
end Newspeak
