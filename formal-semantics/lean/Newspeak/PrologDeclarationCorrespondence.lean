import Newspeak.DirectProgramDerivation
import Newspeak.PrologIdentificationCorrespondence

/-!
# Structural correspondence for statements and local declarations

This layer expands the first declaration-level elaboration equations rather
than treating them as one opaque function graph.  It covers statements,
ordinary and lazy local declarations, declaration lists, and sequential or
simultaneous local groups.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologElaborateStatement (services : ElaborationServices)
    (context : ElaborationContext) : SurfaceStatement → Statement → Prop where
  | expression {span surface core} :
      PrologElaborateExpression services context surface core →
      PrologElaborateStatement services context
        (.expression span surface) (.expression core)
  | returnStatement {span surface core} :
      (context.localReturnPermitted || context.nonlocalReturnPermitted) = true →
      PrologElaborateExpression services context surface core →
      PrologElaborateStatement services context
        (.returnStatement span surface) (.return core)

theorem PrologElaborateStatement.sound
    {services context surface core}
    (derivation : PrologElaborateStatement services context surface core) :
    elaborateStatement services context surface = some core := by
  cases derivation with
  | expression expression =>
      simp [elaborateStatement, prologElaborateExpression_iff.mp expression]
  | returnStatement allowed expression =>
      simp [elaborateStatement, allowed,
        prologElaborateExpression_iff.mp expression]

theorem prologElaborateStatement_complete
    {services context surface core}
    (success : elaborateStatement services context surface = some core) :
    PrologElaborateStatement services context surface core := by
  cases surface with
  | expression span expression =>
      simp [elaborateStatement] at success
      cases expressionResult : elaborateExpression services context expression with
      | none => simp [expressionResult] at success
      | some value =>
          simp [expressionResult] at success
          cases success
          exact .expression (prologElaborateExpression_iff.mpr expressionResult)
  | returnStatement span expression =>
      cases allowed : context.localReturnPermitted ||
          context.nonlocalReturnPermitted with
      | false => simp [elaborateStatement, allowed] at success
      | true =>
          cases expressionResult : elaborateExpression services context expression with
          | none => simp [elaborateStatement, allowed, expressionResult] at success
          | some value =>
              simp [elaborateStatement, allowed, expressionResult] at success
              cases success
              exact .returnStatement allowed
                (prologElaborateExpression_iff.mpr expressionResult)

theorem prologElaborateStatement_iff {services context surface core} :
    PrologElaborateStatement services context surface core ↔
      elaborateStatement services context surface = some core := by
  constructor
  · exact PrologElaborateStatement.sound
  · exact prologElaborateStatement_complete

inductive PrologElaborateStatements (services : ElaborationServices)
    (context : ElaborationContext) :
    List SurfaceStatement → List Statement → Prop where
  | nil : PrologElaborateStatements services context [] []
  | cons {surface remaining core rest} :
      PrologElaborateStatement services context surface core →
      PrologElaborateStatements services context remaining rest →
      PrologElaborateStatements services context
        (surface :: remaining) (core :: rest)

theorem PrologElaborateStatements.sound
    {services context surface core}
    (derivation : PrologElaborateStatements services context surface core) :
    elaborateStatements services context surface = some core := by
  induction derivation with
  | nil => rfl
  | cons first remaining ih =>
      simp [elaborateStatements, first.sound, ih]

theorem prologElaborateStatements_complete
    (services : ElaborationServices) (context : ElaborationContext) :
    ∀ surface core,
      elaborateStatements services context surface = some core →
      PrologElaborateStatements services context surface core := by
  intro surface
  induction surface with
  | nil =>
      intro core success
      simp [elaborateStatements] at success
      cases success
      exact .nil
  | cons first remaining ih =>
      intro core success
      cases firstResult : elaborateStatement services context first with
      | none => simp [elaborateStatements, firstResult] at success
      | some firstCore =>
          cases restResult : elaborateStatements services context remaining with
          | none => simp [elaborateStatements, firstResult, restResult] at success
          | some rest =>
              simp [elaborateStatements, firstResult, restResult] at success
              cases success
              exact .cons (prologElaborateStatement_complete firstResult)
                (ih rest restResult)

theorem prologElaborateStatements_iff {services context surface core} :
    PrologElaborateStatements services context surface core ↔
      elaborateStatements services context surface = some core := by
  constructor
  · exact PrologElaborateStatements.sound
  · exact prologElaborateStatements_complete services context surface core

inductive PrologLocalDeclarationId (identification : IdentificationOutput) :
    SurfaceDeclaration → DeclId → String → Prop where
  | slot {span access name mutability initializer identity} :
      declarationIdAt identification span "slot" = some identity →
      PrologLocalDeclarationId identification
        (.slot span access name mutability initializer) identity name
  | lazySlot {span access name mutability initializer identity} :
      declarationIdAt identification span "lazySlot" = some identity →
      PrologLocalDeclarationId identification
        (.lazySlot span access name mutability initializer) identity name

theorem prologLocalDeclarationId_iff
    {identification declaration identity name} :
    PrologLocalDeclarationId identification declaration identity name ↔
      localDeclarationId identification declaration = some (identity, name) := by
  constructor
  · intro derivation
    cases derivation with
    | slot found => simp [localDeclarationId, found]
    | lazySlot found => simp [localDeclarationId, found]
  · intro success
    cases declaration with
    | slot span access actualName mutability initializer =>
        simp [localDeclarationId] at success
        cases found : declarationIdAt identification span "slot" with
        | none => simp [found] at success
        | some actualIdentity =>
            simp [found] at success
            rcases success with ⟨rfl, rfl⟩
            exact .slot found
    | lazySlot span access actualName mutability initializer =>
        simp [localDeclarationId] at success
        cases found : declarationIdAt identification span "lazySlot" with
        | none => simp [found] at success
        | some actualIdentity =>
            simp [found] at success
            rcases success with ⟨rfl, rfl⟩
            exact .lazySlot found
    | formal span actualName => simp [localDeclarationId] at success
    | method span access selector formals locals body =>
        simp [localDeclarationId] at success
    | nestedClass span access nested => simp [localDeclarationId] at success
    | classDeclaration span actualName selector formals inheritance =>
        simp [localDeclarationId] at success

inductive PrologElaborateLocalDeclaration
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) :
    SurfaceDeclaration → LocalDeclaration → Prop where
  | immutableInitialized {span access name expression identity core} :
      PrologLocalDeclarationId identification
        (.slot span access name .immutable (some expression)) identity name →
      PrologElaborateExpression services context expression core →
      PrologElaborateLocalDeclaration identification services context
        (.slot span access name .immutable (some expression))
        (.immutable (declarationLocalIdentity identity) core)
  | mutableInitialized {span access name expression identity core} :
      PrologLocalDeclarationId identification
        (.slot span access name .mutable (some expression)) identity name →
      PrologElaborateExpression services context expression core →
      PrologElaborateLocalDeclaration identification services context
        (.slot span access name .mutable (some expression))
        (.mutableInitialized (declarationLocalIdentity identity) core)
  | mutableUninitialized {span access name identity} :
      PrologLocalDeclarationId identification
        (.slot span access name .mutable none) identity name →
      PrologElaborateLocalDeclaration identification services context
        (.slot span access name .mutable none)
        (.mutableUninitialized (declarationLocalIdentity identity))
  | lazyImmutable {span access name expression identity core} :
      PrologLocalDeclarationId identification
        (.lazySlot span access name .immutable expression) identity name →
      PrologElaborateExpression services context expression core →
      PrologElaborateLocalDeclaration identification services context
        (.lazySlot span access name .immutable expression)
        (.lazyImmutable (declarationLocalIdentity identity) core)
  | lazyMutable {span access name expression identity core} :
      PrologLocalDeclarationId identification
        (.lazySlot span access name .mutable expression) identity name →
      PrologElaborateExpression services context expression core →
      PrologElaborateLocalDeclaration identification services context
        (.lazySlot span access name .mutable expression)
        (.lazyMutable (declarationLocalIdentity identity) core)

theorem PrologElaborateLocalDeclaration.sound
    {identification services context declaration core}
    (derivation : PrologElaborateLocalDeclaration identification services
      context declaration core) :
    elaborateLocalDeclaration identification services context declaration =
      some core := by
  cases derivation with
  | immutableInitialized identity expression =>
      simp [elaborateLocalDeclaration,
        prologLocalDeclarationId_iff.mp identity,
        prologElaborateExpression_iff.mp expression]
  | mutableInitialized identity expression =>
      simp [elaborateLocalDeclaration,
        prologLocalDeclarationId_iff.mp identity,
        prologElaborateExpression_iff.mp expression]
  | mutableUninitialized identity =>
      simp [elaborateLocalDeclaration, prologLocalDeclarationId_iff.mp identity]
  | lazyImmutable identity expression =>
      simp [elaborateLocalDeclaration,
        prologLocalDeclarationId_iff.mp identity,
        prologElaborateExpression_iff.mp expression]
  | lazyMutable identity expression =>
      simp [elaborateLocalDeclaration,
        prologLocalDeclarationId_iff.mp identity,
        prologElaborateExpression_iff.mp expression]

theorem prologElaborateLocalDeclaration_complete
    {identification services context declaration core}
    (success : elaborateLocalDeclaration identification services context
      declaration = some core) :
    PrologElaborateLocalDeclaration identification services context
      declaration core := by
  cases declaration with
  | formal span name => simp [elaborateLocalDeclaration] at success
  | method span access selector formals locals body =>
      simp [elaborateLocalDeclaration] at success
  | nestedClass span access nested => simp [elaborateLocalDeclaration] at success
  | classDeclaration span name selector formals inheritance =>
      simp [elaborateLocalDeclaration] at success
  | slot span access name mutability initializer =>
      cases found : declarationIdAt identification span "slot" with
      | none => simp [elaborateLocalDeclaration, localDeclarationId, found] at success
      | some identity =>
          have localIdResult : localDeclarationId identification
              (.slot span access name mutability initializer) =
              some (identity, name) := by
            simp [localDeclarationId, found]
          cases mutability with
          | immutable =>
              cases initializer with
              | none =>
                  simp [elaborateLocalDeclaration, localIdResult] at success
              | some expression =>
                  cases expressionResult : elaborateExpression services context
                      expression with
                  | none =>
                      simp [elaborateLocalDeclaration, localIdResult,
                        expressionResult]
                        at success
                  | some value =>
                      simp [elaborateLocalDeclaration, localIdResult,
                        expressionResult]
                        at success
                      cases success
                      exact .immutableInitialized
                        (prologLocalDeclarationId_iff.mpr localIdResult)
                        (prologElaborateExpression_iff.mpr expressionResult)
          | mutable =>
              cases initializer with
              | none =>
                  simp [elaborateLocalDeclaration, localIdResult] at success
                  cases success
                  exact .mutableUninitialized
                    (prologLocalDeclarationId_iff.mpr localIdResult)
              | some expression =>
                  cases expressionResult : elaborateExpression services context
                      expression with
                  | none =>
                      simp [elaborateLocalDeclaration, localIdResult,
                        expressionResult]
                        at success
                  | some value =>
                      simp [elaborateLocalDeclaration, localIdResult,
                        expressionResult]
                        at success
                      cases success
                      exact .mutableInitialized
                        (prologLocalDeclarationId_iff.mpr localIdResult)
                        (prologElaborateExpression_iff.mpr expressionResult)
  | lazySlot span access name mutability expression =>
      cases found : declarationIdAt identification span "lazySlot" with
      | none => simp [elaborateLocalDeclaration, localDeclarationId, found] at success
      | some identity =>
          have localIdResult : localDeclarationId identification
              (.lazySlot span access name mutability expression) =
              some (identity, name) := by
            simp [localDeclarationId, found]
          cases expressionResult : elaborateExpression services context expression with
          | none =>
              simp [elaborateLocalDeclaration, localIdResult, expressionResult]
                at success
          | some value =>
              cases mutability with
              | immutable =>
                  simp [elaborateLocalDeclaration, localIdResult,
                    expressionResult] at success
                  cases success
                  exact .lazyImmutable
                    (prologLocalDeclarationId_iff.mpr localIdResult)
                    (prologElaborateExpression_iff.mpr expressionResult)
              | mutable =>
                  simp [elaborateLocalDeclaration, localIdResult,
                    expressionResult] at success
                  cases success
                  exact .lazyMutable
                    (prologLocalDeclarationId_iff.mpr localIdResult)
                    (prologElaborateExpression_iff.mpr expressionResult)

theorem prologElaborateLocalDeclaration_iff
    {identification services context declaration core} :
    PrologElaborateLocalDeclaration identification services context
      declaration core ↔
      elaborateLocalDeclaration identification services context declaration =
        some core := by
  constructor
  · exact PrologElaborateLocalDeclaration.sound
  · exact prologElaborateLocalDeclaration_complete

inductive PrologElaborateLocalDeclarationList
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) :
    List SurfaceDeclaration → List LocalDeclaration → Prop where
  | nil : PrologElaborateLocalDeclarationList identification services context [] []
  | cons {declaration remaining localDeclaration rest} :
      PrologElaborateLocalDeclaration identification services context
        declaration localDeclaration →
      PrologElaborateLocalDeclarationList identification services context
        remaining rest →
      PrologElaborateLocalDeclarationList identification services context
        (declaration :: remaining) (localDeclaration :: rest)

theorem PrologElaborateLocalDeclarationList.sound
    {identification services context declarations locals}
    (derivation : PrologElaborateLocalDeclarationList identification services
      context declarations locals) :
    elaborateLocalDeclarationList identification services context declarations =
      some locals := by
  induction derivation with
  | nil => rfl
  | cons first remaining ih =>
      simp [elaborateLocalDeclarationList, first.sound, ih]

theorem prologElaborateLocalDeclarationList_complete
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) :
    ∀ declarations locals,
      elaborateLocalDeclarationList identification services context
        declarations = some locals →
      PrologElaborateLocalDeclarationList identification services context
        declarations locals := by
  intro declarations
  induction declarations with
  | nil =>
      intro locals success
      simp [elaborateLocalDeclarationList] at success
      cases success
      exact .nil
  | cons declaration remaining ih =>
      intro locals success
      cases firstResult : elaborateLocalDeclaration identification services
          context declaration with
      | none => simp [elaborateLocalDeclarationList, firstResult] at success
      | some localDeclaration =>
          cases restResult : elaborateLocalDeclarationList identification services
              context remaining with
          | none =>
              simp [elaborateLocalDeclarationList, firstResult, restResult] at success
          | some rest =>
              simp [elaborateLocalDeclarationList, firstResult, restResult] at success
              cases success
              exact .cons
                (prologElaborateLocalDeclaration_complete firstResult)
                (ih rest restResult)

theorem prologElaborateLocalDeclarationList_iff
    {identification services context declarations locals} :
    PrologElaborateLocalDeclarationList identification services context
      declarations locals ↔
      elaborateLocalDeclarationList identification services context declarations =
        some locals := by
  constructor
  · exact PrologElaborateLocalDeclarationList.sound
  · exact prologElaborateLocalDeclarationList_complete identification services
      context declarations locals

inductive PrologElaborateLocalGroups
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) :
    List SurfaceSlotGroup → List LocalDeclarationGroup → Prop where
  | nil : PrologElaborateLocalGroups identification services context [] []
  | sequential {span declarations remaining locals rest} :
      PrologElaborateLocalDeclarationList identification services context
        declarations locals →
      PrologElaborateLocalGroups identification services context remaining rest →
      PrologElaborateLocalGroups identification services context
        (.sequential span declarations :: remaining)
        (locals.map LocalDeclarationGroup.sequential ++ rest)
  | simultaneous {span declarations remaining locals rest} :
      PrologElaborateLocalDeclarationList identification services context
        declarations locals →
      PrologElaborateLocalGroups identification services context remaining rest →
      PrologElaborateLocalGroups identification services context
        (.simultaneous span declarations :: remaining)
        (.simultaneous locals :: rest)

theorem PrologElaborateLocalGroups.sound
    {identification services context groups locals}
    (derivation : PrologElaborateLocalGroups identification services context
      groups locals) :
    elaborateLocalGroups identification services context groups = some locals := by
  induction derivation with
  | nil => rfl
  | sequential current remaining ih =>
      simp [elaborateLocalGroups, current.sound, ih]
  | simultaneous current remaining ih =>
      simp [elaborateLocalGroups, current.sound, ih]

theorem prologElaborateLocalGroups_complete
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) :
    ∀ groups locals,
      elaborateLocalGroups identification services context groups = some locals →
      PrologElaborateLocalGroups identification services context groups locals := by
  intro groups
  induction groups with
  | nil =>
      intro locals success
      simp [elaborateLocalGroups] at success
      cases success
      exact .nil
  | cons group remaining ih =>
      intro output success
      cases group with
      | sequential span declarations =>
          cases currentResult : elaborateLocalDeclarationList identification services
              context declarations with
          | none => simp [elaborateLocalGroups, currentResult] at success
          | some locals =>
              cases restResult : elaborateLocalGroups identification services context
                  remaining with
              | none => simp [elaborateLocalGroups, currentResult, restResult] at success
              | some rest =>
                  simp [elaborateLocalGroups, currentResult, restResult] at success
                  cases success
                  exact .sequential
                    (prologElaborateLocalDeclarationList_complete identification
                      services context declarations locals currentResult)
                    (ih rest restResult)
      | simultaneous span declarations =>
          cases currentResult : elaborateLocalDeclarationList identification services
              context declarations with
          | none => simp [elaborateLocalGroups, currentResult] at success
          | some locals =>
              cases restResult : elaborateLocalGroups identification services context
                  remaining with
              | none => simp [elaborateLocalGroups, currentResult, restResult] at success
              | some rest =>
                  simp [elaborateLocalGroups, currentResult, restResult] at success
                  cases success
                  exact .simultaneous
                    (prologElaborateLocalDeclarationList_complete identification
                      services context declarations locals currentResult)
                    (ih rest restResult)

theorem prologElaborateLocalGroups_iff
    {identification services context groups locals} :
    PrologElaborateLocalGroups identification services context groups locals ↔
      elaborateLocalGroups identification services context groups = some locals := by
  constructor
  · exact PrologElaborateLocalGroups.sound
  · exact prologElaborateLocalGroups_complete identification services context
      groups locals

inductive PrologFormalParameterId (identification : IdentificationOutput)
    (declaration : SurfaceDeclaration) : ParameterId → Prop where
  | result {parameter : ParameterId} :
      formalParameterId identification declaration = some parameter →
      PrologFormalParameterId identification declaration parameter

theorem prologFormalParameterId_iff {identification declaration parameter} :
    PrologFormalParameterId identification declaration parameter ↔
      formalParameterId identification declaration = some parameter := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologFormalParameterIds (identification : IdentificationOutput)
    (declarations : List SurfaceDeclaration) : List ParameterId → Prop where
  | result {parameters : List ParameterId} :
      formalParameterIds identification declarations = some parameters →
      PrologFormalParameterIds identification declarations parameters

theorem prologFormalParameterIds_iff {identification declarations parameters} :
    PrologFormalParameterIds identification declarations parameters ↔
      formalParameterIds identification declarations = some parameters := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologPhysicalSlotIds (identification : IdentificationOutput)
    (declarations : List SurfaceDeclaration) : List SlotId → Prop where
  | result {slots : List SlotId} :
      physicalSlotIds identification declarations = some slots →
      PrologPhysicalSlotIds identification declarations slots

theorem prologPhysicalSlotIds_iff {identification declarations slots} :
    PrologPhysicalSlotIds identification declarations slots ↔
      physicalSlotIds identification declarations = some slots := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateEagerSlotDeclaration
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (declaration : SurfaceDeclaration) :
    Option SlotDeclaration → Prop where
  | result {slot : Option SlotDeclaration} :
      elaborateEagerSlotDeclaration identification services context declaration =
        some slot →
      PrologElaborateEagerSlotDeclaration identification services context
        declaration slot

theorem prologElaborateEagerSlotDeclaration_iff
    {identification services context declaration slot} :
    PrologElaborateEagerSlotDeclaration identification services context
      declaration slot ↔
      elaborateEagerSlotDeclaration identification services context declaration =
        some slot := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateEagerSlotDeclarations
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (declarations : List SurfaceDeclaration) :
    List SlotDeclaration → Prop where
  | result {slots : List SlotDeclaration} :
      elaborateEagerSlotDeclarations identification services context declarations =
        some slots →
      PrologElaborateEagerSlotDeclarations identification services context
        declarations slots

theorem prologElaborateEagerSlotDeclarations_iff
    {identification services context declarations slots} :
    PrologElaborateEagerSlotDeclarations identification services context
      declarations slots ↔
      elaborateEagerSlotDeclarations identification services context declarations =
        some slots := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateInitializerGroup
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (group : SurfaceSlotGroup) :
    SlotDeclarationGroup → Prop where
  | result {core : SlotDeclarationGroup} :
      elaborateInitializerGroup identification services context group = some core →
      PrologElaborateInitializerGroup identification services context group core

theorem prologElaborateInitializerGroup_iff
    {identification services context group core} :
    PrologElaborateInitializerGroup identification services context group core ↔
      elaborateInitializerGroup identification services context group = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateInitializerGroups
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (group : Option SurfaceSlotGroup) :
    List SlotDeclarationGroup → Prop where
  | result {core : List SlotDeclarationGroup} :
      elaborateInitializerGroups identification services context group = some core →
      PrologElaborateInitializerGroups identification services context group core

theorem prologElaborateInitializerGroups_iff
    {identification services context group core} :
    PrologElaborateInitializerGroups identification services context group core ↔
      elaborateInitializerGroups identification services context group = some core := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologAccessOrProtected (access : Option Access) : Access → Prop where
  | result {resolved : Access} : accessOrProtected access = resolved →
      PrologAccessOrProtected access resolved

theorem prologAccessOrProtected_iff {access resolved} :
    PrologAccessOrProtected access resolved ↔
      accessOrProtected access = resolved := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologOrdinarySlotMethods (declaration : DeclId)
    (owner : ClassBodyDecl) (name : String) (access : Access)
    (mutability : SurfaceMutability) : List DerivedMethod → Prop where
  | result {methods : List DerivedMethod} :
      ordinarySlotMethods declaration owner name access mutability = methods →
      PrologOrdinarySlotMethods declaration owner name access mutability methods

theorem prologOrdinarySlotMethods_iff
    {declaration owner name access mutability methods} :
    PrologOrdinarySlotMethods declaration owner name access mutability methods ↔
      ordinarySlotMethods declaration owner name access mutability = methods := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologLazySlotMethods (declaration : DeclId)
    (owner : ClassBodyDecl) (name : String) (access : Access)
    (mutability : SurfaceMutability) (initializer : CoreExpr) :
    List DerivedMethod → Prop where
  | result {methods : List DerivedMethod} :
      lazySlotMethods declaration owner name access mutability initializer =
        methods →
      PrologLazySlotMethods declaration owner name access mutability initializer
        methods

theorem prologLazySlotMethods_iff
    {declaration owner name access mutability initializer methods} :
    PrologLazySlotMethods declaration owner name access mutability initializer
      methods ↔
      lazySlotMethods declaration owner name access mutability initializer =
        methods := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologAddDerivedMethods (image : DerivedProgramImage)
    (mixin : MixinId) (methods : List DerivedMethod) :
    DerivedProgramImage → Prop where
  | result {installed : DerivedProgramImage} :
      addDerivedMethods image mixin methods = some installed →
      PrologAddDerivedMethods image mixin methods installed

theorem prologAddDerivedMethods_iff {image mixin methods installed} :
    PrologAddDerivedMethods image mixin methods installed ↔
      addDerivedMethods image mixin methods = some installed := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

def explicitMethodContext (classContext : ElaborationContext)
    (activation : ActivationDeclId)
    (directDeclarations : List SurfaceDeclaration) : ElaborationContext :=
  let activationBinder :=
    binderForDeclarations (.activationDecl activation) directDeclarations
  { classContext with
    enclosingActivation := some activation
    activationKind := .method
    binders := activationBinder :: classContext.binders
    localReturnPermitted := true
    nonlocalReturnPermitted := false }

def explicitMethodDefinition (declaration : DeclId) (method : MethodId)
    (activation : ActivationDeclId) (selector : Selector) (access : Access)
    (parameters : List ParameterId) (locals : List LocalSlotId)
    (owner : ClassBodyDecl) : MethodDef :=
  { identity := method
    activationDeclaration := activation
    selector := selector
    access := access
    parameters := parameters
    locals := locals
    owner := owner
    body := ⟨declaration.index⟩ }

inductive PrologDeclarationMethodIdentity (declaration : DeclId) :
    MethodId → Prop where
  | result : PrologDeclarationMethodIdentity declaration
      (declarationMethodIdentity declaration)

theorem prologDeclarationMethodIdentity_iff {declaration method} :
    PrologDeclarationMethodIdentity declaration method ↔
      declarationMethodIdentity declaration = method := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst method; exact .result

inductive PrologDeclarationActivationIdentity (declaration : DeclId) :
    ActivationDeclId → Prop where
  | result : PrologDeclarationActivationIdentity declaration
      (declarationActivationIdentity declaration)

theorem prologDeclarationActivationIdentity_iff {declaration activation} :
    PrologDeclarationActivationIdentity declaration activation ↔
      declarationActivationIdentity declaration = activation := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst activation; exact .result

inductive PrologSurfaceGroupsDeclarations (groups : List SurfaceSlotGroup) :
    List SurfaceDeclaration → Prop where
  | result : PrologSurfaceGroupsDeclarations groups
      (surfaceGroupsDeclarations groups)

theorem prologSurfaceGroupsDeclarations_iff {groups declarations} :
    PrologSurfaceGroupsDeclarations groups declarations ↔
      surfaceGroupsDeclarations groups = declarations := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst declarations; exact .result

inductive PrologLocalIdentityList (identification : IdentificationOutput)
    (groups : List SurfaceSlotGroup) : List LocalSlotId → Prop where
  | result {locals : List LocalSlotId} :
      localIdentityList identification groups = some locals →
      PrologLocalIdentityList identification groups locals

theorem prologLocalIdentityList_iff {identification groups locals} :
    PrologLocalIdentityList identification groups locals ↔
      localIdentityList identification groups = some locals := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologExplicitMethodContext (classContext : ElaborationContext)
    (activation : ActivationDeclId)
    (directDeclarations : List SurfaceDeclaration) : ElaborationContext → Prop where
  | result : PrologExplicitMethodContext classContext activation directDeclarations
      (explicitMethodContext classContext activation directDeclarations)

theorem prologExplicitMethodContext_iff
    {classContext activation directDeclarations methodContext} :
    PrologExplicitMethodContext classContext activation directDeclarations
      methodContext ↔
      explicitMethodContext classContext activation directDeclarations =
        methodContext := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst methodContext; exact .result

inductive PrologExplicitMethodDefinition (declaration : DeclId)
    (method : MethodId) (activation : ActivationDeclId) (selector : Selector)
    (access : Access) (parameters : List ParameterId)
    (locals : List LocalSlotId) (owner : ClassBodyDecl) : MethodDef → Prop where
  | result : PrologExplicitMethodDefinition declaration method activation selector
      access parameters locals owner
      (explicitMethodDefinition declaration method activation selector access
        parameters locals owner)

theorem prologExplicitMethodDefinition_iff
    {declaration method activation selector access parameters locals owner
      definition} :
    PrologExplicitMethodDefinition declaration method activation selector access
      parameters locals owner definition ↔
      explicitMethodDefinition declaration method activation selector access
        parameters locals owner = definition := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst definition; exact .result

inductive PrologDerivedImageAddMethod (image : DerivedProgramImage)
    (mixin : MixinId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement) :
    DerivedProgramImage → Prop where
  | result {installed : DerivedProgramImage} :
      image.addMethod mixin definition locals body = some installed →
      PrologDerivedImageAddMethod image mixin definition locals body installed

theorem prologDerivedImageAddMethod_iff
    {image mixin definition locals body installed} :
    PrologDerivedImageAddMethod image mixin definition locals body installed ↔
      image.addMethod mixin definition locals body = some installed := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologAddActivationMembers (image : DerivedProgramImage)
    (activation : ActivationDeclId) (declarations : List SurfaceDeclaration) :
    DerivedProgramImage → Prop where
  | result : PrologAddActivationMembers image activation declarations
      (addActivationMembers image activation declarations)

theorem prologAddActivationMembers_iff
    {image activation declarations installed} :
    PrologAddActivationMembers image activation declarations installed ↔
      addActivationMembers image activation declarations = installed := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst installed; exact .result

inductive PrologDeriveExplicitMethod (identification : IdentificationOutput)
    (services : ElaborationServices) (context : ElaborationContext)
    (owner : ClassBodyDecl) (mixin : MixinId) (image : DerivedProgramImage)
    (declaration : SurfaceDeclaration) : DerivedProgramImage → Prop where
  | result {installed : DerivedProgramImage} :
      deriveExplicitMethod identification services context owner mixin image
        declaration = some installed →
      PrologDeriveExplicitMethod identification services context owner mixin
        image declaration installed

theorem prologDeriveExplicitMethod_iff
    {identification services context owner mixin image declaration installed} :
    PrologDeriveExplicitMethod identification services context owner mixin image
      declaration installed ↔
      deriveExplicitMethod identification services context owner mixin image
        declaration = some installed := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveMemberDeclaration
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (owner : ClassBodyDecl) (mixin : MixinId)
    (image : DerivedProgramImage) (declaration : SurfaceDeclaration) :
    DerivedProgramImage → Prop where
  | result {installed : DerivedProgramImage} :
      deriveMemberDeclaration identification services context owner mixin image
        declaration = some installed →
      PrologDeriveMemberDeclaration identification services context owner mixin
        image declaration installed

theorem prologDeriveMemberDeclaration_iff
    {identification services context owner mixin image declaration installed} :
    PrologDeriveMemberDeclaration identification services context owner mixin
      image declaration installed ↔
      deriveMemberDeclaration identification services context owner mixin image
        declaration = some installed := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveMemberDeclarations
    (identification : IdentificationOutput) (services : ElaborationServices)
    (context : ElaborationContext) (owner : ClassBodyDecl) (mixin : MixinId)
    (image : DerivedProgramImage) (declarations : List SurfaceDeclaration) :
    DerivedProgramImage → Prop where
  | result {installed : DerivedProgramImage} :
      deriveMemberDeclarations identification services context owner mixin image
        declarations = some installed →
      PrologDeriveMemberDeclarations identification services context owner mixin
        image declarations installed

theorem prologDeriveMemberDeclarations_iff
    {identification services context owner mixin image declarations installed} :
    PrologDeriveMemberDeclarations identification services context owner mixin
      image declarations installed ↔
      deriveMemberDeclarations identification services context owner mixin image
        declarations = some installed := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

end PrologBridge
end Newspeak
