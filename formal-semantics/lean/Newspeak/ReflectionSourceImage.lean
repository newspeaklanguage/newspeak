import Newspeak.ReflectionTransactions

namespace Newspeak

/-- The identified, normalized source nodes needed by reflective code edits.
    Method identity, owner, selector, local declarations, and body are retained
    separately because the installed `Program` indexes each projection by the
    key used at run time.  Other source nodes are unchanged by code commands
    and remain in the previous program skeleton during re-elaboration. -/
structure IdentifiedSourceImage where
  mixins : FiniteStore MixinId MixinDef
  methodBodies : FiniteStore MethodId (List Statement)
  methodLocals : FiniteStore MethodId (List LocalDeclarationGroup)
  methodMixins : FiniteStore MethodId MixinId
  methodSelectors : FiniteStore MethodId Selector

namespace IdentifiedSourceImage

/-- Source images denote the same identified AST when all five finite indexes
    agree pointwise.  Domain order is intentionally unobservable: independent
    fresh additions may prepend their keys in opposite orders. -/
structure LookupEquivalent (left right : IdentifiedSourceImage) : Prop where
  mixins : left.mixins.LookupEquivalent right.mixins
  methodBodies : left.methodBodies.LookupEquivalent right.methodBodies
  methodLocals : left.methodLocals.LookupEquivalent right.methodLocals
  methodMixins : left.methodMixins.LookupEquivalent right.methodMixins
  methodSelectors :
    left.methodSelectors.LookupEquivalent right.methodSelectors

theorem LookupEquivalent.refl (source : IdentifiedSourceImage) :
    source.LookupEquivalent source :=
  { mixins := FiniteStore.LookupEquivalent.refl source.mixins
    methodBodies := FiniteStore.LookupEquivalent.refl source.methodBodies
    methodLocals := FiniteStore.LookupEquivalent.refl source.methodLocals
    methodMixins := FiniteStore.LookupEquivalent.refl source.methodMixins
    methodSelectors := FiniteStore.LookupEquivalent.refl source.methodSelectors }

theorem LookupEquivalent.symm {left right : IdentifiedSourceImage}
    (equivalent : left.LookupEquivalent right) :
    right.LookupEquivalent left :=
  { mixins := equivalent.mixins.symm
    methodBodies := equivalent.methodBodies.symm
    methodLocals := equivalent.methodLocals.symm
    methodMixins := equivalent.methodMixins.symm
    methodSelectors := equivalent.methodSelectors.symm }

theorem LookupEquivalent.trans {first second third : IdentifiedSourceImage}
    (left : first.LookupEquivalent second)
    (right : second.LookupEquivalent third) :
    first.LookupEquivalent third :=
  { mixins := left.mixins.trans right.mixins
    methodBodies := left.methodBodies.trans right.methodBodies
    methodLocals := left.methodLocals.trans right.methodLocals
    methodMixins := left.methodMixins.trans right.methodMixins
    methodSelectors := left.methodSelectors.trans right.methodSelectors }

def installProgram (source : IdentifiedSourceImage) (previous : Program) :
    Program :=
  { previous with
    mixins := source.mixins
    methodBodies := source.methodBodies
    methodLocals := fun method => (source.methodLocals method).getD [] }

def methodEntryConsistent (source : IdentifiedSourceImage)
    (mixinId : MixinId) (mixin : MixinDef) (selector : Selector) : Bool :=
  match mixin.methods selector with
  | none => false
  | some method =>
      method.selector == selector &&
      method.owner == mixin.declaration &&
      source.methodMixins method.identity == some mixinId &&
      source.methodSelectors method.identity == some selector &&
      (source.methodBodies method.identity).isSome &&
      (source.methodLocals method.identity).isSome

def mixinConsistent (source : IdentifiedSourceImage) (mixinId : MixinId) : Bool :=
  match source.mixins mixinId with
  | none => false
  | some mixin =>
      mixin.methods.domain.all (source.methodEntryConsistent mixinId mixin)

def methodIndexConsistent (source : IdentifiedSourceImage)
    (method : MethodId) : Bool :=
  match source.methodMixins method, source.methodSelectors method with
  | some mixinId, some selector =>
      match source.mixins mixinId with
      | some mixin =>
          match mixin.methods selector with
          | some definition =>
              definition.identity == method &&
              (source.methodBodies method).isSome &&
              (source.methodLocals method).isSome
          | none => false
      | none => false
  | _, _ => false

/-- Executable static check used by the concrete reflection front end before
    it publishes a rebuilt program.  Both directions are checked: every
    method dictionary entry has complete source projections, and every method
    identity index points back to its dictionary entry. -/
def consistent (source : IdentifiedSourceImage) : Bool :=
  source.mixins.domain.all source.mixinConsistent &&
    source.methodMixins.domain.all source.methodIndexConsistent &&
    FiniteStore.sameDomain source.methodMixins source.methodSelectors &&
    FiniteStore.sameDomain source.methodMixins source.methodBodies &&
    FiniteStore.sameDomain source.methodMixins source.methodLocals

def replaceSourceMethodBody (source : IdentifiedSourceImage)
    (method : MethodId) (body : List Statement) : Option IdentifiedSourceImage := do
  let _ ← source.methodMixins method
  let _ ← source.methodBodies method
  some { source with methodBodies := source.methodBodies.install method body }

def replacementSelectorAvailable (mixin : MixinDef) (method : MethodId)
    (selector : Selector) : Bool :=
  match mixin.methods selector with
  | some occupant => decide (occupant.identity = method)
  | none => true

def replaceSourceMethodDefinition (source : IdentifiedSourceImage)
    (mixinId : MixinId) (method : MethodId) (definition : MethodDef)
    (localGroups : List LocalDeclarationGroup) (body : List Statement) :
    Option IdentifiedSourceImage := do
  guard (decide (definition.identity = method))
  let owner ← source.methodMixins method
  guard (decide (owner = mixinId))
  let oldSelector ← source.methodSelectors method
  let mixin ← source.mixins mixinId
  let oldDefinition ← mixin.methods oldSelector
  guard (decide (oldDefinition.identity = method))
  guard (decide (definition.owner = mixin.declaration))
  guard (replacementSelectorAvailable mixin method definition.selector)
  let methods :=
    (mixin.methods.erase oldSelector).install definition.selector definition
  let updatedMixin := { mixin with methods := methods }
  some { source with
    mixins := source.mixins.install mixinId updatedMixin
    methodBodies := source.methodBodies.install method body
    methodLocals := source.methodLocals.install method localGroups
    methodSelectors := source.methodSelectors.install method definition.selector }

def addSourceMethodDefinition (source : IdentifiedSourceImage)
    (mixinId : MixinId) (definition : MethodDef)
    (localGroups : List LocalDeclarationGroup) (body : List Statement) :
    Option IdentifiedSourceImage := do
  guard ((source.methodMixins definition.identity).isNone)
  guard ((source.methodSelectors definition.identity).isNone)
  guard ((source.methodBodies definition.identity).isNone)
  guard ((source.methodLocals definition.identity).isNone)
  let mixin ← source.mixins mixinId
  guard ((mixin.methods definition.selector).isNone)
  guard (decide (definition.owner = mixin.declaration))
  let updatedMixin :=
    { mixin with
      methods := mixin.methods.install definition.selector definition }
  some { source with
    mixins := source.mixins.install mixinId updatedMixin
    methodBodies := source.methodBodies.install definition.identity body
    methodLocals := source.methodLocals.install definition.identity localGroups
    methodMixins := source.methodMixins.install definition.identity mixinId
    methodSelectors :=
      source.methodSelectors.install definition.identity definition.selector }

def removeSourceMethodDefinition (source : IdentifiedSourceImage)
    (mixinId : MixinId) (method : MethodId) : Option IdentifiedSourceImage := do
  let owner ← source.methodMixins method
  guard (decide (owner = mixinId))
  let selector ← source.methodSelectors method
  let mixin ← source.mixins mixinId
  let definition ← mixin.methods selector
  guard (decide (definition.identity = method))
  let updatedMixin := { mixin with methods := mixin.methods.erase selector }
  some { source with
    mixins := source.mixins.install mixinId updatedMixin
    methodBodies := source.methodBodies.erase method
    methodLocals := source.methodLocals.erase method
    methodMixins := source.methodMixins.erase method
    methodSelectors := source.methodSelectors.erase method }

/-- Update one existing mixin node without changing any of the method identity
    indexes.  Slot, nested-class, and initializer replacement are the three
    concrete instances below. -/
def transformExistingSourceMixin (source : IdentifiedSourceImage)
    (mixinId : MixinId) (transform : MixinDef → MixinDef) :
    Option IdentifiedSourceImage := do
  let mixin ← source.mixins mixinId
  some { source with
    mixins := source.mixins.install mixinId (transform mixin) }

def sourceSlotDeclarationTransform (groups : List SlotDeclarationGroup)
    (mixin : MixinDef) : MixinDef :=
  { mixin with ownSlots := groups.flatMap SlotDeclarationGroup.slots }

def sourceNestedDeclarationTransform (declarations : List ClassDeclId)
    (mixin : MixinDef) : MixinDef :=
  { mixin with nestedDeclarations := declarations }

def sourceMixinInitializerTransform
    (initializer : MixinInitializerReplacement) (mixin : MixinDef) : MixinDef :=
  { mixin with
    initializerDeclaration := initializer.declaration
    initializerSelector := initializer.selector
    initializerParameters := initializer.parameters
    initializerGroups := initializer.groups
    initializerBody := initializer.body }

def replaceSourceSlotDeclarations (source : IdentifiedSourceImage)
    (mixinId : MixinId) (groups : List SlotDeclarationGroup) :
    Option IdentifiedSourceImage :=
  source.transformExistingSourceMixin mixinId
    (sourceSlotDeclarationTransform groups)

def replaceSourceNestedDeclarations (source : IdentifiedSourceImage)
    (mixinId : MixinId) (declarations : List ClassDeclId) :
    Option IdentifiedSourceImage :=
  source.transformExistingSourceMixin mixinId
    (sourceNestedDeclarationTransform declarations)

def replaceSourceMixinInitializer (source : IdentifiedSourceImage)
    (mixinId : MixinId) (initializer : MixinInitializerReplacement) :
    Option IdentifiedSourceImage :=
  source.transformExistingSourceMixin mixinId
    (sourceMixinInitializerTransform initializer)

/-- One equation for each member of `CodeCommand`; non-code commands are
    rejected rather than silently ignored. -/
def patchSourceCodeCommand (source : IdentifiedSourceImage) :
    ReflectionCommand → Option IdentifiedSourceImage
  | .replaceMethodBody _ method body =>
      source.replaceSourceMethodBody method body
  | .replaceMethodDefinition _ mixin method definition localGroups body =>
      source.replaceSourceMethodDefinition mixin method definition localGroups body
  | .addMethodDefinition _ mixin definition localGroups body =>
      source.addSourceMethodDefinition mixin definition localGroups body
  | .removeMethodDefinition _ mixin method =>
      source.removeSourceMethodDefinition mixin method
  | .replaceSlotDeclarations _ mixin groups =>
      source.replaceSourceSlotDeclarations mixin groups
  | .replaceNestedDeclarations _ mixin declarations =>
      source.replaceSourceNestedDeclarations mixin declarations
  | .replaceMixinInitializer _ mixin initializer =>
      source.replaceSourceMixinInitializer mixin initializer
  | _ => none

def applySourceCodeCommands : IdentifiedSourceImage → List ReflectionCommand →
    Option IdentifiedSourceImage
  | source, [] => some source
  | source, command :: remaining => do
      let patched ← source.patchSourceCodeCommand command
      applySourceCodeCommands patched remaining

def reelaborateInstalledProgram (previous : Program)
    (source : IdentifiedSourceImage) : Option Program :=
  if source.consistent then some (source.installProgram previous) else none

end IdentifiedSourceImage

/-- Concrete realization of the source/reflection boundary. -/
def identifiedSourceReflectionFrontEnd : ReflectionFrontEnd IdentifiedSourceImage :=
  { patchSourceCommands := IdentifiedSourceImage.applySourceCodeCommands
    reelaborateProgram := IdentifiedSourceImage.reelaborateInstalledProgram }

@[simp] theorem IdentifiedSourceImage.applySourceCodeCommands_nil
    (source : IdentifiedSourceImage) :
    source.applySourceCodeCommands [] = some source := by
  rfl

theorem IdentifiedSourceImage.replaceSourceMethodBody_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (method : MethodId) (body : List Statement) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.replaceSourceMethodBody method body)
      (right.replaceSourceMethodBody method body) := by
  unfold IdentifiedSourceImage.replaceSourceMethodBody
  cases owner : left.methodMixins method with
  | none =>
      have rightOwner : right.methodMixins method = none := by
        rw [← equivalent.methodMixins method]
        exact owner
      simp [rightOwner]
      exact .bothFailed
  | some mixin =>
      have rightOwner : right.methodMixins method = some mixin := by
        rw [← equivalent.methodMixins method]
        exact owner
      cases oldBody : left.methodBodies method with
      | none =>
          have rightBody : right.methodBodies method = none := by
            rw [← equivalent.methodBodies method]
            exact oldBody
          simp [rightOwner, rightBody]
          exact .bothFailed
      | some previousBody =>
          have rightBody : right.methodBodies method = some previousBody := by
            rw [← equivalent.methodBodies method]
            exact oldBody
          simp only [rightOwner, rightBody]
          exact .bothSucceeded
            { mixins := equivalent.mixins
              methodBodies := equivalent.methodBodies.install method body
              methodLocals := equivalent.methodLocals
              methodMixins := equivalent.methodMixins
              methodSelectors := equivalent.methodSelectors }

theorem IdentifiedSourceImage.transformExistingSourceMixin_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixinId : MixinId) (transform : MixinDef → MixinDef) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.transformExistingSourceMixin mixinId transform)
      (right.transformExistingSourceMixin mixinId transform) := by
  unfold IdentifiedSourceImage.transformExistingSourceMixin
  cases present : left.mixins mixinId with
  | none =>
      have rightPresent : right.mixins mixinId = none := by
        rw [← equivalent.mixins mixinId]
        exact present
      simp [rightPresent]
      exact .bothFailed
  | some mixin =>
      have rightPresent : right.mixins mixinId = some mixin := by
        rw [← equivalent.mixins mixinId]
        exact present
      simp only [rightPresent]
      exact .bothSucceeded
        { mixins := equivalent.mixins.install mixinId (transform mixin)
          methodBodies := equivalent.methodBodies
          methodLocals := equivalent.methodLocals
          methodMixins := equivalent.methodMixins
          methodSelectors := equivalent.methodSelectors }

theorem IdentifiedSourceImage.replaceSourceSlotDeclarations_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixin : MixinId) (groups : List SlotDeclarationGroup) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.replaceSourceSlotDeclarations mixin groups)
      (right.replaceSourceSlotDeclarations mixin groups) :=
  left.transformExistingSourceMixin_respects_lookupEquivalent equivalent mixin _

theorem IdentifiedSourceImage.replaceSourceNestedDeclarations_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixin : MixinId) (declarations : List ClassDeclId) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.replaceSourceNestedDeclarations mixin declarations)
      (right.replaceSourceNestedDeclarations mixin declarations) :=
  left.transformExistingSourceMixin_respects_lookupEquivalent equivalent mixin _

theorem IdentifiedSourceImage.replaceSourceMixinInitializer_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixin : MixinId) (initializer : MixinInitializerReplacement) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.replaceSourceMixinInitializer mixin initializer)
      (right.replaceSourceMixinInitializer mixin initializer) :=
  left.transformExistingSourceMixin_respects_lookupEquivalent equivalent mixin _

set_option linter.unusedSimpArgs false in
theorem IdentifiedSourceImage.addSourceMethodDefinition_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixinId : MixinId) (definition : MethodDef)
    (localGroups : List LocalDeclarationGroup) (body : List Statement) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.addSourceMethodDefinition mixinId definition localGroups body)
      (right.addSourceMethodDefinition mixinId definition localGroups body) := by
  unfold IdentifiedSourceImage.addSourceMethodDefinition
  rw [← equivalent.methodMixins definition.identity,
    ← equivalent.methodSelectors definition.identity,
    ← equivalent.methodBodies definition.identity,
    ← equivalent.methodLocals definition.identity,
    ← equivalent.mixins mixinId]
  cases methodMixinResult : left.methodMixins definition.identity with
  | some existing =>
      simp [methodMixinResult, guard]
      exact .bothFailed
  | none =>
      simp [methodMixinResult, guard]
      cases methodSelectorResult : left.methodSelectors definition.identity with
      | some existing =>
          simp [methodSelectorResult, guard]
          exact .bothFailed
      | none =>
          simp [methodSelectorResult, guard]
          cases methodBodyResult : left.methodBodies definition.identity with
          | some existing =>
              simp [methodBodyResult, guard]
              exact .bothFailed
          | none =>
              simp [methodBodyResult, guard]
              cases methodLocalsResult : left.methodLocals definition.identity with
              | some existing =>
                  simp [methodLocalsResult, guard]
                  exact .bothFailed
              | none =>
                  simp [methodLocalsResult, guard]
                  cases mixinResult : left.mixins mixinId with
                  | none =>
                      simp [mixinResult]
                      exact .bothFailed
                  | some mixin =>
                      simp [mixinResult]
                      cases dictionaryResult : mixin.methods definition.selector with
                      | some occupant =>
                          simp [dictionaryResult, guard]
                          exact .bothFailed
                      | none =>
                          by_cases owner : definition.owner = mixin.declaration
                          · simp [dictionaryResult, owner, guard]
                            exact .bothSucceeded
                              { mixins := equivalent.mixins.install mixinId
                                  ({ mixin with methods :=
                                      (mixin.methods.install definition.selector
                                        definition) })
                                methodBodies := equivalent.methodBodies.install
                                  definition.identity body
                                methodLocals := equivalent.methodLocals.install
                                  definition.identity localGroups
                                methodMixins := equivalent.methodMixins.install
                                  definition.identity mixinId
                                methodSelectors :=
                                  equivalent.methodSelectors.install
                                    definition.identity definition.selector }
                          · simp [dictionaryResult, owner, guard]
                            exact .bothFailed

set_option linter.unusedSimpArgs false in
theorem IdentifiedSourceImage.removeSourceMethodDefinition_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixinId : MixinId) (method : MethodId) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.removeSourceMethodDefinition mixinId method)
      (right.removeSourceMethodDefinition mixinId method) := by
  unfold IdentifiedSourceImage.removeSourceMethodDefinition
  rw [← equivalent.methodMixins method,
    ← equivalent.methodSelectors method, ← equivalent.mixins mixinId]
  cases ownerResult : left.methodMixins method with
  | none =>
      simp
      exact .bothFailed
  | some owner =>
      by_cases correctOwner : owner = mixinId
      · simp [correctOwner, guard]
        cases selectorResult : left.methodSelectors method with
        | none =>
            simp
            exact .bothFailed
        | some selector =>
            simp
            cases mixinResult : left.mixins mixinId with
            | none =>
                simp
                exact .bothFailed
            | some mixin =>
                simp
                cases definitionResult : mixin.methods selector with
                | none =>
                    simp
                    exact .bothFailed
                | some definition =>
                    by_cases identity : definition.identity = method
                    · simp [identity, guard]
                      exact .bothSucceeded
                        { mixins := equivalent.mixins.install mixinId
                            ({ mixin with methods := mixin.methods.erase selector })
                          methodBodies := equivalent.methodBodies.erase method
                          methodLocals := equivalent.methodLocals.erase method
                          methodMixins := equivalent.methodMixins.erase method
                          methodSelectors :=
                            equivalent.methodSelectors.erase method }
                    · simp [identity, guard]
                      exact .bothFailed
      · simp [correctOwner, guard]
        exact .bothFailed

set_option linter.unusedSimpArgs false in
theorem IdentifiedSourceImage.replaceSourceMethodDefinition_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (mixinId : MixinId) (method : MethodId) (definition : MethodDef)
    (localGroups : List LocalDeclarationGroup) (body : List Statement) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.replaceSourceMethodDefinition mixinId method definition localGroups body)
      (right.replaceSourceMethodDefinition mixinId method definition localGroups body) := by
  unfold IdentifiedSourceImage.replaceSourceMethodDefinition
  rw [← equivalent.methodMixins method,
    ← equivalent.methodSelectors method, ← equivalent.mixins mixinId]
  by_cases newIdentity : definition.identity = method
  · simp [newIdentity, guard]
    cases ownerResult : left.methodMixins method with
    | none =>
        simp
        exact .bothFailed
    | some owner =>
        by_cases correctOwner : owner = mixinId
        · simp [correctOwner, guard]
          cases selectorResult : left.methodSelectors method with
          | none =>
              simp
              exact .bothFailed
          | some oldSelector =>
              simp
              cases mixinResult : left.mixins mixinId with
              | none =>
                  simp
                  exact .bothFailed
              | some mixin =>
                  simp
                  cases oldDefinitionResult : mixin.methods oldSelector with
                  | none =>
                      simp
                      exact .bothFailed
                  | some oldDefinition =>
                      by_cases oldIdentity : oldDefinition.identity = method
                      · simp [oldIdentity, guard]
                        by_cases newOwner :
                            definition.owner = mixin.declaration
                        · simp [newOwner, guard]
                          cases availability : replacementSelectorAvailable mixin
                              method definition.selector with
                          | false =>
                              simp
                              exact .bothFailed
                          | true =>
                              simp
                              let methods := (mixin.methods.erase oldSelector).install
                                definition.selector definition
                              exact .bothSucceeded
                                { mixins := equivalent.mixins.install mixinId
                                    ({ mixin with methods := methods })
                                  methodBodies :=
                                    equivalent.methodBodies.install method body
                                  methodLocals :=
                                    equivalent.methodLocals.install method localGroups
                                  methodMixins := equivalent.methodMixins
                                  methodSelectors :=
                                    equivalent.methodSelectors.install method
                                      definition.selector }
                        · simp [newOwner, guard]
                          exact .bothFailed
                      · simp [oldIdentity, guard]
                        exact .bothFailed
        · simp [correctOwner, guard]
          exact .bothFailed
  · simp [newIdentity, guard]
    exact .bothFailed

theorem IdentifiedSourceImage.patchSourceCodeCommand_respects_lookupEquivalent
    {left right : IdentifiedSourceImage} (equivalent : left.LookupEquivalent right)
    (command : ReflectionCommand) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (left.patchSourceCodeCommand command)
      (right.patchSourceCodeCommand command) := by
  cases command with
  | replaceMethodBody _ method body =>
      exact left.replaceSourceMethodBody_respects_lookupEquivalent equivalent
        method body
  | replaceMethodDefinition _ mixin method definition locals body =>
      exact left.replaceSourceMethodDefinition_respects_lookupEquivalent
        equivalent mixin method definition locals body
  | addMethodDefinition _ mixin definition locals body =>
      exact left.addSourceMethodDefinition_respects_lookupEquivalent equivalent
        mixin definition locals body
  | removeMethodDefinition _ mixin method =>
      exact left.removeSourceMethodDefinition_respects_lookupEquivalent equivalent
        mixin method
  | replaceSlotDeclarations _ mixin groups =>
      exact left.replaceSourceSlotDeclarations_respects_lookupEquivalent
        equivalent mixin groups
  | replaceNestedDeclarations _ mixin declarations =>
      exact left.replaceSourceNestedDeclarations_respects_lookupEquivalent
        equivalent mixin declarations
  | replaceMixinInitializer _ mixin initializer =>
      exact left.replaceSourceMixinInitializer_respects_lookupEquivalent
        equivalent mixin initializer
  | changeSuperclass | changeClassEnclosingObject | changeObjectClass
  | objectSlotWrite | activationParameterWrite | activationLocalWrite
  | changeActivationCurrentClass | changeActivationContinuation
  | makeActivationUncontinuable | continueAtActivation | pauseActor
  | replaceCurrentActorStack | replacePausedActorStack
  | resumePausedActorAtFullSpeed | replaceAndResumePausedActorStack =>
      exact .bothFailed

theorem IdentifiedSourceImage.LookupEquivalent.methodEntryConsistent_eq
    {left right : IdentifiedSourceImage}
    (equivalent : left.LookupEquivalent right)
    (mixinId : MixinId) (mixin : MixinDef) (selector : Selector) :
    left.methodEntryConsistent mixinId mixin selector =
      right.methodEntryConsistent mixinId mixin selector := by
  unfold IdentifiedSourceImage.methodEntryConsistent
  cases definitionResult : mixin.methods selector with
  | none => rfl
  | some definition =>
      simp [equivalent.methodMixins definition.identity,
        equivalent.methodSelectors definition.identity,
        equivalent.methodBodies definition.identity,
        equivalent.methodLocals definition.identity]

theorem IdentifiedSourceImage.LookupEquivalent.mixinConsistent_eq
    {left right : IdentifiedSourceImage}
    (equivalent : left.LookupEquivalent right) (mixinId : MixinId) :
    left.mixinConsistent mixinId = right.mixinConsistent mixinId := by
  unfold IdentifiedSourceImage.mixinConsistent
  rw [equivalent.mixins mixinId]
  cases mixinResult : right.mixins mixinId with
  | none => rfl
  | some mixin =>
      apply List.all_congr rfl
      intro selector
      exact equivalent.methodEntryConsistent_eq mixinId mixin selector

theorem IdentifiedSourceImage.LookupEquivalent.methodIndexConsistent_eq
    {left right : IdentifiedSourceImage}
    (equivalent : left.LookupEquivalent right) (method : MethodId) :
    left.methodIndexConsistent method =
      right.methodIndexConsistent method := by
  unfold IdentifiedSourceImage.methodIndexConsistent
  rw [equivalent.methodMixins method, equivalent.methodSelectors method]
  cases mixinResult : right.methodMixins method with
  | none => rfl
  | some mixinId =>
      cases selectorResult : right.methodSelectors method with
      | none => rfl
      | some selector =>
          simp [equivalent.mixins mixinId,
            equivalent.methodBodies method,
            equivalent.methodLocals method]

/-- Source consistency is semantic: it is invariant under finite-store
    domain permutations as long as every lookup agrees. -/
theorem IdentifiedSourceImage.LookupEquivalent.consistent_eq
    {left right : IdentifiedSourceImage}
    (equivalent : left.LookupEquivalent right) :
    left.consistent = right.consistent := by
  have mixinsEqual := equivalent.mixins.all_domain_eq
    (leftPredicate := left.mixinConsistent)
    (rightPredicate := right.mixinConsistent)
    equivalent.mixinConsistent_eq
  have indicesEqual := equivalent.methodMixins.all_domain_eq
    (leftPredicate := left.methodIndexConsistent)
    (rightPredicate := right.methodIndexConsistent)
    equivalent.methodIndexConsistent_eq
  have selectorsEqual := FiniteStore.sameDomain_eq_of_lookupEquivalent
    equivalent.methodMixins equivalent.methodSelectors
  have bodiesEqual := FiniteStore.sameDomain_eq_of_lookupEquivalent
    equivalent.methodMixins equivalent.methodBodies
  have localsEqual := FiniteStore.sameDomain_eq_of_lookupEquivalent
    equivalent.methodMixins equivalent.methodLocals
  simp [IdentifiedSourceImage.consistent, mixinsEqual, indicesEqual,
    selectorsEqual, bodiesEqual, localsEqual]

@[simp] theorem IdentifiedSourceImage.replaceSourceMethodBody_lookup
    {source after : IdentifiedSourceImage} {method : MethodId}
    {body : List Statement}
    (patched : source.replaceSourceMethodBody method body = some after) :
    after.methodBodies method = some body := by
  unfold IdentifiedSourceImage.replaceSourceMethodBody at patched
  cases owner : source.methodMixins method <;> simp [owner] at patched
  cases oldBody : source.methodBodies method <;> simp [oldBody] at patched
  rw [← patched]
  simp

theorem IdentifiedSourceImage.reelaborateInstalledProgram_projects_source
    {previous candidate : Program} {source : IdentifiedSourceImage}
    (rebuilt : source.reelaborateInstalledProgram previous = some candidate) :
    candidate.mixins = source.mixins ∧
      candidate.methodBodies = source.methodBodies := by
  unfold IdentifiedSourceImage.reelaborateInstalledProgram at rebuilt
  split at rebuilt
  · injection rebuilt with equal
    subst candidate
    exact ⟨rfl, rfl⟩
  · contradiction

theorem IdentifiedSourceImage.installProgram_lookupEquivalent
    {left right : IdentifiedSourceImage} (previous : Program)
    (equivalent : left.LookupEquivalent right) :
    (left.installProgram previous).LookupEquivalent
      (right.installProgram previous) :=
  { top := rfl
    object := rfl
    classClass := rfl
    metaclassClass := rfl
    messageMirrorClass := rfl
    activationClass := rfl
    closureClass := rfl
    nilObject := rfl
    mixins := equivalent.mixins
    methodBodies := equivalent.methodBodies
    methodLocals := fun method => by
      simp only [IdentifiedSourceImage.installProgram]
      rw [equivalent.methodLocals method]
    closureParameters := fun _ => rfl
    closureLocals := fun _ => rfl
    closureBodies := FiniteStore.LookupEquivalent.refl previous.closureBodies
    pastFutureExpression := fun _ => rfl
    atoms := fun _ => rfl
    platform := FiniteStore.LookupEquivalent.refl previous.platform
    patternVariable :=
      FiniteStore.LookupEquivalent.refl previous.patternVariable
    classBodies := FiniteStore.LookupEquivalent.refl previous.classBodies
    mixinApplications :=
      FiniteStore.LookupEquivalent.refl previous.mixinApplications
    objectLiterals := FiniteStore.LookupEquivalent.refl previous.objectLiterals
    actorSeeds := FiniteStore.LookupEquivalent.refl previous.actorSeeds
    classOwner := fun _ => rfl
    objectLiteralOwner := fun _ => rfl
    declMixin := FiniteStore.LookupEquivalent.refl previous.declMixin
    lexParent := FiniteStore.LookupEquivalent.refl previous.lexParent
    scopeChain := fun _ => rfl
    declares := fun _ _ => rfl }

theorem IdentifiedSourceImage.reelaborateInstalledProgram_lookupEquivalent
    {left right : IdentifiedSourceImage} {previous first second : Program}
    (equivalent : left.LookupEquivalent right)
    (firstRebuilt : left.reelaborateInstalledProgram previous = some first)
    (secondRebuilt : right.reelaborateInstalledProgram previous = some second) :
    first.LookupEquivalent second := by
  unfold IdentifiedSourceImage.reelaborateInstalledProgram at firstRebuilt secondRebuilt
  split at firstRebuilt
  · split at secondRebuilt
    · injection firstRebuilt with firstEqual
      injection secondRebuilt with secondEqual
      subst first
      subst second
      exact left.installProgram_lookupEquivalent previous equivalent
    · contradiction
  · contradiction

theorem IdentifiedSourceImage.reelaborateInstalledProgram_related_of_consistent
    {left right : IdentifiedSourceImage} (previous : Program)
    (equivalent : left.LookupEquivalent right)
    (leftConsistent : left.consistent = true)
    (rightConsistent : right.consistent = true) :
    OptionalResultsRelated Program.LookupEquivalent
      (left.reelaborateInstalledProgram previous)
      (right.reelaborateInstalledProgram previous) := by
  simp [IdentifiedSourceImage.reelaborateInstalledProgram, leftConsistent,
    rightConsistent]
  exact .bothSucceeded (left.installProgram_lookupEquivalent previous equivalent)

theorem IdentifiedSourceImage.reelaborateInstalledProgram_related
    {left right : IdentifiedSourceImage} (previous : Program)
    (equivalent : left.LookupEquivalent right)
    (consistency : left.consistent = right.consistent) :
    OptionalResultsRelated Program.LookupEquivalent
      (left.reelaborateInstalledProgram previous)
      (right.reelaborateInstalledProgram previous) := by
  cases leftResult : left.consistent with
  | false =>
      have rightResult : right.consistent = false := by
        rw [← consistency]
        exact leftResult
      simp [IdentifiedSourceImage.reelaborateInstalledProgram, leftResult,
        rightResult]
      exact .bothFailed
  | true =>
      have rightResult : right.consistent = true := by
        rw [← consistency]
        exact leftResult
      exact left.reelaborateInstalledProgram_related_of_consistent previous
        equivalent leftResult rightResult

theorem IdentifiedSourceImage.reelaborateInstalledProgram_related_of_lookupEquivalent
    {left right : IdentifiedSourceImage} (previous : Program)
    (equivalent : left.LookupEquivalent right) :
    OptionalResultsRelated Program.LookupEquivalent
      (left.reelaborateInstalledProgram previous)
      (right.reelaborateInstalledProgram previous) :=
  left.reelaborateInstalledProgram_related previous equivalent
    equivalent.consistent_eq

theorem IdentifiedSourceImage.transformExistingSourceMixin_distinct_commutes
    (source : IdentifiedSourceImage) {first second : MixinId}
    (different : first ≠ second) (firstTransform secondTransform : MixinDef → MixinDef)
    {firstDefinition secondDefinition : MixinDef}
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    (do
      let afterFirst ← source.transformExistingSourceMixin first firstTransform
      afterFirst.transformExistingSourceMixin second secondTransform) =
    (do
      let afterSecond ← source.transformExistingSourceMixin second secondTransform
      afterSecond.transformExistingSourceMixin first firstTransform) := by
  have firstMember := source.mixins.mem_domain_of_lookup_eq_some firstPresent
  have secondMember := source.mixins.mem_domain_of_lookup_eq_some secondPresent
  simp [IdentifiedSourceImage.transformExistingSourceMixin, firstPresent,
    secondPresent, different, different.symm]
  rw [source.mixins.install_distinct_commute_of_mem different firstMember
    secondMember (firstTransform firstDefinition)
    (secondTransform secondDefinition)]

theorem IdentifiedSourceImage.transformExistingSourceMixin_same_commutes
    (source : IdentifiedSourceImage) (mixinId : MixinId)
    (firstTransform secondTransform : MixinDef → MixinDef)
    {definition : MixinDef}
    (present : source.mixins mixinId = some definition)
    (transformsCommute :
      secondTransform (firstTransform definition) =
        firstTransform (secondTransform definition)) :
    (do
      let afterFirst ←
        source.transformExistingSourceMixin mixinId firstTransform
      afterFirst.transformExistingSourceMixin mixinId secondTransform) =
    (do
      let afterSecond ←
        source.transformExistingSourceMixin mixinId secondTransform
      afterSecond.transformExistingSourceMixin mixinId firstTransform) := by
  simp [IdentifiedSourceImage.transformExistingSourceMixin, present,
    transformsCommute]
  rw [FiniteStore.install_same_key_overwrites,
    FiniteStore.install_same_key_overwrites]

theorem IdentifiedSourceImage.transformExistingSourceMixin_distinct_commutes_total
    (source : IdentifiedSourceImage) {first second : MixinId}
    (different : first ≠ second)
    (firstTransform secondTransform : MixinDef → MixinDef) :
    (do
      let afterFirst ← source.transformExistingSourceMixin first firstTransform
      afterFirst.transformExistingSourceMixin second secondTransform) =
    (do
      let afterSecond ← source.transformExistingSourceMixin second secondTransform
      afterSecond.transformExistingSourceMixin first firstTransform) := by
  cases firstPresent : source.mixins first with
  | none =>
      cases secondPresent : source.mixins second <;>
        simp [IdentifiedSourceImage.transformExistingSourceMixin, firstPresent,
          secondPresent, different]
  | some firstDefinition =>
      cases secondPresent : source.mixins second with
      | none =>
          simp [IdentifiedSourceImage.transformExistingSourceMixin,
            firstPresent, secondPresent, different.symm]
      | some secondDefinition =>
          exact source.transformExistingSourceMixin_distinct_commutes different
            firstTransform secondTransform firstPresent secondPresent

theorem IdentifiedSourceImage.transformExistingSourceMixin_same_commutes_total
    (source : IdentifiedSourceImage) (mixinId : MixinId)
    (firstTransform secondTransform : MixinDef → MixinDef)
    (transformsCommute : ∀ definition,
      secondTransform (firstTransform definition) =
        firstTransform (secondTransform definition)) :
    (do
      let afterFirst ←
        source.transformExistingSourceMixin mixinId firstTransform
      afterFirst.transformExistingSourceMixin mixinId secondTransform) =
    (do
      let afterSecond ←
        source.transformExistingSourceMixin mixinId secondTransform
      afterSecond.transformExistingSourceMixin mixinId firstTransform) := by
  cases present : source.mixins mixinId with
  | none => simp [IdentifiedSourceImage.transformExistingSourceMixin, present]
  | some definition =>
      exact source.transformExistingSourceMixin_same_commutes mixinId _ _
        present (transformsCommute definition)

theorem IdentifiedSourceImage.transformExistingSourceMixin_commutes_total
    (source : IdentifiedSourceImage) (first second : MixinId)
    (firstTransform secondTransform : MixinDef → MixinDef)
    (transformsCommute : ∀ definition,
      secondTransform (firstTransform definition) =
        firstTransform (secondTransform definition)) :
    (do
      let afterFirst ← source.transformExistingSourceMixin first firstTransform
      afterFirst.transformExistingSourceMixin second secondTransform) =
    (do
      let afterSecond ← source.transformExistingSourceMixin second secondTransform
      afterSecond.transformExistingSourceMixin first firstTransform) := by
  by_cases equal : first = second
  · subst second
    exact source.transformExistingSourceMixin_same_commutes_total first _ _
      transformsCommute
  · exact source.transformExistingSourceMixin_distinct_commutes_total equal _ _

theorem sourceSlotAndNestedTransforms_commute
    (groups : List SlotDeclarationGroup) (declarations : List ClassDeclId)
    (definition : MixinDef) :
    IdentifiedSourceImage.sourceNestedDeclarationTransform declarations
        (IdentifiedSourceImage.sourceSlotDeclarationTransform groups definition) =
      IdentifiedSourceImage.sourceSlotDeclarationTransform groups
        (IdentifiedSourceImage.sourceNestedDeclarationTransform declarations
          definition) := by
  rfl

theorem sourceSlotAndInitializerTransforms_commute
    (groups : List SlotDeclarationGroup)
    (initializer : MixinInitializerReplacement) (definition : MixinDef) :
    IdentifiedSourceImage.sourceMixinInitializerTransform initializer
        (IdentifiedSourceImage.sourceSlotDeclarationTransform groups definition) =
      IdentifiedSourceImage.sourceSlotDeclarationTransform groups
        (IdentifiedSourceImage.sourceMixinInitializerTransform initializer
          definition) := by
  rfl

theorem sourceNestedAndInitializerTransforms_commute
    (declarations : List ClassDeclId)
    (initializer : MixinInitializerReplacement) (definition : MixinDef) :
    IdentifiedSourceImage.sourceMixinInitializerTransform initializer
        (IdentifiedSourceImage.sourceNestedDeclarationTransform declarations
          definition) =
      IdentifiedSourceImage.sourceNestedDeclarationTransform declarations
        (IdentifiedSourceImage.sourceMixinInitializerTransform initializer
          definition) := by
  rfl

theorem IdentifiedSourceImage.replaceSourceMethodBody_and_mixinTransform_commute
    (source : IdentifiedSourceImage) (method : MethodId) (body : List Statement)
    (mixinId : MixinId) (transform : MixinDef → MixinDef)
    {owner : MixinId} {oldBody : List Statement} {definition : MixinDef}
    (ownerPresent : source.methodMixins method = some owner)
    (bodyPresent : source.methodBodies method = some oldBody)
    (mixinPresent : source.mixins mixinId = some definition) :
    (do
      let afterBody ← source.replaceSourceMethodBody method body
      afterBody.transformExistingSourceMixin mixinId transform) =
    (do
      let afterMixin ← source.transformExistingSourceMixin mixinId transform
      afterMixin.replaceSourceMethodBody method body) := by
  simp [IdentifiedSourceImage.replaceSourceMethodBody,
    IdentifiedSourceImage.transformExistingSourceMixin, ownerPresent,
    bodyPresent, mixinPresent]

theorem IdentifiedSourceImage.replaceSourceMethodBody_and_mixinTransform_commute_total
    (source : IdentifiedSourceImage) (method : MethodId)
    (body : List Statement) (mixinId : MixinId)
    (transform : MixinDef → MixinDef) :
    (do
      let afterBody ← source.replaceSourceMethodBody method body
      afterBody.transformExistingSourceMixin mixinId transform) =
    (do
      let afterMixin ← source.transformExistingSourceMixin mixinId transform
      afterMixin.replaceSourceMethodBody method body) := by
  cases ownerPresent : source.methodMixins method with
  | none =>
      cases mixinPresent : source.mixins mixinId <;>
        simp [IdentifiedSourceImage.replaceSourceMethodBody,
          IdentifiedSourceImage.transformExistingSourceMixin, ownerPresent,
          mixinPresent]
  | some owner =>
      cases bodyPresent : source.methodBodies method with
      | none =>
          cases mixinPresent : source.mixins mixinId <;>
            simp [IdentifiedSourceImage.replaceSourceMethodBody,
              IdentifiedSourceImage.transformExistingSourceMixin,
              ownerPresent, bodyPresent, mixinPresent]
      | some oldBody =>
          cases mixinPresent : source.mixins mixinId with
          | none =>
              simp [IdentifiedSourceImage.replaceSourceMethodBody,
                IdentifiedSourceImage.transformExistingSourceMixin,
                ownerPresent, bodyPresent, mixinPresent]
          | some definition =>
              exact source.replaceSourceMethodBody_and_mixinTransform_commute
                method body mixinId transform ownerPresent bodyPresent
                mixinPresent

theorem IdentifiedSourceImage.replaceSourceSlotAndNested_commute
    (source : IdentifiedSourceImage) (slotMixin nestedMixin : MixinId)
    (groups : List SlotDeclarationGroup) (declarations : List ClassDeclId)
    {slotDefinition nestedDefinition : MixinDef}
    (slotPresent : source.mixins slotMixin = some slotDefinition)
    (nestedPresent : source.mixins nestedMixin = some nestedDefinition) :
    (do
      let afterSlots ← source.replaceSourceSlotDeclarations slotMixin groups
      afterSlots.replaceSourceNestedDeclarations nestedMixin declarations) =
    (do
      let afterNested ←
        source.replaceSourceNestedDeclarations nestedMixin declarations
      afterNested.replaceSourceSlotDeclarations slotMixin groups) := by
  by_cases equal : slotMixin = nestedMixin
  · subst nestedMixin
    have definitionsEqual : slotDefinition = nestedDefinition := by
      rw [slotPresent] at nestedPresent
      injection nestedPresent
    subst nestedDefinition
    exact source.transformExistingSourceMixin_same_commutes slotMixin _ _
      slotPresent (sourceSlotAndNestedTransforms_commute groups declarations _)
  · exact source.transformExistingSourceMixin_distinct_commutes equal _ _
      slotPresent nestedPresent

theorem IdentifiedSourceImage.replaceSourceSlotAndInitializer_commute
    (source : IdentifiedSourceImage) (slotMixin initializerMixin : MixinId)
    (groups : List SlotDeclarationGroup)
    (initializer : MixinInitializerReplacement)
    {slotDefinition initializerDefinition : MixinDef}
    (slotPresent : source.mixins slotMixin = some slotDefinition)
    (initializerPresent :
      source.mixins initializerMixin = some initializerDefinition) :
    (do
      let afterSlots ← source.replaceSourceSlotDeclarations slotMixin groups
      afterSlots.replaceSourceMixinInitializer initializerMixin initializer) =
    (do
      let afterInitializer ←
        source.replaceSourceMixinInitializer initializerMixin initializer
      afterInitializer.replaceSourceSlotDeclarations slotMixin groups) := by
  by_cases equal : slotMixin = initializerMixin
  · subst initializerMixin
    have definitionsEqual : slotDefinition = initializerDefinition := by
      rw [slotPresent] at initializerPresent
      injection initializerPresent
    subst initializerDefinition
    exact source.transformExistingSourceMixin_same_commutes slotMixin _ _
      slotPresent
      (sourceSlotAndInitializerTransforms_commute groups initializer _)
  · exact source.transformExistingSourceMixin_distinct_commutes equal _ _
      slotPresent initializerPresent

theorem IdentifiedSourceImage.replaceSourceNestedAndInitializer_commute
    (source : IdentifiedSourceImage) (nestedMixin initializerMixin : MixinId)
    (declarations : List ClassDeclId)
    (initializer : MixinInitializerReplacement)
    {nestedDefinition initializerDefinition : MixinDef}
    (nestedPresent : source.mixins nestedMixin = some nestedDefinition)
    (initializerPresent :
      source.mixins initializerMixin = some initializerDefinition) :
    (do
      let afterNested ←
        source.replaceSourceNestedDeclarations nestedMixin declarations
      afterNested.replaceSourceMixinInitializer initializerMixin initializer) =
    (do
      let afterInitializer ←
        source.replaceSourceMixinInitializer initializerMixin initializer
      afterInitializer.replaceSourceNestedDeclarations nestedMixin declarations) := by
  by_cases equal : nestedMixin = initializerMixin
  · subst initializerMixin
    have definitionsEqual : nestedDefinition = initializerDefinition := by
      rw [nestedPresent] at initializerPresent
      injection initializerPresent
    subst initializerDefinition
    exact source.transformExistingSourceMixin_same_commutes nestedMixin _ _
      nestedPresent
      (sourceNestedAndInitializerTransforms_commute declarations initializer _)
  · exact source.transformExistingSourceMixin_distinct_commutes equal _ _
      nestedPresent initializerPresent

theorem IdentifiedSourceImage.replaceSourceSlotAndNested_commute_total
    (source : IdentifiedSourceImage) (slotMixin nestedMixin : MixinId)
    (groups : List SlotDeclarationGroup)
    (declarations : List ClassDeclId) :
    (do
      let afterSlots ← source.replaceSourceSlotDeclarations slotMixin groups
      afterSlots.replaceSourceNestedDeclarations nestedMixin declarations) =
    (do
      let afterNested ←
        source.replaceSourceNestedDeclarations nestedMixin declarations
      afterNested.replaceSourceSlotDeclarations slotMixin groups) := by
  exact source.transformExistingSourceMixin_commutes_total slotMixin
    nestedMixin _ _ (sourceSlotAndNestedTransforms_commute groups declarations)

theorem IdentifiedSourceImage.replaceSourceSlotAndInitializer_commute_total
    (source : IdentifiedSourceImage) (slotMixin initializerMixin : MixinId)
    (groups : List SlotDeclarationGroup)
    (initializer : MixinInitializerReplacement) :
    (do
      let afterSlots ← source.replaceSourceSlotDeclarations slotMixin groups
      afterSlots.replaceSourceMixinInitializer initializerMixin initializer) =
    (do
      let afterInitializer ←
        source.replaceSourceMixinInitializer initializerMixin initializer
      afterInitializer.replaceSourceSlotDeclarations slotMixin groups) := by
  exact source.transformExistingSourceMixin_commutes_total slotMixin
    initializerMixin _ _
      (sourceSlotAndInitializerTransforms_commute groups initializer)

theorem IdentifiedSourceImage.replaceSourceNestedAndInitializer_commute_total
    (source : IdentifiedSourceImage) (nestedMixin initializerMixin : MixinId)
    (declarations : List ClassDeclId)
    (initializer : MixinInitializerReplacement) :
    (do
      let afterNested ←
        source.replaceSourceNestedDeclarations nestedMixin declarations
      afterNested.replaceSourceMixinInitializer initializerMixin initializer) =
    (do
      let afterInitializer ←
        source.replaceSourceMixinInitializer initializerMixin initializer
      afterInitializer.replaceSourceNestedDeclarations nestedMixin declarations) := by
  exact source.transformExistingSourceMixin_commutes_total nestedMixin
    initializerMixin _ _
      (sourceNestedAndInitializerTransforms_commute declarations initializer)

theorem IdentifiedSourceImage.replaceSourceMethodBody_commutes
    (source : IdentifiedSourceImage) {first second : MethodId}
    (different : first ≠ second) (firstBody secondBody : List Statement)
    {firstOwner secondOwner : MixinId}
    {oldFirstBody oldSecondBody : List Statement}
    (firstOwnerPresent : source.methodMixins first = some firstOwner)
    (secondOwnerPresent : source.methodMixins second = some secondOwner)
    (firstBodyPresent : source.methodBodies first = some oldFirstBody)
    (secondBodyPresent : source.methodBodies second = some oldSecondBody) :
    (do
      let afterFirst ← source.replaceSourceMethodBody first firstBody
      afterFirst.replaceSourceMethodBody second secondBody) =
    (do
      let afterSecond ← source.replaceSourceMethodBody second secondBody
      afterSecond.replaceSourceMethodBody first firstBody) := by
  have firstPresent :=
    source.methodBodies.mem_domain_of_lookup_eq_some firstBodyPresent
  have secondPresent :=
    source.methodBodies.mem_domain_of_lookup_eq_some secondBodyPresent
  simp [IdentifiedSourceImage.replaceSourceMethodBody, firstOwnerPresent,
    secondOwnerPresent, firstBodyPresent, secondBodyPresent, different,
    different.symm]
  rw [source.methodBodies.install_distinct_commute_of_mem different
    firstPresent secondPresent firstBody secondBody]

theorem IdentifiedSourceImage.replaceSourceMethodBody_distinct_commutes_total
    (source : IdentifiedSourceImage) {first second : MethodId}
    (different : first ≠ second) (firstBody secondBody : List Statement) :
    (do
      let afterFirst ← source.replaceSourceMethodBody first firstBody
      afterFirst.replaceSourceMethodBody second secondBody) =
    (do
      let afterSecond ← source.replaceSourceMethodBody second secondBody
      afterSecond.replaceSourceMethodBody first firstBody) := by
  cases firstOwnerPresent : source.methodMixins first with
  | none =>
      cases secondOwnerPresent : source.methodMixins second with
      | none =>
          simp [IdentifiedSourceImage.replaceSourceMethodBody,
            firstOwnerPresent, secondOwnerPresent]
      | some secondOwner =>
          cases secondBodyPresent : source.methodBodies second <;>
            simp [IdentifiedSourceImage.replaceSourceMethodBody,
              firstOwnerPresent, secondOwnerPresent, secondBodyPresent,
              different, different.symm]
  | some firstOwner =>
      cases firstBodyPresent : source.methodBodies first with
      | none =>
          cases secondOwnerPresent : source.methodMixins second with
          | none =>
              simp [IdentifiedSourceImage.replaceSourceMethodBody,
                firstOwnerPresent, firstBodyPresent, secondOwnerPresent]
          | some secondOwner =>
              cases secondBodyPresent : source.methodBodies second <;>
                simp [IdentifiedSourceImage.replaceSourceMethodBody,
                  firstOwnerPresent, firstBodyPresent, secondOwnerPresent,
                  secondBodyPresent, different, different.symm]
      | some oldFirstBody =>
          cases secondOwnerPresent : source.methodMixins second with
          | none =>
              simp [IdentifiedSourceImage.replaceSourceMethodBody,
                firstOwnerPresent, firstBodyPresent, secondOwnerPresent,
                different.symm]
          | some secondOwner =>
              cases secondBodyPresent : source.methodBodies second with
              | none =>
                  simp [IdentifiedSourceImage.replaceSourceMethodBody,
                    firstOwnerPresent, firstBodyPresent, secondOwnerPresent,
                    secondBodyPresent, different.symm]
              | some oldSecondBody =>
                  exact source.replaceSourceMethodBody_commutes different
                    firstBody secondBody firstOwnerPresent secondOwnerPresent
                    firstBodyPresent secondBodyPresent

theorem IdentifiedSourceImage.replaceSourceMethodBody_and_removeSourceMethodDefinition_commute
    (source : IdentifiedSourceImage) {bodyMethod removedMethod : MethodId}
    (different : bodyMethod ≠ removedMethod) (body : List Statement)
    (removedMixin : MixinId) {bodyOwner : MixinId}
    {oldBody : List Statement} {removedSelector : Selector}
    {mixinDefinition : MixinDef} {methodDefinition : MethodDef}
    (bodyOwnerPresent : source.methodMixins bodyMethod = some bodyOwner)
    (bodyPresent : source.methodBodies bodyMethod = some oldBody)
    (removedOwnerPresent :
      source.methodMixins removedMethod = some removedMixin)
    (removedSelectorPresent :
      source.methodSelectors removedMethod = some removedSelector)
    (mixinPresent : source.mixins removedMixin = some mixinDefinition)
    (definitionPresent :
      mixinDefinition.methods removedSelector = some methodDefinition)
    (identity : methodDefinition.identity = removedMethod) :
    (do
      let afterBody ← source.replaceSourceMethodBody bodyMethod body
      afterBody.removeSourceMethodDefinition removedMixin removedMethod) =
    (do
      let afterRemove ←
        source.removeSourceMethodDefinition removedMixin removedMethod
      afterRemove.replaceSourceMethodBody bodyMethod body) := by
  have bodyMember :=
    source.methodBodies.mem_domain_of_lookup_eq_some bodyPresent
  simp [IdentifiedSourceImage.replaceSourceMethodBody,
    IdentifiedSourceImage.removeSourceMethodDefinition, guard,
    bodyOwnerPresent, bodyPresent, removedOwnerPresent,
    removedSelectorPresent, mixinPresent, definitionPresent, identity,
    different, different.symm]
  rw [source.methodBodies.install_erase_distinct_commute_of_mem different
    bodyMember body]

theorem IdentifiedSourceImage.replaceSourceSlotDeclarations_commutes
    (source : IdentifiedSourceImage) {first second : MixinId}
    (different : first ≠ second)
    (firstGroups secondGroups : List SlotDeclarationGroup)
    {firstDefinition secondDefinition : MixinDef}
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    (do
      let afterFirst ← source.replaceSourceSlotDeclarations first firstGroups
      afterFirst.replaceSourceSlotDeclarations second secondGroups) =
    (do
      let afterSecond ← source.replaceSourceSlotDeclarations second secondGroups
      afterSecond.replaceSourceSlotDeclarations first firstGroups) := by
  exact source.transformExistingSourceMixin_distinct_commutes different _ _
    firstPresent secondPresent

theorem IdentifiedSourceImage.replaceSourceNestedDeclarations_commutes
    (source : IdentifiedSourceImage) {first second : MixinId}
    (different : first ≠ second)
    (firstDeclarations secondDeclarations : List ClassDeclId)
    {firstDefinition secondDefinition : MixinDef}
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    (do
      let afterFirst ←
        source.replaceSourceNestedDeclarations first firstDeclarations
      afterFirst.replaceSourceNestedDeclarations second secondDeclarations) =
    (do
      let afterSecond ←
        source.replaceSourceNestedDeclarations second secondDeclarations
      afterSecond.replaceSourceNestedDeclarations first firstDeclarations) := by
  exact source.transformExistingSourceMixin_distinct_commutes different _ _
    firstPresent secondPresent

theorem IdentifiedSourceImage.replaceSourceMixinInitializer_commutes
    (source : IdentifiedSourceImage) {first second : MixinId}
    (different : first ≠ second)
    (firstInitializer secondInitializer : MixinInitializerReplacement)
    {firstDefinition secondDefinition : MixinDef}
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    (do
      let afterFirst ←
        source.replaceSourceMixinInitializer first firstInitializer
      afterFirst.replaceSourceMixinInitializer second secondInitializer) =
    (do
      let afterSecond ←
        source.replaceSourceMixinInitializer second secondInitializer
      afterSecond.replaceSourceMixinInitializer first firstInitializer) := by
  exact source.transformExistingSourceMixin_distinct_commutes different _ _
    firstPresent secondPresent

theorem IdentifiedSourceImage.removeSourceMethodDefinition_commutes
    (source : IdentifiedSourceImage) {firstMixin secondMixin : MixinId}
    {firstMethod secondMethod : MethodId}
    (differentMixins : firstMixin ≠ secondMixin)
    (differentMethods : firstMethod ≠ secondMethod)
    {firstSelector secondSelector : Selector}
    {firstMixinDefinition secondMixinDefinition : MixinDef}
    {firstMethodDefinition secondMethodDefinition : MethodDef}
    (firstOwnerPresent :
      source.methodMixins firstMethod = some firstMixin)
    (secondOwnerPresent :
      source.methodMixins secondMethod = some secondMixin)
    (firstSelectorPresent :
      source.methodSelectors firstMethod = some firstSelector)
    (secondSelectorPresent :
      source.methodSelectors secondMethod = some secondSelector)
    (firstMixinPresent :
      source.mixins firstMixin = some firstMixinDefinition)
    (secondMixinPresent :
      source.mixins secondMixin = some secondMixinDefinition)
    (firstDefinitionPresent :
      firstMixinDefinition.methods firstSelector = some firstMethodDefinition)
    (secondDefinitionPresent :
      secondMixinDefinition.methods secondSelector = some secondMethodDefinition)
    (firstIdentity : firstMethodDefinition.identity = firstMethod)
    (secondIdentity : secondMethodDefinition.identity = secondMethod) :
    (do
      let afterFirst ←
        source.removeSourceMethodDefinition firstMixin firstMethod
      afterFirst.removeSourceMethodDefinition secondMixin secondMethod) =
    (do
      let afterSecond ←
        source.removeSourceMethodDefinition secondMixin secondMethod
      afterSecond.removeSourceMethodDefinition firstMixin firstMethod) := by
  have firstMixinMember :=
    source.mixins.mem_domain_of_lookup_eq_some firstMixinPresent
  have secondMixinMember :=
    source.mixins.mem_domain_of_lookup_eq_some secondMixinPresent
  simp [IdentifiedSourceImage.removeSourceMethodDefinition,
    guard,
    firstOwnerPresent, secondOwnerPresent, firstSelectorPresent,
    secondSelectorPresent, firstMixinPresent, secondMixinPresent,
    firstDefinitionPresent, secondDefinitionPresent, firstIdentity,
    secondIdentity, differentMixins, differentMixins.symm,
    differentMethods, differentMethods.symm]
  rw [source.mixins.install_distinct_commute_of_mem differentMixins
    firstMixinMember secondMixinMember
    { firstMixinDefinition with
      methods := firstMixinDefinition.methods.erase firstSelector }
    { secondMixinDefinition with
      methods := secondMixinDefinition.methods.erase secondSelector }]
  rw [source.methodBodies.erase_distinct_commute differentMethods]
  rw [source.methodLocals.erase_distinct_commute differentMethods]
  rw [source.methodMixins.erase_distinct_commute differentMethods]
  rw [source.methodSelectors.erase_distinct_commute differentMethods]
  simp

theorem IdentifiedSourceImage.replaceSourceMethodDefinition_commutes
    (source : IdentifiedSourceImage) {firstMixin secondMixin : MixinId}
    {firstMethod secondMethod : MethodId}
    (differentMixins : firstMixin ≠ secondMixin)
    (differentMethods : firstMethod ≠ secondMethod)
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    {firstOldSelector secondOldSelector : Selector}
    {firstMixinDefinition secondMixinDefinition : MixinDef}
    {firstOldDefinition secondOldDefinition : MethodDef}
    (firstIdentity : firstDefinition.identity = firstMethod)
    (secondIdentity : secondDefinition.identity = secondMethod)
    (firstOwnerPresent : source.methodMixins firstMethod = some firstMixin)
    (secondOwnerPresent : source.methodMixins secondMethod = some secondMixin)
    (firstSelectorPresent :
      source.methodSelectors firstMethod = some firstOldSelector)
    (secondSelectorPresent :
      source.methodSelectors secondMethod = some secondOldSelector)
    (firstMixinPresent :
      source.mixins firstMixin = some firstMixinDefinition)
    (secondMixinPresent :
      source.mixins secondMixin = some secondMixinDefinition)
    (firstOldPresent :
      firstMixinDefinition.methods firstOldSelector = some firstOldDefinition)
    (secondOldPresent :
      secondMixinDefinition.methods secondOldSelector = some secondOldDefinition)
    (firstOldIdentity : firstOldDefinition.identity = firstMethod)
    (secondOldIdentity : secondOldDefinition.identity = secondMethod)
    (firstNewOwner :
      firstDefinition.owner = firstMixinDefinition.declaration)
    (secondNewOwner :
      secondDefinition.owner = secondMixinDefinition.declaration)
    (firstNewSelectorAvailable : replacementSelectorAvailable
      firstMixinDefinition firstMethod firstDefinition.selector = true)
    (secondNewSelectorAvailable : replacementSelectorAvailable
      secondMixinDefinition secondMethod secondDefinition.selector = true)
    {firstOldBody secondOldBody : List Statement}
    {firstOldLocals secondOldLocals : List LocalDeclarationGroup}
    (firstBodyPresent : source.methodBodies firstMethod = some firstOldBody)
    (secondBodyPresent : source.methodBodies secondMethod = some secondOldBody)
    (firstLocalsPresent :
      source.methodLocals firstMethod = some firstOldLocals)
    (secondLocalsPresent :
      source.methodLocals secondMethod = some secondOldLocals) :
    (do
      let afterFirst ← source.replaceSourceMethodDefinition firstMixin
        firstMethod firstDefinition firstLocals firstBody
      afterFirst.replaceSourceMethodDefinition secondMixin secondMethod
        secondDefinition secondLocals secondBody) =
    (do
      let afterSecond ← source.replaceSourceMethodDefinition secondMixin
        secondMethod secondDefinition secondLocals secondBody
      afterSecond.replaceSourceMethodDefinition firstMixin firstMethod
        firstDefinition firstLocals firstBody) := by
  have firstMixinMember :=
    source.mixins.mem_domain_of_lookup_eq_some firstMixinPresent
  have secondMixinMember :=
    source.mixins.mem_domain_of_lookup_eq_some secondMixinPresent
  have firstBodyMember :=
    source.methodBodies.mem_domain_of_lookup_eq_some firstBodyPresent
  have secondBodyMember :=
    source.methodBodies.mem_domain_of_lookup_eq_some secondBodyPresent
  have firstLocalsMember :=
    source.methodLocals.mem_domain_of_lookup_eq_some firstLocalsPresent
  have secondLocalsMember :=
    source.methodLocals.mem_domain_of_lookup_eq_some secondLocalsPresent
  have firstSelectorMember :=
    source.methodSelectors.mem_domain_of_lookup_eq_some firstSelectorPresent
  have secondSelectorMember :=
    source.methodSelectors.mem_domain_of_lookup_eq_some secondSelectorPresent
  simp [IdentifiedSourceImage.replaceSourceMethodDefinition, guard,
    firstIdentity, secondIdentity, firstOwnerPresent, secondOwnerPresent,
    firstSelectorPresent, secondSelectorPresent, firstMixinPresent,
    secondMixinPresent, firstOldPresent, secondOldPresent, firstOldIdentity,
    secondOldIdentity, firstNewOwner, secondNewOwner,
    firstNewSelectorAvailable, secondNewSelectorAvailable, differentMixins,
    differentMixins.symm, differentMethods, differentMethods.symm]
  rw [source.mixins.install_distinct_commute_of_mem differentMixins
    firstMixinMember secondMixinMember]
  rw [source.methodBodies.install_distinct_commute_of_mem differentMethods
    firstBodyMember secondBodyMember]
  rw [source.methodLocals.install_distinct_commute_of_mem differentMethods
    firstLocalsMember secondLocalsMember]
  rw [source.methodSelectors.install_distinct_commute_of_mem differentMethods
    firstSelectorMember secondSelectorMember]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem IdentifiedSourceImage.addSourceMethodDefinition_commutes_extensionally
    (source : IdentifiedSourceImage) {firstMixin secondMixin : MixinId}
    (differentMixins : firstMixin ≠ secondMixin)
    (firstDefinition secondDefinition : MethodDef)
    (differentMethods : firstDefinition.identity ≠ secondDefinition.identity)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    {firstMixinDefinition secondMixinDefinition : MixinDef}
    (firstMixinPresent :
      source.mixins firstMixin = some firstMixinDefinition)
    (secondMixinPresent :
      source.mixins secondMixin = some secondMixinDefinition)
    (firstMethodFresh :
      source.methodMixins firstDefinition.identity = none)
    (secondMethodFresh :
      source.methodMixins secondDefinition.identity = none)
    (firstSelectorFresh :
      source.methodSelectors firstDefinition.identity = none)
    (secondSelectorFresh :
      source.methodSelectors secondDefinition.identity = none)
    (firstBodyFresh : source.methodBodies firstDefinition.identity = none)
    (secondBodyFresh : source.methodBodies secondDefinition.identity = none)
    (firstLocalsFresh : source.methodLocals firstDefinition.identity = none)
    (secondLocalsFresh : source.methodLocals secondDefinition.identity = none)
    (firstDictionaryFresh :
      firstMixinDefinition.methods firstDefinition.selector = none)
    (secondDictionaryFresh :
      secondMixinDefinition.methods secondDefinition.selector = none)
    (firstOwner : firstDefinition.owner = firstMixinDefinition.declaration)
    (secondOwner : secondDefinition.owner = secondMixinDefinition.declaration) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (do
        let afterFirst ← source.addSourceMethodDefinition firstMixin
          firstDefinition firstLocals firstBody
        afterFirst.addSourceMethodDefinition secondMixin secondDefinition
          secondLocals secondBody)
      (do
        let afterSecond ← source.addSourceMethodDefinition secondMixin
          secondDefinition secondLocals secondBody
        afterSecond.addSourceMethodDefinition firstMixin firstDefinition
          firstLocals firstBody) := by
  have firstMixinMember :=
    source.mixins.mem_domain_of_lookup_eq_some firstMixinPresent
  have secondMixinMember :=
    source.mixins.mem_domain_of_lookup_eq_some secondMixinPresent
  simp [IdentifiedSourceImage.addSourceMethodDefinition, guard,
    firstMixinPresent, secondMixinPresent, firstMethodFresh, secondMethodFresh,
    firstSelectorFresh, secondSelectorFresh, firstBodyFresh, secondBodyFresh,
    firstLocalsFresh, secondLocalsFresh, firstDictionaryFresh,
    secondDictionaryFresh, firstOwner, secondOwner, differentMixins,
    differentMixins.symm, differentMethods, differentMethods.symm]
  apply OptionalResultsRelated.bothSucceeded
  refine
    { mixins := ?_
      methodBodies := ?_
      methodLocals := ?_
      methodMixins := ?_
      methodSelectors := ?_ }
  · intro mixin
    rw [source.mixins.install_distinct_commute_of_mem differentMixins
      firstMixinMember secondMixinMember]
  · exact source.methodBodies.install_distinct_commute_lookup
      differentMethods firstBody secondBody
  · exact source.methodLocals.install_distinct_commute_lookup
      differentMethods firstLocals secondLocals
  · exact source.methodMixins.install_distinct_commute_lookup
      differentMethods firstMixin secondMixin
  · exact source.methodSelectors.install_distinct_commute_lookup
      differentMethods firstDefinition.selector secondDefinition.selector

theorem IdentifiedSourceImage.addSourceMethodDefinition_and_mixinTransform_commute
    (source : IdentifiedSourceImage) (methodMixin fieldMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (transform : MixinDef → MixinDef)
    (preservesDeclaration : ∀ mixin,
      (transform mixin).declaration = mixin.declaration)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (commutesWithMethods : ∀ mixin methods,
      transform { mixin with methods := methods } =
        { transform mixin with methods := methods })
    {mixinDefinition fieldDefinition : MixinDef}
    (methodFresh : source.methodMixins definition.identity = none)
    (selectorFresh : source.methodSelectors definition.identity = none)
    (bodyFresh : source.methodBodies definition.identity = none)
    (localsFresh : source.methodLocals definition.identity = none)
    (mixinPresent : source.mixins methodMixin = some mixinDefinition)
    (dictionaryFresh : mixinDefinition.methods definition.selector = none)
    (owner : definition.owner = mixinDefinition.declaration)
    (fieldPresent : source.mixins fieldMixin = some fieldDefinition) :
    (do
      let added ← source.addSourceMethodDefinition methodMixin definition
        locals body
      added.transformExistingSourceMixin fieldMixin transform) =
    (do
      let transformed ← source.transformExistingSourceMixin fieldMixin transform
      transformed.addSourceMethodDefinition methodMixin definition locals body) := by
  by_cases same : methodMixin = fieldMixin
  · subst fieldMixin
    rw [mixinPresent] at fieldPresent
    injection fieldPresent with definitionsEqual
    subst fieldDefinition
    have transformedFresh :
        (transform mixinDefinition).methods definition.selector = none := by
      rw [preservesMethods]
      exact dictionaryFresh
    simp [IdentifiedSourceImage.addSourceMethodDefinition,
      IdentifiedSourceImage.transformExistingSourceMixin, methodFresh,
      selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
      owner, transformedFresh, preservesDeclaration, guard]
    rw [commutesWithMethods]
    rw [FiniteStore.install_same_key_overwrites,
      FiniteStore.install_same_key_overwrites]
    dsimp
    rw [preservesDeclaration, preservesMethods]
  · have methodMember :=
      source.mixins.mem_domain_of_lookup_eq_some mixinPresent
    have fieldMember := source.mixins.mem_domain_of_lookup_eq_some fieldPresent
    simp [IdentifiedSourceImage.addSourceMethodDefinition,
      IdentifiedSourceImage.transformExistingSourceMixin, methodFresh,
      selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
      owner, fieldPresent, guard, preservesDeclaration, preservesMethods,
      same, Ne.symm same]
    rw [source.mixins.install_distinct_commute_of_mem same methodMember
      fieldMember]

theorem IdentifiedSourceImage.removeSourceMethodDefinition_and_mixinTransform_commute
    (source : IdentifiedSourceImage) (methodMixin fieldMixin : MixinId)
    (method : MethodId) (transform : MixinDef → MixinDef)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (commutesWithMethods : ∀ mixin methods,
      transform { mixin with methods := methods } =
        { transform mixin with methods := methods })
    {selector : Selector} {mixinDefinition fieldDefinition : MixinDef}
    {methodDefinition : MethodDef}
    (ownerPresent : source.methodMixins method = some methodMixin)
    (selectorPresent : source.methodSelectors method = some selector)
    (mixinPresent : source.mixins methodMixin = some mixinDefinition)
    (definitionPresent :
      mixinDefinition.methods selector = some methodDefinition)
    (identity : methodDefinition.identity = method)
    (fieldPresent : source.mixins fieldMixin = some fieldDefinition) :
    (do
      let removed ← source.removeSourceMethodDefinition methodMixin method
      removed.transformExistingSourceMixin fieldMixin transform) =
    (do
      let transformed ← source.transformExistingSourceMixin fieldMixin transform
      transformed.removeSourceMethodDefinition methodMixin method) := by
  by_cases same : methodMixin = fieldMixin
  · subst fieldMixin
    rw [mixinPresent] at fieldPresent
    injection fieldPresent with definitionsEqual
    subst fieldDefinition
    have transformedPresent :
        (transform mixinDefinition).methods selector = some methodDefinition := by
      rw [preservesMethods]
      exact definitionPresent
    simp [IdentifiedSourceImage.removeSourceMethodDefinition,
      IdentifiedSourceImage.transformExistingSourceMixin, ownerPresent,
      selectorPresent, mixinPresent, definitionPresent, transformedPresent,
      identity, guard]
    rw [commutesWithMethods]
    rw [FiniteStore.install_same_key_overwrites,
      FiniteStore.install_same_key_overwrites]
    rw [preservesMethods]
  · have methodMember :=
      source.mixins.mem_domain_of_lookup_eq_some mixinPresent
    have fieldMember := source.mixins.mem_domain_of_lookup_eq_some fieldPresent
    simp [IdentifiedSourceImage.removeSourceMethodDefinition,
      IdentifiedSourceImage.transformExistingSourceMixin, ownerPresent,
      selectorPresent, mixinPresent, definitionPresent, identity, fieldPresent,
      guard, preservesMethods, same, Ne.symm same]
    rw [source.mixins.install_distinct_commute_of_mem same methodMember
      fieldMember]

theorem IdentifiedSourceImage.replaceSourceMethodDefinition_and_mixinTransform_commute
    (source : IdentifiedSourceImage) (methodMixin fieldMixin : MixinId)
    (method : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement)
    (transform : MixinDef → MixinDef)
    (preservesDeclaration : ∀ mixin,
      (transform mixin).declaration = mixin.declaration)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (commutesWithMethods : ∀ mixin methods,
      transform { mixin with methods := methods } =
        { transform mixin with methods := methods })
    {oldSelector : Selector} {mixinDefinition fieldDefinition : MixinDef}
    {oldDefinition : MethodDef}
    (identity : definition.identity = method)
    (ownerPresent : source.methodMixins method = some methodMixin)
    (selectorPresent : source.methodSelectors method = some oldSelector)
    (mixinPresent : source.mixins methodMixin = some mixinDefinition)
    (oldPresent : mixinDefinition.methods oldSelector = some oldDefinition)
    (oldIdentity : oldDefinition.identity = method)
    (newOwner : definition.owner = mixinDefinition.declaration)
    (selectorAvailable : replacementSelectorAvailable mixinDefinition method
      definition.selector = true)
    (fieldPresent : source.mixins fieldMixin = some fieldDefinition) :
    (do
      let replaced ← source.replaceSourceMethodDefinition methodMixin method
        definition locals body
      replaced.transformExistingSourceMixin fieldMixin transform) =
    (do
      let transformed ← source.transformExistingSourceMixin fieldMixin transform
      transformed.replaceSourceMethodDefinition methodMixin method definition
        locals body) := by
  by_cases same : methodMixin = fieldMixin
  · subst fieldMixin
    rw [mixinPresent] at fieldPresent
    injection fieldPresent with definitionsEqual
    subst fieldDefinition
    have transformedAvailable : replacementSelectorAvailable
        (transform mixinDefinition) method definition.selector = true := by
      unfold replacementSelectorAvailable
      rw [preservesMethods]
      exact selectorAvailable
    simp [IdentifiedSourceImage.replaceSourceMethodDefinition,
      IdentifiedSourceImage.transformExistingSourceMixin, identity,
      ownerPresent, selectorPresent, mixinPresent, oldPresent, oldIdentity,
      newOwner, selectorAvailable, guard, preservesDeclaration,
      preservesMethods, transformedAvailable]
    rw [commutesWithMethods]
    rw [FiniteStore.install_same_key_overwrites,
      FiniteStore.install_same_key_overwrites]
    dsimp
    rw [preservesDeclaration]
  · have methodMember :=
      source.mixins.mem_domain_of_lookup_eq_some mixinPresent
    have fieldMember := source.mixins.mem_domain_of_lookup_eq_some fieldPresent
    simp [IdentifiedSourceImage.replaceSourceMethodDefinition,
      IdentifiedSourceImage.transformExistingSourceMixin, identity,
      ownerPresent, selectorPresent, mixinPresent, oldPresent, oldIdentity,
      newOwner, selectorAvailable, fieldPresent, guard, preservesDeclaration,
      preservesMethods, same, Ne.symm same]
    rw [source.mixins.install_distinct_commute_of_mem same methodMember
      fieldMember]

end Newspeak
