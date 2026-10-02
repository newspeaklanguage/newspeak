import Newspeak.StructuralArtifactDerivation

namespace Newspeak

def deriveBodiedMixinChainImage (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (context : ElaborationContext)
    (ownerKind : ClassOwner) (image : DerivedProgramImage)
    (declaration : SurfaceDeclaration) :
    Option (DerivedProgramImage × CoreExpr) := do
  let (.classDeclaration span name factorySelector factoryFormals
    (.mixinChain inheritanceSpan baseReceiver baseInitializer additional
      (some classStructure))) := declaration | none
  let directDeclaration := SurfaceDeclaration.classDeclaration span name
    factorySelector factoryFormals
    (.explicitInheritance inheritanceSpan baseReceiver baseInitializer
      classStructure)
  let (directImage, directExpression) ← deriveClassDeclarationIntoWithFuel
    config artifactConfig identification artifactConfig.fuel context ownerKind
    image directDeclaration
  let (.classBody classIdentity baseCore) := directExpression | none
  let enclosing ← declarationIdAt identification span "classDeclaration"
  let (foldedImage, foldedCore, finalInitializer) ←
    foldAnonymousApplications config identification enclosing ownerKind context 1
      directImage baseCore baseInitializer additional
  let services := directElaborationServices config identification
  let finalMessage ← elaborateMessageTemplate services context finalInitializer
  let complete ← foldedImage.replaceClassBodySuperclassMessage classIdentity
    finalMessage
  pure (complete, .classBody classIdentity foldedCore)

def deriveBodiedMixinChainProgram (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Option (Program × CoreExpr) := do
  let (image, expression) ← deriveBodiedMixinChainImage config artifactConfig
    identification topElaborationContext .topOwner DerivedProgramImage.empty
    unit.declaration
  let complete ← deriveStructuralClassDeclarationContents config artifactConfig
    identification topElaborationContext image unit.declaration
  pure (complete.install config.baseProgram, expression)

def deriveCompleteClassProgram (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Option (Program × CoreExpr) :=
  match unit.declaration with
  | .classDeclaration _ _ _ _ (.mixinChain _ _ _ _ none) =>
      deriveBodylessMixinChainProgram config artifactConfig unit identification
  | .classDeclaration _ _ _ _ (.mixinChain _ _ _ _ (some _)) =>
      deriveBodiedMixinChainProgram config artifactConfig unit identification
  | _ => deriveClassProgramWithStructuralArtifacts config artifactConfig unit
      identification

def completeClassProgramDerivationServices (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat) :
    ProgramDerivationServices :=
  { deriveProgram := deriveCompleteClassProgram config artifactConfig
    surfaceOK := fun unit _ => surfaceCompilationUnitShapeOK unit
    coreFuel := coreFuel }

theorem deriveBodiedMixinChainProgram_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {first second : Program × CoreExpr}
    (firstResult : deriveBodiedMixinChainProgram config artifactConfig unit
      identification = some first)
    (secondResult : deriveBodiedMixinChainProgram config artifactConfig unit
      identification = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

theorem deriveCompleteClassProgram_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {first second : Program × CoreExpr}
    (firstResult : deriveCompleteClassProgram config artifactConfig unit
      identification = some first)
    (secondResult : deriveCompleteClassProgram config artifactConfig unit
      identification = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
