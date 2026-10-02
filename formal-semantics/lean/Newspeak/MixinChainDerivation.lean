import Newspeak.ClassDerivation

namespace Newspeak

def deriveBodylessMixinChainProgram (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Option (Program × CoreExpr) := do
  let (complete, expression) ← deriveBodylessMixinChainInto config artifactConfig
    identification topElaborationContext .topOwner DerivedProgramImage.empty
    unit.declaration
  pure (complete.install config.baseProgram, expression)

def deriveProgramIncludingBodylessMixins (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Option (Program × CoreExpr) :=
  match unit.declaration with
  | .classDeclaration _ _ _ _ (.mixinChain _ _ _ _ none) =>
      deriveBodylessMixinChainProgram config artifactConfig unit identification
  | _ => deriveClassProgram config artifactConfig unit identification

def programDerivationServicesIncludingBodylessMixins
    (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat) :
    ProgramDerivationServices :=
  { deriveProgram :=
      deriveProgramIncludingBodylessMixins config artifactConfig
    surfaceOK := fun unit _ => surfaceCompilationUnitShapeOK unit
    coreFuel := coreFuel }

theorem deriveProgramIncludingBodylessMixins_deterministic
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {first second : Program × CoreExpr}
    (firstResult : deriveProgramIncludingBodylessMixins config artifactConfig unit
      identification = some first)
    (secondResult : deriveProgramIncludingBodylessMixins config artifactConfig unit
      identification = some second) : first = second := by
  rw [firstResult] at secondResult
  exact Option.some.inj secondResult

end Newspeak
