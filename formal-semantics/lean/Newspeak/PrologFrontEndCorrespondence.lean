import Newspeak.FrontEnd
import Newspeak.PEGCertificateSoundness
import Newspeak.PrologProgramDerivationCorrespondence

/-!
# Correspondence with the proof-facing Prolog front end

The Prolog clauses expose the same phase boundaries as Section 13: complete
PEG recognition, concrete-tree projection, Newspeak semantic actions, stable
identification, surface checking, Program derivation, and annotated-core
validation.  The grammar, decoder, and derivation services remain explicit
parameters.  Thus this bridge does not silently replace the reified language
services by a second parser or compiler.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologPEGGrammarWellFormed (grammar : PEGGrammar) : Prop where
  | witness : PEGGrammarWellFormed grammar →
      PrologPEGGrammarWellFormed grammar

theorem prologPEGGrammarWellFormed_iff {grammar : PEGGrammar} :
    PrologPEGGrammarWellFormed grammar ↔ PEGGrammarWellFormed grammar := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologPEGParsesNewspeakUnit (grammar : PEGGrammar)
    (decoders : NewspeakLexicalDecoders) (source : SourceText) :
    SurfaceCompilationUnit → List SurfaceMetadata → Prop where
  | parsed {unit : SurfaceCompilationUnit} {metadata : List SurfaceMetadata} :
      PrologPEGGrammarWellFormed grammar →
      PrologPEGParsesAST grammar (newspeakSurfaceSemantics decoders) source
        (.compilationUnit unit) metadata →
      PrologPEGParsesNewspeakUnit grammar decoders source unit metadata

theorem prologPEGParsesNewspeakUnit_iff {grammar decoders source unit metadata} :
    PrologPEGParsesNewspeakUnit grammar decoders source unit metadata ↔
      PEGParsesNewspeakUnit grammar decoders source unit metadata := by
  constructor
  · intro derivation
    cases derivation with
    | parsed wellFormed parsed =>
        exact ⟨prologPEGGrammarWellFormed_iff.mp wellFormed,
          prologPEGParsesAST_iff.mp parsed⟩
  · rintro ⟨wellFormed, parsed⟩
    exact .parsed (prologPEGGrammarWellFormed_iff.mpr wellFormed)
      (prologPEGParsesAST_iff.mpr parsed)

inductive PrologIdentifiedSourceNodesOK (identification : IdentificationOutput) :
    Prop where
  | witness : IdentifiedSourceNodesOK identification.nodes →
      PrologIdentifiedSourceNodesOK identification

theorem prologIdentifiedSourceNodesOK_iff {identification} :
    PrologIdentifiedSourceNodesOK identification ↔
      IdentifiedSourceNodesOK identification.nodes := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

theorem prologSurfaceIdentification_idsOK
    {retained supply unit identification}
    (identified : PrologSurfaceIdentification retained supply unit identification) :
    PrologIdentifiedSourceNodesOK identification :=
  prologIdentifiedSourceNodesOK_iff.mpr
    (identifySurfaceCompilationUnit_success_idsOK
      (prologSurfaceIdentification_iff.mp identified))

inductive PrologSurfaceCompilationUnitValid
    (derivation : ProgramDerivationServices) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Prop where
  | witness : derivation.surfaceOK unit identification = true →
      PrologSurfaceCompilationUnitValid derivation unit identification

theorem prologSurfaceCompilationUnitValid_iff
    {derivation unit identification} :
    PrologSurfaceCompilationUnitValid derivation unit identification ↔
      derivation.surfaceOK unit identification = true := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologDerivedAnnotatedProgram
    (derivation : ProgramDerivationServices) (unit : SurfaceCompilationUnit)
    (identification : IdentificationOutput) : Program → CoreExpr → Prop where
  | result {program : Program} {expression : CoreExpr} :
      derivation.deriveProgram unit identification = some (program, expression) →
      PrologDerivedAnnotatedProgram derivation unit identification
        program expression

theorem prologDerivedAnnotatedProgram_iff
    {derivation unit identification program expression} :
    PrologDerivedAnnotatedProgram derivation unit identification
      program expression ↔
      derivation.deriveProgram unit identification = some (program, expression) := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

theorem prologCompleteClassProgram_services_iff
    {config : DirectDerivationConfig}
    {artifactConfig : EmbeddedArtifactConfig} {coreFuel : Nat}
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {program : Program} {expression : CoreExpr} :
    PrologDerivedAnnotatedProgram
        (completeClassProgramDerivationServices config artifactConfig coreFuel)
        unit identification program expression ↔
      PrologDeriveCompleteClassProgram config artifactConfig unit identification
        (program, expression) := by
  rw [prologDerivedAnnotatedProgram_iff,
    prologDeriveCompleteClassProgram_iff]
  rfl

inductive PrologAnnotatedCoreCheck (program : Program) (expression : CoreExpr)
    (fuel : Nat) : Prop where
  | checked : annotatedCoreValidCheck program expression fuel = true →
      PrologAnnotatedCoreCheck program expression fuel

theorem prologAnnotatedCoreCheck_iff {program expression fuel} :
    PrologAnnotatedCoreCheck program expression fuel ↔
      annotatedCoreValidCheck program expression fuel = true := by
  constructor <;> intro premise
  · cases premise with | checked proof => exact proof
  · exact .checked premise

theorem PrologAnnotatedCoreCheck.sound {program expression fuel}
    (checked : PrologAnnotatedCoreCheck program expression fuel) :
    AnnotatedCoreValid program expression fuel :=
  annotatedCoreValidCheck_sound (prologAnnotatedCoreCheck_iff.mp checked)

inductive PrologAnnotatedCoreValid (program : Program) (expression : CoreExpr)
    (fuel : Nat) : Prop where
  | witness : AnnotatedCoreValid program expression fuel →
      PrologAnnotatedCoreValid program expression fuel

theorem prologAnnotatedCoreValid_iff {program expression fuel} :
    PrologAnnotatedCoreValid program expression fuel ↔
      AnnotatedCoreValid program expression fuel := by
  constructor <;> intro premise
  · cases premise with | witness proof => exact proof
  · exact .witness premise

inductive PrologFrontEndDerivation (grammar : PEGGrammar)
    (decoders : NewspeakLexicalDecoders)
    (derivation : ProgramDerivationServices)
    (retained : IdentityRetentionMap) (supply : IdentificationSupply)
    (source : SourceText) : FrontEndResult → Prop where
  | accepted {unit metadata identification program expression} :
      PrologPEGParsesNewspeakUnit grammar decoders source unit metadata →
      PrologSurfaceIdentification retained supply unit identification →
      PrologSurfaceCompilationUnitValid derivation unit identification →
      PrologDerivedAnnotatedProgram derivation unit identification
        program expression →
      PrologAnnotatedCoreValid program expression derivation.coreFuel →
      PrologFrontEndDerivation grammar decoders derivation retained supply source
        { program := program
          expression := expression
          retention := identification.retention }

theorem prologFrontEndDerivation_iff
    {grammar : PEGGrammar} {decoders : NewspeakLexicalDecoders}
    {derivation : ProgramDerivationServices}
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {source : SourceText} {result : FrontEndResult} :
    PrologFrontEndDerivation grammar decoders derivation retained supply source
      result ↔
      FrontEndDerivation grammar decoders derivation retained supply source
        result := by
  constructor
  · intro run
    cases run with
    | accepted parsed identified surfaceValid derived coreValid =>
        exact .accepted
          (prologPEGParsesNewspeakUnit_iff.mp parsed)
          (prologSurfaceIdentification_iff.mp identified)
          (prologSurfaceCompilationUnitValid_iff.mp surfaceValid)
          (prologDerivedAnnotatedProgram_iff.mp derived)
          (prologAnnotatedCoreValid_iff.mp coreValid)
  · intro run
    cases run with
    | accepted parsed identified surfaceValid derived coreValid =>
        exact .accepted
          (prologPEGParsesNewspeakUnit_iff.mpr parsed)
          (prologSurfaceIdentification_iff.mpr identified)
          (prologSurfaceCompilationUnitValid_iff.mpr surfaceValid)
          (prologDerivedAnnotatedProgram_iff.mpr derived)
          (prologAnnotatedCoreValid_iff.mpr coreValid)

theorem PrologFrontEndDerivation.deterministic
    {grammar : PEGGrammar} {decoders : NewspeakLexicalDecoders}
    {derivation : ProgramDerivationServices}
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {source : SourceText} {first second : FrontEndResult}
    (firstRun : PrologFrontEndDerivation grammar decoders derivation retained
      supply source first)
    (secondRun : PrologFrontEndDerivation grammar decoders derivation retained
      supply source second) :
    first = second :=
  FrontEndDerivation.deterministic
    (prologFrontEndDerivation_iff.mp firstRun)
    (prologFrontEndDerivation_iff.mp secondRun)

end PrologBridge
end Newspeak
