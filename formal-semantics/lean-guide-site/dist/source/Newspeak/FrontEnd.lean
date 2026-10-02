import Newspeak.SurfaceNodes
import Newspeak.NewspeakSurfaceActions
import Newspeak.StaticElaboration
import Newspeak.CoreValidity

namespace Newspeak

/-- The declaration-building phase is kept distinct from expression
    elaboration because it produces all finite Program indexes atomically. -/
structure ProgramDerivationServices where
  deriveProgram : SurfaceCompilationUnit → IdentificationOutput →
    Option (Program × CoreExpr)
  surfaceOK : SurfaceCompilationUnit → IdentificationOutput → Bool
  coreFuel : Nat

structure FrontEndResult where
  program : Program
  expression : CoreExpr
  retention : IdentityRetentionMap

/-- Exact composition of parse, semantic projection, stable identification,
    static checking, Program derivation, and the top-level restriction. -/
inductive FrontEndDerivation (grammar : PEGGrammar)
    (decoders : NewspeakLexicalDecoders)
    (derivation : ProgramDerivationServices)
    (retained : IdentityRetentionMap) (supply : IdentificationSupply)
    (source : SourceText) : FrontEndResult → Prop where
  | accepted {surface metadata identification program expression}
      (parsed : PEGParsesNewspeakUnit grammar decoders source surface metadata)
      (identified : identifySurfaceCompilationUnit retained supply surface =
        some identification)
      (surfaceValid : derivation.surfaceOK surface identification = true)
      (derived : derivation.deriveProgram surface identification =
        some (program, expression))
      (coreValid : AnnotatedCoreValid program expression derivation.coreFuel) :
      FrontEndDerivation grammar decoders derivation retained supply source
        { program := program
          expression := expression
          retention := identification.retention }

theorem FrontEndDerivation.deterministic
    {grammar : PEGGrammar} {decoders : NewspeakLexicalDecoders}
    {derivation : ProgramDerivationServices}
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {source : SourceText} {first second : FrontEndResult}
    (firstRun : FrontEndDerivation grammar decoders derivation retained supply
      source first)
    (secondRun : FrontEndDerivation grammar decoders derivation retained supply
      source second) :
    first = second := by
  cases firstRun with
  | accepted firstParsed firstIdentified firstValid firstDerived firstCoreValid =>
      cases secondRun with
      | accepted secondParsed secondIdentified secondValid secondDerived secondCoreValid =>
          have parsedEqual :=
            PEGParsesNewspeakUnit.deterministic firstParsed secondParsed
          cases parsedEqual.1
          cases parsedEqual.2
          have identificationEqual := identifySourceNodes_deterministic
            firstIdentified secondIdentified
          cases identificationEqual
          rw [firstDerived] at secondDerived
          have derivedEqual := Option.some.inj secondDerived
          cases derivedEqual
          rfl

theorem FrontEndDerivation.identitiesOK
    {grammar : PEGGrammar} {decoders : NewspeakLexicalDecoders}
    {derivation : ProgramDerivationServices}
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {source : SourceText} {result : FrontEndResult}
    (run : FrontEndDerivation grammar decoders derivation retained supply
      source result) :
    ∃ surface metadata identification,
      PEGParsesNewspeakUnit grammar decoders source surface metadata ∧
      identifySurfaceCompilationUnit retained supply surface = some identification ∧
      IdentifiedSourceNodesOK identification.nodes ∧
      result.retention = identification.retention := by
  cases run with
  | accepted parsed identified surfaceValid derived coreValid =>
      exact ⟨_, _, _, parsed, identified,
        identifySurfaceCompilationUnit_success_idsOK identified, rfl⟩

theorem FrontEndDerivation.topLevel
    {grammar : PEGGrammar} {decoders : NewspeakLexicalDecoders}
    {derivation : ProgramDerivationServices}
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {source : SourceText} {result : FrontEndResult}
    (run : FrontEndDerivation grammar decoders derivation retained supply
      source result) :
    result.program.TopLevelExpression result.expression := by
  cases run
  exact AnnotatedCoreValid.topLevelExpression ‹_›

end Newspeak
