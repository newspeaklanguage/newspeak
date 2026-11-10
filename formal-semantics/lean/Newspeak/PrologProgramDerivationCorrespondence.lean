import Newspeak.BodiedMixinDerivation
import Newspeak.PrologDeclarationCorrespondence

/-!
# Correspondence for class, mixin, object, and Program derivation

This module pins the outer source-to-Program construction graphs to their Lean
implementations and gives the final class-program choice a structural reading.
The very large class/object image builders remain decomposed into separately
named graph relations, so later constructor-level refinements can replace one
boundary at a time without changing the final theorem.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologDirectClassStructure (inheritance : SurfaceInheritance) :
    SurfaceClassStructure → Prop where
  | result {classStructure : SurfaceClassStructure} :
      directClassStructure inheritance = some classStructure →
      PrologDirectClassStructure inheritance classStructure

theorem prologDirectClassStructure_iff {inheritance classStructure} :
    PrologDirectClassStructure inheritance classStructure ↔
      directClassStructure inheritance = some classStructure := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDirectSuperclassSyntax (inheritance : SurfaceInheritance) :
    SuperclassSyntax → Prop where
  | result {superclassSyntax : SuperclassSyntax} :
      directSuperclassSyntax inheritance = superclassSyntax →
      PrologDirectSuperclassSyntax inheritance superclassSyntax

theorem prologDirectSuperclassSyntax_iff {inheritance superclassSyntax} :
    PrologDirectSuperclassSyntax inheritance superclassSyntax ↔
      directSuperclassSyntax inheritance = superclassSyntax := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDirectSuperclassMessage (services : ElaborationServices)
    (context : ElaborationContext) (inheritance : SurfaceInheritance) :
    MessageTemplate → Prop where
  | result {message : MessageTemplate} :
      directSuperclassMessage services context inheritance = some message →
      PrologDirectSuperclassMessage services context inheritance message

theorem prologDirectSuperclassMessage_iff
    {services context inheritance message} :
    PrologDirectSuperclassMessage services context inheritance message ↔
      directSuperclassMessage services context inheritance = some message := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDirectSuperclassExpression (services : ElaborationServices)
    (context : ElaborationContext) (inheritance : SurfaceInheritance) :
    CoreExpr → Prop where
  | result {expression : CoreExpr} :
      directSuperclassExpression services context inheritance = some expression →
      PrologDirectSuperclassExpression services context inheritance expression

theorem prologDirectSuperclassExpression_iff
    {services context inheritance expression} :
    PrologDirectSuperclassExpression services context inheritance expression ↔
      directSuperclassExpression services context inheritance = some expression := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologObjectLiteralOwnerFromContext
    (context : ElaborationContext) : ClassOwner → Prop where
  | result {owner : ClassOwner} :
      objectLiteralOwnerFromContext context = owner →
      PrologObjectLiteralOwnerFromContext context owner

theorem prologObjectLiteralOwnerFromContext_iff {context owner} :
    PrologObjectLiteralOwnerFromContext context owner ↔
      objectLiteralOwnerFromContext context = owner := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologObjectHeaderStructure (header : SurfaceObjectHeader) :
    SurfaceClassStructure → Prop where
  | result {classStructure : SurfaceClassStructure} :
      objectHeaderStructure header = classStructure →
      PrologObjectHeaderStructure header classStructure

theorem prologObjectHeaderStructure_iff {header classStructure} :
    PrologObjectHeaderStructure header classStructure ↔
      objectHeaderStructure header = classStructure := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologObjectHeaderSuperclassSyntax (header : SurfaceObjectHeader) :
    SuperclassSyntax → Prop where
  | result {superclassSyntax : SuperclassSyntax} :
      objectHeaderSuperclassSyntax header = superclassSyntax →
      PrologObjectHeaderSuperclassSyntax header superclassSyntax

theorem prologObjectHeaderSuperclassSyntax_iff {header superclassSyntax} :
    PrologObjectHeaderSuperclassSyntax header superclassSyntax ↔
      objectHeaderSuperclassSyntax header = superclassSyntax := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologObjectHeaderSuperclass (services : ElaborationServices)
    (context : ElaborationContext) (header : SurfaceObjectHeader) :
    CoreExpr → Prop where
  | result {superclass : CoreExpr} :
      objectHeaderSuperclass services context header = some superclass →
      PrologObjectHeaderSuperclass services context header superclass

theorem prologObjectHeaderSuperclass_iff
    {services context header superclass} :
    PrologObjectHeaderSuperclass services context header superclass ↔
      objectHeaderSuperclass services context header = some superclass := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologObjectHeaderSuperclassMessage (services : ElaborationServices)
    (context : ElaborationContext) (header : SurfaceObjectHeader) :
    MessageTemplate → Prop where
  | result {message : MessageTemplate} :
      objectHeaderSuperclassMessage services context header = some message →
      PrologObjectHeaderSuperclassMessage services context header message

theorem prologObjectHeaderSuperclassMessage_iff
    {services context header message} :
    PrologObjectHeaderSuperclassMessage services context header message ↔
      objectHeaderSuperclassMessage services context header = some message := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologElaborateMessageTemplate (services : ElaborationServices)
    (context : ElaborationContext) (clause : SurfaceClause) :
    MessageTemplate → Prop where
  | result {message : MessageTemplate} :
      elaborateMessageTemplate services context clause = some message →
      PrologElaborateMessageTemplate services context clause message

theorem prologElaborateMessageTemplate_iff
    {services context clause message} :
    PrologElaborateMessageTemplate services context clause message ↔
      elaborateMessageTemplate services context clause = some message := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveAnonymousApplication (config : DirectDerivationConfig)
    (identification : IdentificationOutput) (enclosing : DeclId)
    (position : Nat) (ownerKind : ClassOwner)
    (context : ElaborationContext) (image : DerivedProgramImage)
    (superclass : CoreExpr) (superclassInitializer : SurfaceClause)
    (head : SurfaceInheritanceHead) :
    DerivedProgramImage × CoreExpr × SurfaceClause → Prop where
  | result {output : DerivedProgramImage × CoreExpr × SurfaceClause} :
      deriveAnonymousApplication config identification enclosing position
        ownerKind context image superclass superclassInitializer head =
          some output →
      PrologDeriveAnonymousApplication config identification enclosing position
        ownerKind context image superclass superclassInitializer head output

theorem prologDeriveAnonymousApplication_iff
    {config identification enclosing position ownerKind context image superclass
      superclassInitializer head output} :
    PrologDeriveAnonymousApplication config identification enclosing position
      ownerKind context image superclass superclassInitializer head output ↔
      deriveAnonymousApplication config identification enclosing position
        ownerKind context image superclass superclassInitializer head =
          some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologFoldAnonymousApplications (config : DirectDerivationConfig)
    (identification : IdentificationOutput) (enclosing : DeclId)
    (ownerKind : ClassOwner) (context : ElaborationContext) (position : Nat)
    (image : DerivedProgramImage) (superclass : CoreExpr)
    (initializer : SurfaceClause) (heads : List SurfaceInheritanceHead) :
    DerivedProgramImage × CoreExpr × SurfaceClause → Prop where
  | result {output : DerivedProgramImage × CoreExpr × SurfaceClause} :
      foldAnonymousApplications config identification enclosing ownerKind context
        position image superclass initializer heads = some output →
      PrologFoldAnonymousApplications config identification enclosing ownerKind
        context position image superclass initializer heads output

theorem prologFoldAnonymousApplications_iff
    {config identification enclosing ownerKind context position image superclass
      initializer heads output} :
    PrologFoldAnonymousApplications config identification enclosing ownerKind
      context position image superclass initializer heads output ↔
      foldAnonymousApplications config identification enclosing ownerKind context
        position image superclass initializer heads = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveBodylessMixinChainInto
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (context : ElaborationContext)
    (ownerKind : ClassOwner) (image : DerivedProgramImage)
    (declaration : SurfaceDeclaration) : DerivedProgramImage × CoreExpr → Prop where
  | result {output : DerivedProgramImage × CoreExpr} :
      deriveBodylessMixinChainInto config artifactConfig identification context
        ownerKind image declaration = some output →
      PrologDeriveBodylessMixinChainInto config artifactConfig identification
        context ownerKind image declaration output

theorem prologDeriveBodylessMixinChainInto_iff
    {config artifactConfig identification context ownerKind image declaration
      output} :
    PrologDeriveBodylessMixinChainInto config artifactConfig identification
      context ownerKind image declaration output ↔
      deriveBodylessMixinChainInto config artifactConfig identification context
        ownerKind image declaration = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveClassDeclarationIntoWithFuel
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (fuel : Nat)
    (context : ElaborationContext) (ownerKind : ClassOwner)
    (image : DerivedProgramImage) (declaration : SurfaceDeclaration) :
    DerivedProgramImage × CoreExpr → Prop where
  | result {output : DerivedProgramImage × CoreExpr} :
      deriveClassDeclarationIntoWithFuel config artifactConfig identification fuel
        context ownerKind image declaration = some output →
      PrologDeriveClassDeclarationIntoWithFuel config artifactConfig identification
        fuel context ownerKind image declaration output

theorem prologDeriveClassDeclarationIntoWithFuel_iff
    {config artifactConfig identification fuel context ownerKind image declaration
      output} :
    PrologDeriveClassDeclarationIntoWithFuel config artifactConfig identification
      fuel context ownerKind image declaration output ↔
      deriveClassDeclarationIntoWithFuel config artifactConfig identification fuel
        context ownerKind image declaration = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveNestedClassDeclarationsWithFuel
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (fuel : Nat)
    (context : ElaborationContext) (owner : ClassBodyDecl) (mixin : MixinId)
    (image : DerivedProgramImage) (declarations : List SurfaceDeclaration) :
    DerivedProgramImage → Prop where
  | result {output : DerivedProgramImage} :
      deriveNestedClassDeclarationsWithFuel config artifactConfig identification
        fuel context owner mixin image declarations = some output →
      PrologDeriveNestedClassDeclarationsWithFuel config artifactConfig
        identification fuel context owner mixin image declarations output

theorem prologDeriveNestedClassDeclarationsWithFuel_iff
    {config artifactConfig identification fuel context owner mixin image
      declarations output} :
    PrologDeriveNestedClassDeclarationsWithFuel config artifactConfig
      identification fuel context owner mixin image declarations output ↔
      deriveNestedClassDeclarationsWithFuel config artifactConfig identification
        fuel context owner mixin image declarations = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveObjectLiteralInto (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (context : ElaborationContext)
    (image : DerivedProgramImage) (span : SourceSpan)
    (header : SurfaceObjectHeader) : DerivedProgramImage × CoreExpr → Prop where
  | result {output : DerivedProgramImage × CoreExpr} :
      deriveObjectLiteralInto config artifactConfig identification context image
        span header = some output →
      PrologDeriveObjectLiteralInto config artifactConfig identification context
        image span header output

theorem prologDeriveObjectLiteralInto_iff
    {config artifactConfig identification context image span header output} :
    PrologDeriveObjectLiteralInto config artifactConfig identification context
      image span header output ↔
      deriveObjectLiteralInto config artifactConfig identification context image
        span header = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveStructuralClassDeclarationContents
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (identification : IdentificationOutput) (context : ElaborationContext)
    (image : DerivedProgramImage) (declaration : SurfaceDeclaration) :
    DerivedProgramImage → Prop where
  | result {output : DerivedProgramImage} :
      deriveStructuralClassDeclarationContents config artifactConfig
        identification context image declaration = some output →
      PrologDeriveStructuralClassDeclarationContents config artifactConfig
        identification context image declaration output

theorem prologDeriveStructuralClassDeclarationContents_iff
    {config artifactConfig identification context image declaration output} :
    PrologDeriveStructuralClassDeclarationContents config artifactConfig
      identification context image declaration output ↔
      deriveStructuralClassDeclarationContents config artifactConfig
        identification context image declaration = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveBodylessMixinChainProgram
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) :
    Program × CoreExpr → Prop where
  | result {output : Program × CoreExpr} :
      deriveBodylessMixinChainProgram config artifactConfig unit identification =
        some output →
      PrologDeriveBodylessMixinChainProgram config artifactConfig unit
        identification output

theorem prologDeriveBodylessMixinChainProgram_iff
    {config artifactConfig unit identification output} :
    PrologDeriveBodylessMixinChainProgram config artifactConfig unit
      identification output ↔
      deriveBodylessMixinChainProgram config artifactConfig unit identification =
        some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveBodiedMixinChainProgram
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) :
    Program × CoreExpr → Prop where
  | result {output : Program × CoreExpr} :
      deriveBodiedMixinChainProgram config artifactConfig unit identification =
        some output →
      PrologDeriveBodiedMixinChainProgram config artifactConfig unit
        identification output

theorem prologDeriveBodiedMixinChainProgram_iff
    {config artifactConfig unit identification output} :
    PrologDeriveBodiedMixinChainProgram config artifactConfig unit identification
      output ↔
      deriveBodiedMixinChainProgram config artifactConfig unit identification =
        some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveClassProgramWithStructuralArtifacts
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) :
    Program × CoreExpr → Prop where
  | result {output : Program × CoreExpr} :
      deriveClassProgramWithStructuralArtifacts config artifactConfig unit
        identification = some output →
      PrologDeriveClassProgramWithStructuralArtifacts config artifactConfig unit
        identification output

theorem prologDeriveClassProgramWithStructuralArtifacts_iff
    {config artifactConfig unit identification output} :
    PrologDeriveClassProgramWithStructuralArtifacts config artifactConfig unit
      identification output ↔
      deriveClassProgramWithStructuralArtifacts config artifactConfig unit
        identification = some output := by
  constructor <;> intro premise
  · cases premise with | result proof => exact proof
  · exact .result premise

inductive PrologDeriveCompleteClassProgram
    (config : DirectDerivationConfig) (artifactConfig : EmbeddedArtifactConfig)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) :
    Program × CoreExpr → Prop where
  | bodyless {span name selector formals inheritanceSpan receiver initializer
      additional output} :
      unit.declaration = .classDeclaration span name selector formals
        (.mixinChain inheritanceSpan receiver initializer additional none) →
      PrologDeriveBodylessMixinChainProgram config artifactConfig unit
        identification output →
      PrologDeriveCompleteClassProgram config artifactConfig unit identification
        output
  | bodied {span name selector formals inheritanceSpan receiver initializer
      additional body output} :
      unit.declaration = .classDeclaration span name selector formals
        (.mixinChain inheritanceSpan receiver initializer additional (some body)) →
      PrologDeriveBodiedMixinChainProgram config artifactConfig unit
        identification output →
      PrologDeriveCompleteClassProgram config artifactConfig unit identification
        output
  | ordinary {output} :
      (∀ span name selector formals inheritanceSpan receiver initializer
          additional body,
        unit.declaration ≠ .classDeclaration span name selector formals
          (.mixinChain inheritanceSpan receiver initializer additional body)) →
      PrologDeriveClassProgramWithStructuralArtifacts config artifactConfig unit
        identification output →
      PrologDeriveCompleteClassProgram config artifactConfig unit identification
        output

theorem prologDeriveCompleteClassProgram_iff
    {config artifactConfig unit identification output} :
    PrologDeriveCompleteClassProgram config artifactConfig unit identification
      output ↔
      deriveCompleteClassProgram config artifactConfig unit identification =
        some output := by
  constructor
  · intro derivation
    cases derivation with
    | bodyless shape run =>
        simp [deriveCompleteClassProgram, shape,
          prologDeriveBodylessMixinChainProgram_iff.mp run]
    | bodied shape run =>
        simp [deriveCompleteClassProgram, shape,
          prologDeriveBodiedMixinChainProgram_iff.mp run]
    | ordinary notMixin run =>
        cases declarationShape : unit.declaration with
        | classDeclaration span name selector formals inheritance =>
            cases inheritance with
            | mixinChain inheritanceSpan receiver initializer additional body =>
                exact (notMixin span name selector formals inheritanceSpan receiver
                  initializer additional body declarationShape).elim
            | defaultInheritance inheritanceSpan body =>
                simpa [deriveCompleteClassProgram, declarationShape] using
                  prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
            | explicitInheritance inheritanceSpan receiver initializer body =>
                simpa [deriveCompleteClassProgram, declarationShape] using
                  prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
        | formal span name =>
            simpa [deriveCompleteClassProgram, declarationShape] using
              prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
        | slot span access name mutability initializer =>
            simpa [deriveCompleteClassProgram, declarationShape] using
              prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
        | lazySlot span access name mutability initializer =>
            simpa [deriveCompleteClassProgram, declarationShape] using
              prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
        | method span access selector formals locals body =>
            simpa [deriveCompleteClassProgram, declarationShape] using
              prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
        | nestedClass span access declaration =>
            simpa [deriveCompleteClassProgram, declarationShape] using
              prologDeriveClassProgramWithStructuralArtifacts_iff.mp run
  · intro success
    cases declarationShape : unit.declaration with
      | classDeclaration span name selector formals inheritance =>
          cases inheritance with
          | mixinChain inheritanceSpan receiver initializer additional body =>
              cases body with
              | none =>
                  exact .bodyless declarationShape
                    (prologDeriveBodylessMixinChainProgram_iff.mpr
                      (by simpa [deriveCompleteClassProgram, declarationShape]
                        using success))
              | some body =>
                  exact .bodied declarationShape
                    (prologDeriveBodiedMixinChainProgram_iff.mpr
                      (by simpa [deriveCompleteClassProgram, declarationShape]
                        using success))
          | defaultInheritance inheritanceSpan body =>
              exact .ordinary (by intros; simp [declarationShape]) <|
                prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
                  by simpa [deriveCompleteClassProgram, declarationShape]
                    using success
          | explicitInheritance inheritanceSpan receiver initializer body =>
              exact .ordinary (by intros; simp [declarationShape]) <|
                prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
                  by simpa [deriveCompleteClassProgram, declarationShape]
                    using success
      | formal span name =>
          exact .ordinary (by intros; simp [declarationShape]) <|
            prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
              by simpa [deriveCompleteClassProgram, declarationShape] using success
      | slot span access name mutability initializer =>
          exact .ordinary (by intros; simp [declarationShape]) <|
            prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
              by simpa [deriveCompleteClassProgram, declarationShape] using success
      | lazySlot span access name mutability initializer =>
          exact .ordinary (by intros; simp [declarationShape]) <|
            prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
              by simpa [deriveCompleteClassProgram, declarationShape] using success
      | method span access selector formals locals body =>
          exact .ordinary (by intros; simp [declarationShape]) <|
            prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
              by simpa [deriveCompleteClassProgram, declarationShape] using success
      | nestedClass span access declaration =>
          exact .ordinary (by intros; simp [declarationShape]) <|
            prologDeriveClassProgramWithStructuralArtifacts_iff.mpr <|
              by simpa [deriveCompleteClassProgram, declarationShape] using success

theorem PrologDeriveCompleteClassProgram.deterministic
    {config artifactConfig unit identification first second}
    (firstRun : PrologDeriveCompleteClassProgram config artifactConfig unit
      identification first)
    (secondRun : PrologDeriveCompleteClassProgram config artifactConfig unit
      identification second) : first = second :=
  deriveCompleteClassProgram_deterministic
    (prologDeriveCompleteClassProgram_iff.mp firstRun)
    (prologDeriveCompleteClassProgram_iff.mp secondRun)

end PrologBridge
end Newspeak
