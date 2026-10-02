import Newspeak.BodiedMixinDerivation

namespace Newspeak

def stringsDistinct : List String → Bool
  | [] => true
  | name :: remaining =>
      !(remaining.contains name) && stringsDistinct remaining

def declarationNames (declarations : List SurfaceDeclaration) : List String :=
  declarations.filterMap surfaceDeclarationName

def activationDeclarationsOK (formals : List SurfaceDeclaration)
    (locals : List SurfaceSlotGroup) : Bool :=
  stringsDistinct (declarationNames
    (formals ++ surfaceGroupsDeclarations locals))

def inducedSelectors : SurfaceDeclaration → List String
  | .slot _ _ name mutability _ | .lazySlot _ _ name mutability _ =>
      match mutability with
      | .immutable => [name]
      | .mutable => [name, name ++ ":"]
  | .method _ _ selector _ _ _ => [selector.spelling]
  | .nestedClass _ _ (.classDeclaration _ name _ _ _) => [name]
  | _ => []

def declarationsInducedSelectors (declarations : List SurfaceDeclaration) :
    List String :=
  declarations.flatMap inducedSelectors

mutual
  partial def surfaceStaticExpressionOK (isUnary : Selector → Bool) :
      SurfaceExpression → Bool
    | .atom _ _ | .identifier _ _ | .selfValue _ | .outer _ _
    | .superValue _ => true
    | .parenthesized _ expression | .setter _ _ expression =>
        surfaceStaticExpressionOK isUnary expression
    | .implicitSend _ selector arguments =>
        selectorArity isUnary selector == arguments.length &&
          arguments.all (surfaceStaticExpressionOK isUnary)
    | .messageSend _ receiver selector arguments
    | .eventualSend _ receiver selector arguments =>
        surfaceStaticExpressionOK isUnary receiver &&
          selectorArity isUnary selector == arguments.length &&
          arguments.all (surfaceStaticExpressionOK isUnary)
    | .cascade _ receiver initial subsequent =>
        surfaceStaticExpressionOK isUnary receiver &&
          (initial ++ subsequent).all (surfaceStaticClauseOK isUnary)
    | .tuple _ elements => elements.all (surfaceStaticExpressionOK isUnary)
    | .pattern _ pattern => surfaceStaticPatternOK isUnary pattern
    | .closure _ formals locals body =>
        activationDeclarationsOK formals locals &&
          formals.all (surfaceStaticDeclarationOK isUnary) &&
          locals.all (surfaceStaticSlotGroupOK isUnary) &&
          body.all (surfaceStaticStatementOK isUnary)
    | .objectLiteral _ header => surfaceStaticObjectHeaderOK isUnary header
    | .classExpression _ declaration =>
        surfaceStaticDeclarationOK isUnary declaration
    | .sequence _ statements => statements.all (surfaceStaticStatementOK isUnary)

  partial def surfaceStaticPatternOK (isUnary : Selector → Bool) :
      SurfacePattern → Bool
    | .wildcard _ | .variable _ _ => true
    | .literal _ expression => surfaceStaticExpressionOK isUnary expression
    | .nested _ pattern => surfaceStaticPatternOK isUnary pattern
    | .keyword _ pairs => pairs.all fun pair =>
        match pair.2 with
        | none => true
        | some pattern => surfaceStaticPatternOK isUnary pattern

  partial def surfaceStaticClauseOK (isUnary : Selector → Bool) :
      SurfaceClause → Bool
    | .clause _ selector arguments =>
        selectorArity isUnary selector == arguments.length &&
          arguments.all (surfaceStaticExpressionOK isUnary)

  partial def surfaceStaticStatementOK (isUnary : Selector → Bool) :
      SurfaceStatement → Bool
    | .expression _ expression | .returnStatement _ expression =>
        surfaceStaticExpressionOK isUnary expression

  partial def surfaceStaticDeclarationOK (isUnary : Selector → Bool) :
      SurfaceDeclaration → Bool
    | .formal _ _ => true
    | .slot _ _ _ _ initializer =>
        match initializer with
        | none => true
        | some expression => surfaceStaticExpressionOK isUnary expression
    | .lazySlot _ _ _ _ initializer =>
        surfaceStaticExpressionOK isUnary initializer
    | .method _ _ selector formals locals body =>
        selectorArity isUnary selector == formals.length &&
          activationDeclarationsOK formals locals &&
          formals.all (surfaceStaticDeclarationOK isUnary) &&
          locals.all (surfaceStaticSlotGroupOK isUnary) &&
          body.all (surfaceStaticStatementOK isUnary)
    | .nestedClass _ _ declaration => surfaceStaticDeclarationOK isUnary declaration
    | .classDeclaration _ _ factorySelector factoryFormals inheritance =>
        selectorArity isUnary factorySelector == factoryFormals.length &&
          stringsDistinct (declarationNames factoryFormals) &&
          factoryFormals.all (surfaceStaticDeclarationOK isUnary) &&
          surfaceStaticInheritanceOK isUnary factorySelector inheritance

  partial def surfaceStaticSlotGroupOK (isUnary : Selector → Bool) :
      SurfaceSlotGroup → Bool
    | .sequential _ declarations | .simultaneous _ declarations =>
        stringsDistinct (declarationNames declarations) &&
          declarations.all (surfaceStaticDeclarationOK isUnary)

  partial def surfaceStaticClassStructureOK (isUnary : Selector → Bool)
      (factorySelector : Selector) : SurfaceClassStructure → Bool
    | .structure _ headerLocals headerStatements instanceDeclarations
        classDeclarations =>
      let headerDeclarations := headerLocals.map surfaceGroupDeclarations |>.getD []
      stringsDistinct (declarationNames
          (headerDeclarations ++ instanceDeclarations ++ classDeclarations)) &&
        stringsDistinct (declarationsInducedSelectors
          (headerDeclarations ++ instanceDeclarations)) &&
        stringsDistinct (factorySelector.spelling ::
          declarationsInducedSelectors classDeclarations) &&
        (match headerLocals with
         | none => true
         | some group => surfaceStaticSlotGroupOK isUnary group) &&
        headerStatements.all (surfaceStaticStatementOK isUnary) &&
        instanceDeclarations.all (surfaceStaticDeclarationOK isUnary) &&
        classDeclarations.all (surfaceStaticDeclarationOK isUnary)

  partial def surfaceStaticObjectHeaderOK (isUnary : Selector → Bool) :
      SurfaceObjectHeader → Bool
    | .implicitHeader _ body =>
        surfaceStaticClassStructureOK isUnary ⟨"new"⟩ body
    | .explicitHeader _ receiver initializer body =>
        surfaceStaticExpressionOK isUnary receiver &&
          surfaceStaticClauseOK isUnary initializer &&
          surfaceStaticClassStructureOK isUnary ⟨"new"⟩ body

  partial def surfaceStaticInheritanceOK (isUnary : Selector → Bool)
      (factorySelector : Selector) : SurfaceInheritance → Bool
    | .defaultInheritance _ body =>
        surfaceStaticClassStructureOK isUnary factorySelector body
    | .explicitInheritance _ receiver initializer body =>
        surfaceStaticExpressionOK isUnary receiver &&
          surfaceStaticClauseOK isUnary initializer &&
          surfaceStaticClassStructureOK isUnary factorySelector body
    | .mixinChain _ receiver initializer additional body =>
        surfaceStaticExpressionOK isUnary receiver &&
          surfaceStaticClauseOK isUnary initializer &&
          additional.all (fun head =>
            surfaceStaticExpressionOK isUnary head.receiver &&
              surfaceStaticClauseOK isUnary head.initializer) &&
          (match body with
           | none => true
           | some classStructure =>
               surfaceStaticClassStructureOK isUnary factorySelector
                 classStructure)
end

def completeSurfaceStaticOK (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat)
    (unit : SurfaceCompilationUnit) (identification : IdentificationOutput) : Bool :=
  surfaceCompilationUnitShapeOK unit &&
    surfaceStaticDeclarationOK config.isUnarySelector unit.declaration &&
    match deriveCompleteClassProgram config artifactConfig unit identification with
    | none => false
    | some (program, expression) =>
        annotatedCoreValidCheck program expression coreFuel

def checkedCompleteProgramDerivationServices
    (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat) :
    ProgramDerivationServices :=
  { deriveProgram := deriveCompleteClassProgram config artifactConfig
    surfaceOK := completeSurfaceStaticOK config artifactConfig coreFuel
    coreFuel := coreFuel }

theorem completeSurfaceStaticOK_shape
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {coreFuel : Nat} {unit : SurfaceCompilationUnit}
    {identification : IdentificationOutput}
    (valid : completeSurfaceStaticOK config artifactConfig coreFuel unit
      identification = true) : surfaceCompilationUnitShapeOK unit = true := by
  simp [completeSurfaceStaticOK] at valid
  exact valid.1.1

theorem completeSurfaceStaticOK_static
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {coreFuel : Nat} {unit : SurfaceCompilationUnit}
    {identification : IdentificationOutput}
    (valid : completeSurfaceStaticOK config artifactConfig coreFuel unit
      identification = true) :
    surfaceStaticDeclarationOK config.isUnarySelector unit.declaration = true := by
  unfold completeSurfaceStaticOK at valid
  split at valid <;> simp_all

theorem completeSurfaceStaticOK_derives
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {coreFuel : Nat} {unit : SurfaceCompilationUnit}
    {identification : IdentificationOutput}
    (valid : completeSurfaceStaticOK config artifactConfig coreFuel unit
      identification = true) : ∃ result, deriveCompleteClassProgram config artifactConfig unit
      identification = some result := by
  unfold completeSurfaceStaticOK at valid
  split at valid <;> simp_all

theorem completeSurfaceStaticOK_coreValid
    {config : DirectDerivationConfig} {artifactConfig : EmbeddedArtifactConfig}
    {coreFuel : Nat} {unit : SurfaceCompilationUnit}
    {identification : IdentificationOutput} {program : Program}
    {expression : CoreExpr}
    (valid : completeSurfaceStaticOK config artifactConfig coreFuel unit
      identification = true)
    (derived : deriveCompleteClassProgram config artifactConfig unit
      identification = some (program, expression)) :
    AnnotatedCoreValid program expression coreFuel := by
  unfold completeSurfaceStaticOK at valid
  rw [derived] at valid
  simp only [Bool.and_eq_true] at valid
  exact annotatedCoreValidCheck_sound valid.2

end Newspeak
