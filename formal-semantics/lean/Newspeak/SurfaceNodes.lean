import Newspeak.SourceIdentification
import Newspeak.SurfaceSyntax

namespace Newspeak

def sourceNodeKey (sourceUnit : String) (path : List Nat)
    (constructorKind : String) (declaredName : Option String := none) :
    SourceNodeKey :=
  { sourceUnit, path, constructorKind, declaredName }

def sourceExpressionNode (sourceUnit : String) (path : List Nat)
    (constructorKind : String) (span : Option SourceSpan := none) :
    UnidentifiedSourceNode :=
  ⟨sourceNodeKey sourceUnit path constructorKind, .expression,
    span.map fun value => (value.startOffset, value.endOffset)⟩

def sourceDeclarationNode (sourceUnit : String) (path : List Nat)
    (constructorKind : String) (declaredName : Option String := none)
    (span : Option SourceSpan := none) :
    UnidentifiedSourceNode :=
  ⟨sourceNodeKey sourceUnit path constructorKind declaredName, .declaration,
    span.map fun value => (value.startOffset, value.endOffset)⟩

def childSourcePath (path : List Nat) (index : Nat) : List Nat :=
  path ++ [index]

mutual
  partial def surfaceExpressionNodes (sourceUnit : String) (path : List Nat) :
      SurfaceExpression → List UnidentifiedSourceNode
    | .atom span _ => [sourceExpressionNode sourceUnit path "atom" (some span)]
    | .identifier span _ =>
        [sourceExpressionNode sourceUnit path "identifier" (some span)]
    | .selfValue span => [sourceExpressionNode sourceUnit path "self" (some span)]
    | .outer span _ => [sourceExpressionNode sourceUnit path "outer" (some span)]
    | .superValue span => [sourceExpressionNode sourceUnit path "super" (some span)]
    | .parenthesized span expression =>
        sourceExpressionNode sourceUnit path "parenthesized" (some span) ::
          surfaceExpressionNodes sourceUnit (childSourcePath path 0) expression
    | .implicitSend span _ arguments =>
        sourceExpressionNode sourceUnit path "implicitSend" (some span) ::
          surfaceExpressionListNodes sourceUnit path 0 arguments
    | .messageSend span receiver _ arguments =>
        sourceExpressionNode sourceUnit path "messageSend" (some span) ::
          (surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
            surfaceExpressionListNodes sourceUnit path 1 arguments)
    | .eventualSend span receiver _ arguments =>
        sourceExpressionNode sourceUnit path "eventualSend" (some span) ::
          (surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
            surfaceExpressionListNodes sourceUnit path 1 arguments)
    | .cascade span receiver initial subsequent =>
        sourceExpressionNode sourceUnit path "cascade" (some span) ::
          (surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
            surfaceClauseListNodes sourceUnit path 1 initial ++
            surfaceClauseListNodes sourceUnit path (initial.length + 1) subsequent)
    | .setter span _ expression =>
        sourceExpressionNode sourceUnit path "setter" (some span) ::
          surfaceExpressionNodes sourceUnit (childSourcePath path 0) expression
    | .tuple span elements =>
        sourceExpressionNode sourceUnit path "tuple" (some span) ::
          surfaceExpressionListNodes sourceUnit path 0 elements
    | .pattern span pattern =>
        sourceExpressionNode sourceUnit path "pattern" (some span) ::
          surfacePatternNodes sourceUnit (childSourcePath path 0) pattern
    | .closure span parameters locals body =>
        sourceExpressionNode sourceUnit path "closure" (some span) ::
          (surfaceDeclarationListNodes sourceUnit path 0 parameters ++
            surfaceSlotGroupListNodes sourceUnit path parameters.length locals ++
            surfaceStatementListNodes sourceUnit path
              (parameters.length + locals.length) body)
    | .objectLiteral span header =>
        sourceExpressionNode sourceUnit path "objectLiteral" (some span) ::
          surfaceObjectHeaderNodes sourceUnit (childSourcePath path 0) header
    | .classExpression span declaration =>
        sourceExpressionNode sourceUnit path "classExpression" (some span) ::
          surfaceDeclarationNodes sourceUnit (childSourcePath path 0) declaration
    | .sequence span statements =>
        sourceExpressionNode sourceUnit path "sequence" (some span) ::
          surfaceStatementListNodes sourceUnit path 0 statements

  partial def surfaceExpressionListNodes (sourceUnit : String)
      (path : List Nat) (firstIndex : Nat) :
      List SurfaceExpression → List UnidentifiedSourceNode
    | [] => []
    | expression :: remaining =>
        surfaceExpressionNodes sourceUnit (childSourcePath path firstIndex) expression ++
          surfaceExpressionListNodes sourceUnit path (firstIndex + 1) remaining

  partial def surfaceClauseNodes (sourceUnit : String) (path : List Nat) :
      SurfaceClause → List UnidentifiedSourceNode
    | .clause _ _ arguments =>
        surfaceExpressionListNodes sourceUnit path 0 arguments

  partial def surfaceClauseListNodes (sourceUnit : String) (path : List Nat)
      (firstIndex : Nat) : List SurfaceClause → List UnidentifiedSourceNode
    | [] => []
    | clause :: remaining =>
        surfaceClauseNodes sourceUnit (childSourcePath path firstIndex) clause ++
          surfaceClauseListNodes sourceUnit path (firstIndex + 1) remaining

  partial def surfacePatternNodes (sourceUnit : String) (path : List Nat) :
      SurfacePattern → List UnidentifiedSourceNode
    | .wildcard span =>
        [sourceExpressionNode sourceUnit path "wildcardPattern" (some span)]
    | .literal span expression =>
        sourceExpressionNode sourceUnit path "literalPattern" (some span) ::
          surfaceExpressionNodes sourceUnit (childSourcePath path 0) expression
    | .variable span _ =>
        [sourceExpressionNode sourceUnit path "variablePattern" (some span)]
    | .nested span pattern =>
        sourceExpressionNode sourceUnit path "nestedPattern" (some span) ::
          surfacePatternNodes sourceUnit (childSourcePath path 0) pattern
    | .keyword span pairs =>
        sourceExpressionNode sourceUnit path "keywordPattern" (some span) ::
          surfacePatternPairNodes sourceUnit path 0 pairs

  partial def surfacePatternPairNodes (sourceUnit : String) (path : List Nat)
      (firstIndex : Nat) :
      List (Selector × Option SurfacePattern) → List UnidentifiedSourceNode
    | [] => []
    | (_, none) :: remaining =>
        surfacePatternPairNodes sourceUnit path (firstIndex + 1) remaining
    | (_, some pattern) :: remaining =>
        surfacePatternNodes sourceUnit (childSourcePath path firstIndex) pattern ++
          surfacePatternPairNodes sourceUnit path (firstIndex + 1) remaining

  partial def surfaceStatementNodes (sourceUnit : String) (path : List Nat) :
      SurfaceStatement → List UnidentifiedSourceNode
    | .expression _ expression | .returnStatement _ expression =>
        surfaceExpressionNodes sourceUnit (childSourcePath path 0) expression

  partial def surfaceStatementListNodes (sourceUnit : String) (path : List Nat)
      (firstIndex : Nat) : List SurfaceStatement → List UnidentifiedSourceNode
    | [] => []
    | statement :: remaining =>
        surfaceStatementNodes sourceUnit (childSourcePath path firstIndex) statement ++
          surfaceStatementListNodes sourceUnit path (firstIndex + 1) remaining

  partial def surfaceDeclarationNodes (sourceUnit : String) (path : List Nat) :
      SurfaceDeclaration → List UnidentifiedSourceNode
    | .formal span name =>
        [sourceDeclarationNode sourceUnit path "formal" (some name) (some span)]
    | .slot span _ name _ initializer =>
        sourceDeclarationNode sourceUnit path "slot" (some name) (some span) ::
          surfaceOptionalExpressionNodes sourceUnit (childSourcePath path 0) initializer
    | .lazySlot span _ name _ initializer =>
        sourceDeclarationNode sourceUnit path "lazySlot" (some name) (some span) ::
          surfaceExpressionNodes sourceUnit (childSourcePath path 0) initializer
    | .method span _ selector formals locals body =>
        sourceDeclarationNode sourceUnit path "method" (some selector.spelling)
          (some span) ::
          (surfaceDeclarationListNodes sourceUnit path 0 formals ++
            surfaceSlotGroupListNodes sourceUnit path formals.length locals ++
            surfaceStatementListNodes sourceUnit path
              (formals.length + locals.length) body)
    | .nestedClass span _ declaration =>
        sourceDeclarationNode sourceUnit path "nestedClass" none (some span) ::
          surfaceDeclarationNodes sourceUnit (childSourcePath path 0) declaration
    | .classDeclaration span name _ factoryFormals inheritance =>
        sourceDeclarationNode sourceUnit path "classDeclaration" (some name)
          (some span) ::
          (surfaceDeclarationListNodes sourceUnit path 0 factoryFormals ++
            surfaceInheritanceNodes sourceUnit
              (childSourcePath path factoryFormals.length) inheritance)

  partial def surfaceOptionalExpressionNodes (sourceUnit : String)
      (path : List Nat) : Option SurfaceExpression → List UnidentifiedSourceNode
    | none => []
    | some expression => surfaceExpressionNodes sourceUnit path expression

  partial def surfaceDeclarationListNodes (sourceUnit : String)
      (path : List Nat) (firstIndex : Nat) :
      List SurfaceDeclaration → List UnidentifiedSourceNode
    | [] => []
    | declaration :: remaining =>
        surfaceDeclarationNodes sourceUnit (childSourcePath path firstIndex) declaration ++
          surfaceDeclarationListNodes sourceUnit path (firstIndex + 1) remaining

  partial def surfaceSlotGroupNodes (sourceUnit : String) (path : List Nat) :
      SurfaceSlotGroup → List UnidentifiedSourceNode
    | .sequential _ declarations | .simultaneous _ declarations =>
        surfaceDeclarationListNodes sourceUnit path 0 declarations

  partial def surfaceSlotGroupListNodes (sourceUnit : String)
      (path : List Nat) (firstIndex : Nat) :
      List SurfaceSlotGroup → List UnidentifiedSourceNode
    | [] => []
    | group :: remaining =>
        surfaceSlotGroupNodes sourceUnit (childSourcePath path firstIndex) group ++
          surfaceSlotGroupListNodes sourceUnit path (firstIndex + 1) remaining

  partial def surfaceClassStructureNodes (sourceUnit : String)
      (path : List Nat) : SurfaceClassStructure → List UnidentifiedSourceNode
    | .structure _ headerLocals headerStatements instanceDeclarations
        classDeclarations =>
        surfaceOptionalSlotGroupNodes sourceUnit (childSourcePath path 0)
          headerLocals ++
        surfaceStatementListNodes sourceUnit path 1 headerStatements ++
        surfaceDeclarationListNodes sourceUnit path
          (headerStatements.length + 1) instanceDeclarations ++
        surfaceDeclarationListNodes sourceUnit path
          (headerStatements.length + instanceDeclarations.length + 1)
          classDeclarations

  partial def surfaceOptionalSlotGroupNodes (sourceUnit : String)
      (path : List Nat) : Option SurfaceSlotGroup → List UnidentifiedSourceNode
    | none => []
    | some group => surfaceSlotGroupNodes sourceUnit path group

  partial def surfaceObjectHeaderNodes (sourceUnit : String) (path : List Nat) :
      SurfaceObjectHeader → List UnidentifiedSourceNode
    | .implicitHeader _ classStructure =>
        surfaceClassStructureNodes sourceUnit (childSourcePath path 0) classStructure
    | .explicitHeader _ receiver initializer classStructure =>
        surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
        surfaceClauseNodes sourceUnit (childSourcePath path 1) initializer ++
        surfaceClassStructureNodes sourceUnit (childSourcePath path 2) classStructure

  partial def surfaceInheritanceNodes (sourceUnit : String) (path : List Nat) :
      SurfaceInheritance → List UnidentifiedSourceNode
    | .defaultInheritance _ classStructure =>
        surfaceClassStructureNodes sourceUnit (childSourcePath path 0) classStructure
    | .explicitInheritance _ receiver initializer classStructure =>
        surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
        surfaceClauseNodes sourceUnit (childSourcePath path 1) initializer ++
        surfaceClassStructureNodes sourceUnit (childSourcePath path 2) classStructure
    | .mixinChain _ receiver initializer additional classStructure =>
        surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
        surfaceClauseNodes sourceUnit (childSourcePath path 1) initializer ++
        surfaceInheritanceHeadListNodes sourceUnit path 2 additional ++
        surfaceOptionalClassStructureNodes sourceUnit
          (childSourcePath path (additional.length + 2)) classStructure

  partial def surfaceInheritanceHeadNodes (sourceUnit : String)
      (path : List Nat) : SurfaceInheritanceHead → List UnidentifiedSourceNode
    | .head _ receiver initializer =>
        surfaceExpressionNodes sourceUnit (childSourcePath path 0) receiver ++
          surfaceClauseNodes sourceUnit (childSourcePath path 1) initializer

  partial def surfaceInheritanceHeadListNodes (sourceUnit : String)
      (path : List Nat) (firstIndex : Nat) :
      List SurfaceInheritanceHead → List UnidentifiedSourceNode
    | [] => []
    | head :: remaining =>
        surfaceInheritanceHeadNodes sourceUnit (childSourcePath path firstIndex)
          head ++
        surfaceInheritanceHeadListNodes sourceUnit path (firstIndex + 1)
          remaining

  partial def surfaceOptionalClassStructureNodes (sourceUnit : String)
      (path : List Nat) :
      Option SurfaceClassStructure → List UnidentifiedSourceNode
    | none => []
    | some classStructure =>
        surfaceClassStructureNodes sourceUnit path classStructure
end

def surfaceCompilationUnitNodes (unit : SurfaceCompilationUnit) :
    List UnidentifiedSourceNode :=
  surfaceDeclarationNodes unit.language [0] unit.declaration

def identifySurfaceCompilationUnit (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (unit : SurfaceCompilationUnit) :
    Option IdentificationOutput :=
  identifySourceNodes retained supply (surfaceCompilationUnitNodes unit)

theorem identifySurfaceCompilationUnit_success_idsOK
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {unit : SurfaceCompilationUnit} {output : IdentificationOutput}
    (success : identifySurfaceCompilationUnit retained supply unit = some output) :
    IdentifiedSourceNodesOK output.nodes :=
  identifySourceNodes_success_idsOK success

theorem identifySurfaceCompilationUnit_deterministic
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {unit : SurfaceCompilationUnit} {first second : IdentificationOutput}
    (firstResult : identifySurfaceCompilationUnit retained supply unit = some first)
    (secondResult : identifySurfaceCompilationUnit retained supply unit = some second) :
    first = second :=
  identifySourceNodes_deterministic firstResult secondResult

end Newspeak
