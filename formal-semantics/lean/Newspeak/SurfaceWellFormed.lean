import Newspeak.SurfaceNodes

namespace Newspeak

/-!
# Executable surface-shape validation

The Boolean below is the non-binding portion of `shapesOK`: it rejects
standalone `outer`/`super`, non-final returns, immutable slots without an
initializer, and malformed body-less mixin chains.  It recursively checks all
embedded declarations and expressions rather than relying on a prose side
condition.
-/

def optionalExpressionShapeOK
    (check : Bool → SurfaceExpression → Bool) (receiverPosition : Bool) :
    Option SurfaceExpression → Bool
  | none => true
  | some expression => check receiverPosition expression

mutual
  partial def surfaceExpressionShapeOK (receiverPosition : Bool) :
      SurfaceExpression → Bool
    | .atom _ _ | .identifier _ _ | .selfValue _ => true
    | .outer _ _ | .superValue _ => receiverPosition
    | .parenthesized _ expression =>
        surfaceExpressionShapeOK receiverPosition expression
    | .implicitSend _ _ arguments =>
        arguments.all (surfaceExpressionShapeOK false)
    | .messageSend _ receiver _ arguments =>
        surfaceExpressionShapeOK true receiver &&
          arguments.all (surfaceExpressionShapeOK false)
    | .eventualSend _ receiver _ arguments =>
        surfaceExpressionShapeOK true receiver &&
          arguments.all (surfaceExpressionShapeOK false)
    | .cascade _ receiver initial subsequent =>
        surfaceExpressionShapeOK true receiver &&
          initial.all surfaceClauseShapeOK &&
          subsequent.all surfaceClauseShapeOK
    | .setter _ _ expression => surfaceExpressionShapeOK false expression
    | .tuple _ elements => elements.all (surfaceExpressionShapeOK false)
    | .pattern _ pattern => surfacePatternShapeOK pattern
    | .closure _ parameters locals body =>
        parameters.all surfaceDeclarationShapeOK &&
          locals.all surfaceSlotGroupShapeOK &&
          surfaceStatementListShapeOK body
    | .objectLiteral _ header => surfaceObjectHeaderShapeOK header
    | .classExpression _ declaration => surfaceDeclarationShapeOK declaration
    | .sequence _ statements => surfaceStatementListShapeOK statements

  partial def surfaceClauseShapeOK : SurfaceClause → Bool
    | .clause _ _ arguments =>
        arguments.all (surfaceExpressionShapeOK false)

  partial def surfacePatternShapeOK : SurfacePattern → Bool
    | .wildcard _ | .variable _ _ => true
    | .literal _ expression => surfaceExpressionShapeOK false expression
    | .nested _ pattern => surfacePatternShapeOK pattern
    | .keyword _ pairs => pairs.all fun pair =>
        match pair.2 with
        | none => true
        | some pattern => surfacePatternShapeOK pattern

  partial def surfaceStatementShapeOK : SurfaceStatement → Bool
    | .expression _ expression | .returnStatement _ expression =>
        surfaceExpressionShapeOK false expression

  partial def surfaceStatementListShapeOK : List SurfaceStatement → Bool
    | [] => true
    | [statement] => surfaceStatementShapeOK statement
    | .returnStatement _ _ :: _ => false
    | statement :: remaining =>
        surfaceStatementShapeOK statement &&
          surfaceStatementListShapeOK remaining

  partial def surfaceDeclarationShapeOK : SurfaceDeclaration → Bool
    | .formal _ _ => true
    | .slot _ _ _ .immutable none => false
    | .slot _ _ _ _ initializer =>
        optionalExpressionShapeOK surfaceExpressionShapeOK false initializer
    | .lazySlot _ _ _ _ initializer =>
        surfaceExpressionShapeOK false initializer
    | .method _ _ _ formals locals body =>
        formals.all surfaceDeclarationShapeOK &&
          locals.all surfaceSlotGroupShapeOK &&
          surfaceStatementListShapeOK body
    | .nestedClass _ _ declaration => surfaceDeclarationShapeOK declaration
    | .classDeclaration _ _ factorySelector factoryFormals inheritance =>
        factoryFormals.all surfaceDeclarationShapeOK &&
          surfaceInheritanceShapeOK factorySelector inheritance

  partial def surfaceSlotGroupShapeOK : SurfaceSlotGroup → Bool
    | .sequential _ declarations | .simultaneous _ declarations =>
        declarations.all surfaceDeclarationShapeOK

  partial def surfaceClassStructureShapeOK : SurfaceClassStructure → Bool
    | .structure _ headerLocals headerStatements instanceDeclarations
        classDeclarations =>
        (match headerLocals with
          | none => true
          | some locals => surfaceSlotGroupShapeOK locals) &&
        surfaceStatementListShapeOK headerStatements &&
        instanceDeclarations.all surfaceDeclarationShapeOK &&
        classDeclarations.all surfaceDeclarationShapeOK

  partial def surfaceObjectHeaderShapeOK : SurfaceObjectHeader → Bool
    | .implicitHeader _ classStructure =>
        surfaceClassStructureShapeOK classStructure
    | .explicitHeader _ receiver initializer classStructure =>
        surfaceExpressionShapeOK false receiver &&
          surfaceClauseShapeOK initializer &&
          surfaceClassStructureShapeOK classStructure

  partial def surfaceInheritanceShapeOK (factorySelector : Selector) :
      SurfaceInheritance → Bool
    | .defaultInheritance _ classStructure =>
        surfaceClassStructureShapeOK classStructure
    | .explicitInheritance _ receiver initializer classStructure =>
        surfaceExpressionShapeOK false receiver &&
          surfaceClauseShapeOK initializer &&
          surfaceClassStructureShapeOK classStructure
    | .mixinChain _ receiver initializer additional classStructure =>
        surfaceExpressionShapeOK false receiver &&
          surfaceClauseShapeOK initializer &&
          additional.all (fun head =>
            surfaceExpressionShapeOK false head.receiver &&
              surfaceClauseShapeOK head.initializer) &&
          (match classStructure with
           | some body => surfaceClassStructureShapeOK body
           | none =>
               match additional.getLast? with
               | none => false
               | some head => head.initializer.selector == factorySelector)
end

def surfaceCompilationUnitShapeOK (unit : SurfaceCompilationUnit) : Bool :=
  surfaceDeclarationShapeOK unit.declaration

end Newspeak
