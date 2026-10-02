import Newspeak.PEGProjection
import Newspeak.Syntax

namespace Newspeak

/-!
# Complete executable surface syntax

These mutually recursive datatypes transcribe the surface domains in the
front-end semantics.  They intentionally retain parentheses, identifiers,
cascades, source-level setters, optional access, slot mutability, inheritance
syntax, and declaration grouping: elaboration, not parsing, removes those
distinctions.
-/

inductive SurfaceMutability where
  | immutable
  | mutable
deriving Repr, DecidableEq, BEq

structure SurfaceMetadata where
  tag : String
  payload : SourceText
  span : SourceSpan
deriving Repr

mutual
  inductive SurfaceClause where
    | clause (span : SourceSpan) (selector : Selector)
        (arguments : List SurfaceExpression)
  deriving Repr

  inductive SurfacePattern where
    | wildcard (span : SourceSpan)
    | literal (span : SourceSpan) (expression : SurfaceExpression)
    | variable (span : SourceSpan) (name : String)
    | nested (span : SourceSpan) (pattern : SurfacePattern)
    | keyword (span : SourceSpan)
        (pairs : List (Selector × Option SurfacePattern))
  deriving Repr

  inductive SurfaceExpression where
    | atom (span : SourceSpan) (payload : AtomPayload)
    | identifier (span : SourceSpan) (name : String)
    | selfValue (span : SourceSpan)
    | outer (span : SourceSpan) (name : String)
    | superValue (span : SourceSpan)
    | parenthesized (span : SourceSpan) (expression : SurfaceExpression)
    | implicitSend (span : SourceSpan) (selector : Selector)
        (arguments : List SurfaceExpression)
    | messageSend (span : SourceSpan) (receiver : SurfaceExpression)
        (selector : Selector) (arguments : List SurfaceExpression)
    | eventualSend (span : SourceSpan) (receiver : SurfaceExpression)
        (selector : Selector) (arguments : List SurfaceExpression)
    | cascade (span : SourceSpan) (receiver : SurfaceExpression)
        (initialClauses subsequentClauses : List SurfaceClause)
    | setter (span : SourceSpan) (name : String)
        (expression : SurfaceExpression)
    | tuple (span : SourceSpan) (elements : List SurfaceExpression)
    | pattern (span : SourceSpan) (value : SurfacePattern)
    | closure (span : SourceSpan) (parameters : List SurfaceDeclaration)
        (locals : List SurfaceSlotGroup) (body : List SurfaceStatement)
    | objectLiteral (span : SourceSpan) (header : SurfaceObjectHeader)
    | classExpression (span : SourceSpan) (declaration : SurfaceDeclaration)
    | sequence (span : SourceSpan) (statements : List SurfaceStatement)
  deriving Repr

  inductive SurfaceStatement where
    | expression (span : SourceSpan) (value : SurfaceExpression)
    | returnStatement (span : SourceSpan) (value : SurfaceExpression)
  deriving Repr

  inductive SurfaceDeclaration where
    | formal (span : SourceSpan) (name : String)
    | slot (span : SourceSpan) (access : Option Access) (name : String)
        (mutability : SurfaceMutability)
        (initializer : Option SurfaceExpression)
    | lazySlot (span : SourceSpan) (access : Option Access) (name : String)
        (mutability : SurfaceMutability) (initializer : SurfaceExpression)
    | method (span : SourceSpan) (access : Option Access)
        (selector : Selector) (formals : List SurfaceDeclaration)
        (locals : List SurfaceSlotGroup) (body : List SurfaceStatement)
    | nestedClass (span : SourceSpan) (access : Option Access)
        (declaration : SurfaceDeclaration)
    | classDeclaration (span : SourceSpan) (name : String)
        (factorySelector : Selector) (factoryFormals : List SurfaceDeclaration)
        (inheritance : SurfaceInheritance)
  deriving Repr

  inductive SurfaceSlotGroup where
    | sequential (span : SourceSpan) (declarations : List SurfaceDeclaration)
    | simultaneous (span : SourceSpan) (declarations : List SurfaceDeclaration)
  deriving Repr

  inductive SurfaceClassStructure where
    | structure (span : SourceSpan) (headerLocals : Option SurfaceSlotGroup)
        (headerStatements : List SurfaceStatement)
        (instanceDeclarations classDeclarations : List SurfaceDeclaration)
  deriving Repr

  inductive SurfaceObjectHeader where
    | implicitHeader (span : SourceSpan)
        (classStructure : SurfaceClassStructure)
    | explicitHeader (span : SourceSpan) (receiver : SurfaceExpression)
        (initializer : SurfaceClause) (classStructure : SurfaceClassStructure)
  deriving Repr

  inductive SurfaceInheritanceHead where
    | head (span : SourceSpan) (receiver : SurfaceExpression)
        (initializer : SurfaceClause)
  deriving Repr

  inductive SurfaceInheritance where
    | defaultInheritance (span : SourceSpan)
        (classStructure : SurfaceClassStructure)
    | explicitInheritance (span : SourceSpan) (receiver : SurfaceExpression)
        (initializer : SurfaceClause) (classStructure : SurfaceClassStructure)
    | mixinChain (span : SourceSpan) (receiver : SurfaceExpression)
        (initializer : SurfaceClause)
        (additional : List SurfaceInheritanceHead)
        (classStructure : Option SurfaceClassStructure)
  deriving Repr
end

structure SurfaceCompilationUnit where
  span : SourceSpan
  language : String
  category : Option String
  declaration : SurfaceDeclaration
deriving Repr

def SurfaceClause.span : SurfaceClause → SourceSpan
  | .clause span _ _ => span

def SurfaceClause.selector : SurfaceClause → Selector
  | .clause _ selector _ => selector

def SurfaceClause.arguments : SurfaceClause → List SurfaceExpression
  | .clause _ _ arguments => arguments

def SurfaceExpression.span : SurfaceExpression → SourceSpan
  | .atom span _ | .identifier span _ | .selfValue span | .outer span _
  | .superValue span | .parenthesized span _ | .implicitSend span _ _
  | .messageSend span _ _ _ | .eventualSend span _ _ _
  | .cascade span _ _ _ | .setter span _ _ | .tuple span _
  | .pattern span _ | .closure span _ _ _ | .objectLiteral span _
  | .classExpression span _ | .sequence span _ => span

def SurfaceDeclaration.span : SurfaceDeclaration → SourceSpan
  | .formal span _ | .slot span _ _ _ _ | .lazySlot span _ _ _ _
  | .method span _ _ _ _ _ | .nestedClass span _ _
  | .classDeclaration span _ _ _ _ => span

def SurfaceStatement.span : SurfaceStatement → SourceSpan
  | .expression span _ | .returnStatement span _ => span

def SurfaceInheritanceHead.span : SurfaceInheritanceHead → SourceSpan
  | .head span _ _ => span

def SurfaceInheritanceHead.receiver : SurfaceInheritanceHead → SurfaceExpression
  | .head _ receiver _ => receiver

def SurfaceInheritanceHead.initializer : SurfaceInheritanceHead → SurfaceClause
  | .head _ _ initializer => initializer

end Newspeak
