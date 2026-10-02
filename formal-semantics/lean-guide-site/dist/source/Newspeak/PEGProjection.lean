import Newspeak.PEG

namespace Newspeak

/-!
# Concrete-tree projection

This module is the executable form of the `project`, `emitResult`, and `ast`
equations.  It is polymorphic in the grammar's semantic value and metadata
domains; `NewspeakSurface` supplies the Newspeak-specific action value below.
-/

structure SourceSpan where
  startOffset : Nat
  endOffset : Nat
deriving Repr, DecidableEq, BEq

def sourceSlice (source : SourceText) (span : SourceSpan) : SourceText :=
  (source.drop span.startOffset).take (span.endOffset - span.startOffset)

inductive SemanticActionResult (Value Metadata : Type) where
  | emit (value : Value)
  | erase
  | metadata (value : Metadata)

/-- A finite grammar may replace these functions reflectively; admission of
    its output is handled separately from the fixed projection semantics. -/
structure PEGActionSemantics (Value Metadata : Type) where
  token : SourceText → SourceSpan → Value
  action : CaptureName → SourceSpan → List Value → SourceText →
    Option (SemanticActionResult Value Metadata)

def emitSemanticResult {Value Metadata : Type}
    (result : SemanticActionResult Value Metadata)
    (accumulatedMetadata : List Metadata) : List Value × List Metadata :=
  match result with
  | .emit value => ([value], accumulatedMetadata)
  | .erase => ([], accumulatedMetadata)
  | .metadata value => ([], accumulatedMetadata ++ [value])

mutual
  def projectConcreteTree {Value Metadata : Type}
      (semantics : PEGActionSemantics Value Metadata) (source : SourceText) :
      ConcreteTree → Option (List Value × List Metadata)
    | .leaf startOffset endOffset =>
        some ([semantics.token source ⟨startOffset, endOffset⟩], [])
    | .node name startOffset endOffset children => do
        let childProjection ← projectConcreteForest semantics source children
        let result ← semantics.action name ⟨startOffset, endOffset⟩ childProjection.1
          (sourceSlice source ⟨startOffset, endOffset⟩)
        pure (emitSemanticResult result childProjection.2)

  def projectConcreteForest {Value Metadata : Type}
      (semantics : PEGActionSemantics Value Metadata) (source : SourceText) :
      List ConcreteTree → Option (List Value × List Metadata)
    | [] => some ([], [])
    | tree :: remaining => do
        let first ← projectConcreteTree semantics source tree
        let rest ← projectConcreteForest semantics source remaining
        pure (first.1 ++ rest.1, first.2 ++ rest.2)
end

/-- Projection is an AST exactly when the root emits one semantic value. -/
def projectPEGAST {Value Metadata : Type}
    (semantics : PEGActionSemantics Value Metadata) (source : SourceText)
    (tree : ConcreteTree) : Option (Value × List Metadata) := do
  let projection ← projectConcreteTree semantics source tree
  match projection.1 with
  | [root] => some (root, projection.2)
  | _ => none

def PEGProjects {Value Metadata : Type}
    (semantics : PEGActionSemantics Value Metadata) (source : SourceText)
    (tree : ConcreteTree) (root : Value) (metadata : List Metadata) : Prop :=
  projectPEGAST semantics source tree = some (root, metadata)

theorem PEGProjects.deterministic {Value Metadata : Type}
    {semantics : PEGActionSemantics Value Metadata} {source : SourceText}
    {tree : ConcreteTree} {firstRoot secondRoot : Value}
    {firstMetadata secondMetadata : List Metadata}
    (first : PEGProjects semantics source tree firstRoot firstMetadata)
    (second : PEGProjects semantics source tree secondRoot secondMetadata) :
    firstRoot = secondRoot ∧ firstMetadata = secondMetadata := by
  unfold PEGProjects at first second
  rw [first] at second
  exact Prod.mk.inj (Option.some.inj second)

def PEGParsesAST {Value Metadata : Type}
    (grammar : PEGGrammar) (semantics : PEGActionSemantics Value Metadata)
    (source : SourceText) (root : Value) (metadata : List Metadata) : Prop :=
  ∃ tree, PEGCompleteParse grammar source tree ∧
    PEGProjects semantics source tree root metadata

theorem PEGParsesAST.deterministic {Value Metadata : Type}
    {grammar : PEGGrammar} {semantics : PEGActionSemantics Value Metadata}
    {source : SourceText} {firstRoot secondRoot : Value}
    {firstMetadata secondMetadata : List Metadata}
    (first : PEGParsesAST grammar semantics source firstRoot firstMetadata)
    (second : PEGParsesAST grammar semantics source secondRoot secondMetadata) :
    firstRoot = secondRoot ∧ firstMetadata = secondMetadata := by
  rcases first with ⟨firstTree, firstParse, firstProjection⟩
  rcases second with ⟨secondTree, secondParse, secondProjection⟩
  have trees : firstTree = secondTree := PEGCompleteParse.unique firstParse secondParse
  subst secondTree
  exact PEGProjects.deterministic firstProjection secondProjection

end Newspeak
