import Newspeak.FiniteStore

namespace Newspeak

/-!
# Parsing-expression-grammar recognition

This is the relational counterpart of the PEG equations in the formal
semantics.  It deliberately models recognition, including diagnostic failure
offsets and ordered forests, independently of the Newspeak-specific semantic
actions that turn the captured concrete tree into a surface AST.
-/

abbrev SourceText := List Char
abbrev Nonterminal := String
abbrev CaptureName := String

inductive PEGExpr where
  | empty
  | character (value : Char)
  | characterSet (accepts : Char → Bool)
  | any
  | nonterminal (name : Nonterminal)
  | sequence (first second : PEGExpr)
  | orderedChoice (first second : PEGExpr)
  | star (body : PEGExpr)
  | notAhead (body : PEGExpr)
  | andAhead (body : PEGExpr)
  | capture (name : CaptureName) (body : PEGExpr)

inductive ConcreteTree where
  | leaf (startOffset endOffset : Nat)
  | node (name : CaptureName) (startOffset endOffset : Nat)
      (children : List ConcreteTree)
deriving Repr

def ConcreteTree.span : ConcreteTree → Nat × Nat
  | .leaf startOffset endOffset => (startOffset, endOffset)
  | .node _ startOffset endOffset _ => (startOffset, endOffset)

inductive PEGResult where
  | success (nextOffset : Nat) (forest : List ConcreteTree)
  | failure (offset : Nat)
deriving Repr

structure PEGGrammar where
  start : Nonterminal
  rules : FiniteStore Nonterminal PEGExpr

/-- Big-step PEG recognition.  Ordered choice restarts its right operand at
    the original offset.  Lookahead consumes nothing and contributes no tree.
    A repetition step must advance, making the semantic side condition that
    corresponds to the grammar's non-nullable-star admissibility clause
    explicit in the derivation. -/
inductive PEGRecognizes (grammar : PEGGrammar) (source : SourceText) :
    PEGExpr → Nat → PEGResult → Prop where
  | empty (offset) :
      PEGRecognizes grammar source .empty offset (.success offset [])
  | characterSuccess (offset value)
      (present : source[offset]? = some value) :
      PEGRecognizes grammar source (.character value) offset
        (.success (offset + 1) [.leaf offset (offset + 1)])
  | characterFailure (offset value)
      (absent : source[offset]? ≠ some value) :
      PEGRecognizes grammar source (.character value) offset (.failure offset)
  | characterSetSuccess (offset accepts value)
      (present : source[offset]? = some value) (accepted : accepts value = true) :
      PEGRecognizes grammar source (.characterSet accepts) offset
        (.success (offset + 1) [.leaf offset (offset + 1)])
  | characterSetFailureAbsent (offset accepts)
      (absent : source[offset]? = none) :
      PEGRecognizes grammar source (.characterSet accepts) offset
        (.failure offset)
  | characterSetFailureRejected (offset accepts value)
      (present : source[offset]? = some value) (rejected : accepts value = false) :
      PEGRecognizes grammar source (.characterSet accepts) offset
        (.failure offset)
  | anySuccess (offset value) (present : source[offset]? = some value) :
      PEGRecognizes grammar source .any offset
        (.success (offset + 1) [.leaf offset (offset + 1)])
  | anyFailure (offset) (absent : source[offset]? = none) :
      PEGRecognizes grammar source .any offset (.failure offset)
  | nonterminalDefined (offset name body result)
      (defined : grammar.rules name = some body)
      (recognizes : PEGRecognizes grammar source body offset result) :
      PEGRecognizes grammar source (.nonterminal name) offset result
  | nonterminalUndefined (offset name)
      (undefined : grammar.rules name = none) :
      PEGRecognizes grammar source (.nonterminal name) offset (.failure offset)
  | sequenceFirstFailure (offset first second failureOffset)
      (firstFails : PEGRecognizes grammar source first offset
        (.failure failureOffset)) :
      PEGRecognizes grammar source (.sequence first second) offset
        (.failure failureOffset)
  | sequenceSecondFailure (offset first second middle firstForest failureOffset)
      (firstSucceeds : PEGRecognizes grammar source first offset
        (.success middle firstForest))
      (secondFails : PEGRecognizes grammar source second middle
        (.failure failureOffset)) :
      PEGRecognizes grammar source (.sequence first second) offset
        (.failure failureOffset)
  | sequenceSuccess (offset first second middle final firstForest secondForest)
      (firstSucceeds : PEGRecognizes grammar source first offset
        (.success middle firstForest))
      (secondSucceeds : PEGRecognizes grammar source second middle
        (.success final secondForest)) :
      PEGRecognizes grammar source (.sequence first second) offset
        (.success final (firstForest ++ secondForest))
  | choiceLeftSuccess (offset first second final forest)
      (leftSucceeds : PEGRecognizes grammar source first offset
        (.success final forest)) :
      PEGRecognizes grammar source (.orderedChoice first second) offset
        (.success final forest)
  | choiceRight (offset first second leftFailure result)
      (leftFails : PEGRecognizes grammar source first offset
        (.failure leftFailure))
      (rightResult : PEGRecognizes grammar source second offset result) :
      PEGRecognizes grammar source (.orderedChoice first second) offset result
  | starStop (offset body failureOffset)
      (bodyFails : PEGRecognizes grammar source body offset
        (.failure failureOffset)) :
      PEGRecognizes grammar source (.star body) offset (.success offset [])
  | starStep (offset body middle final firstForest remainingForest)
      (bodySucceeds : PEGRecognizes grammar source body offset
        (.success middle firstForest))
      (advances : offset < middle)
      (remaining : PEGRecognizes grammar source (.star body) middle
        (.success final remainingForest)) :
      PEGRecognizes grammar source (.star body) offset
        (.success final (firstForest ++ remainingForest))
  | notAheadSuccess (offset body failureOffset)
      (bodyFails : PEGRecognizes grammar source body offset
        (.failure failureOffset)) :
      PEGRecognizes grammar source (.notAhead body) offset (.success offset [])
  | notAheadFailure (offset body final forest)
      (bodySucceeds : PEGRecognizes grammar source body offset
        (.success final forest)) :
      PEGRecognizes grammar source (.notAhead body) offset (.failure offset)
  | andAheadSuccess (offset body final forest)
      (bodySucceeds : PEGRecognizes grammar source body offset
        (.success final forest)) :
      PEGRecognizes grammar source (.andAhead body) offset (.success offset [])
  | andAheadFailure (offset body failureOffset)
      (bodyFails : PEGRecognizes grammar source body offset
        (.failure failureOffset)) :
      PEGRecognizes grammar source (.andAhead body) offset (.failure offset)
  | captureSuccess (offset name body final forest)
      (bodySucceeds : PEGRecognizes grammar source body offset
        (.success final forest)) :
      PEGRecognizes grammar source (.capture name body) offset
        (.success final [.node name offset final forest])
  | captureFailure (offset name body failureOffset)
      (bodyFails : PEGRecognizes grammar source body offset
        (.failure failureOffset)) :
      PEGRecognizes grammar source (.capture name body) offset
        (.failure failureOffset)

def PEGCompleteParse (grammar : PEGGrammar) (source : SourceText)
    (tree : ConcreteTree) : Prop :=
  PEGRecognizes grammar source (.nonterminal grammar.start) 0
    (.success source.length [tree])

/-- PEG recognition is functional, including its diagnostic failure offset
    and captured forest.  Grammar admissibility is needed for totality, but
    not for uniqueness of a finite derivation. -/
theorem PEGRecognizes.deterministic
    {grammar : PEGGrammar} {source : SourceText} {expression : PEGExpr}
    {offset : Nat} {firstResult secondResult : PEGResult}
    (first : PEGRecognizes grammar source expression offset firstResult)
    (second : PEGRecognizes grammar source expression offset secondResult) :
    firstResult = secondResult := by
  induction first generalizing secondResult <;> cases second <;> grind

theorem PEGCompleteParse.unique
    {grammar : PEGGrammar} {source : SourceText}
    {firstTree secondTree : ConcreteTree}
    (first : PEGCompleteParse grammar source firstTree)
    (second : PEGCompleteParse grammar source secondTree) :
    firstTree = secondTree := by
  have resultEqual := PEGRecognizes.deterministic first second
  have forests : [firstTree] = [secondTree] :=
    (PEGResult.success.inj resultEqual).2
  exact (List.cons.inj forests).1

end Newspeak
