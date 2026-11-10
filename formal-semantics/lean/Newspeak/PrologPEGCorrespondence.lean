import Newspeak.PEGProjection
import Newspeak.PrologGCCorrespondence

/-!
# Structural correspondence for the PEG and projection clauses

Unlike the phase-level front-end bridge, this file follows the recursive PEG
and concrete-tree clauses constructor by constructor.  Operations owned by
the metalanguage---source indexing, character predicates, natural-number
progress, source slicing, and supplied semantic actions---are explicit graph
premises.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologSourceCharacterAt (source : SourceText) (offset : Nat) :
    Option Char → Prop where
  | witness {result : Option Char} : source[offset]? = result →
      PrologSourceCharacterAt source offset result

inductive PrologSourceCharacterDifferent (source : SourceText) (offset : Nat)
    (character : Char) : Prop where
  | witness : source[offset]? ≠ some character →
      PrologSourceCharacterDifferent source offset character

inductive PrologCharacterSetAccepts (predicate : Char → Bool)
    (character : Char) : Bool → Prop where
  | witness {result : Bool} : predicate character = result →
      PrologCharacterSetAccepts predicate character result

inductive PrologNaturalSuccessor (offset : Nat) : Nat → Prop where
  | witness {next : Nat} : next = offset + 1 → PrologNaturalSuccessor offset next

inductive PrologNaturalStrictlyLess (smaller larger : Nat) : Prop where
  | witness : smaller < larger → PrologNaturalStrictlyLess smaller larger

inductive PrologPEGGrammarRule (grammar : PEGGrammar) (name : Nonterminal) :
    Option PEGExpr → Prop where
  | witness {result : Option PEGExpr} : grammar.rules name = result →
      PrologPEGGrammarRule grammar name result

inductive PrologPEGRecognizes (grammar : PEGGrammar) (source : SourceText) :
    PEGExpr → Nat → PEGResult → Prop where
  | empty (offset : Nat) :
      PrologPEGRecognizes grammar source .empty offset (.success offset [])
  | characterSuccess (offset next : Nat) (value : Char) :
      PrologSourceCharacterAt source offset (some value) →
      PrologNaturalSuccessor offset next →
      PrologPEGRecognizes grammar source (.character value) offset
        (.success next [.leaf offset next])
  | characterFailure (offset : Nat) (value : Char) :
      PrologSourceCharacterDifferent source offset value →
      PrologPEGRecognizes grammar source (.character value) offset
        (.failure offset)
  | characterSetSuccess (offset next : Nat) (accepts : Char → Bool)
      (value : Char) :
      PrologSourceCharacterAt source offset (some value) →
      PrologCharacterSetAccepts accepts value true →
      PrologNaturalSuccessor offset next →
      PrologPEGRecognizes grammar source (.characterSet accepts) offset
        (.success next [.leaf offset next])
  | characterSetFailureAbsent (offset : Nat) (accepts : Char → Bool) :
      PrologSourceCharacterAt source offset none →
      PrologPEGRecognizes grammar source (.characterSet accepts) offset
        (.failure offset)
  | characterSetFailureRejected (offset : Nat) (accepts : Char → Bool)
      (value : Char) :
      PrologSourceCharacterAt source offset (some value) →
      PrologCharacterSetAccepts accepts value false →
      PrologPEGRecognizes grammar source (.characterSet accepts) offset
        (.failure offset)
  | anySuccess (offset next : Nat) (value : Char) :
      PrologSourceCharacterAt source offset (some value) →
      PrologNaturalSuccessor offset next →
      PrologPEGRecognizes grammar source .any offset
        (.success next [.leaf offset next])
  | anyFailure (offset : Nat) :
      PrologSourceCharacterAt source offset none →
      PrologPEGRecognizes grammar source .any offset (.failure offset)
  | nonterminalDefined (offset : Nat) (name : Nonterminal) (body : PEGExpr)
      (result : PEGResult) :
      PrologPEGGrammarRule grammar name (some body) →
      PrologPEGRecognizes grammar source body offset result →
      PrologPEGRecognizes grammar source (.nonterminal name) offset result
  | nonterminalUndefined (offset : Nat) (name : Nonterminal) :
      PrologPEGGrammarRule grammar name none →
      PrologPEGRecognizes grammar source (.nonterminal name) offset
        (.failure offset)
  | sequenceFirstFailure (offset : Nat) (first second : PEGExpr)
      (failureOffset : Nat) :
      PrologPEGRecognizes grammar source first offset (.failure failureOffset) →
      PrologPEGRecognizes grammar source (.sequence first second) offset
        (.failure failureOffset)
  | sequenceSecondFailure (offset : Nat) (first second : PEGExpr)
      (middle : Nat) (firstForest : List ConcreteTree) (failureOffset : Nat) :
      PrologPEGRecognizes grammar source first offset
        (.success middle firstForest) →
      PrologPEGRecognizes grammar source second middle (.failure failureOffset) →
      PrologPEGRecognizes grammar source (.sequence first second) offset
        (.failure failureOffset)
  | sequenceSuccess (offset : Nat) (first second : PEGExpr)
      (middle final : Nat) (firstForest secondForest : List ConcreteTree) :
      PrologPEGRecognizes grammar source first offset
        (.success middle firstForest) →
      PrologPEGRecognizes grammar source second middle
        (.success final secondForest) →
      PrologPEGRecognizes grammar source (.sequence first second) offset
        (.success final (firstForest ++ secondForest))
  | choiceLeftSuccess (offset : Nat) (first second : PEGExpr)
      (final : Nat) (forest : List ConcreteTree) :
      PrologPEGRecognizes grammar source first offset (.success final forest) →
      PrologPEGRecognizes grammar source (.orderedChoice first second) offset
        (.success final forest)
  | choiceRight (offset : Nat) (first second : PEGExpr)
      (leftFailure : Nat) (result : PEGResult) :
      PrologPEGRecognizes grammar source first offset (.failure leftFailure) →
      PrologPEGRecognizes grammar source second offset result →
      PrologPEGRecognizes grammar source (.orderedChoice first second) offset
        result
  | starStop (offset : Nat) (body : PEGExpr) (failureOffset : Nat) :
      PrologPEGRecognizes grammar source body offset (.failure failureOffset) →
      PrologPEGRecognizes grammar source (.star body) offset
        (.success offset [])
  | starStep (offset : Nat) (body : PEGExpr) (middle final : Nat)
      (firstForest remainingForest : List ConcreteTree) :
      PrologPEGRecognizes grammar source body offset
        (.success middle firstForest) →
      PrologNaturalStrictlyLess offset middle →
      PrologPEGRecognizes grammar source (.star body) middle
        (.success final remainingForest) →
      PrologPEGRecognizes grammar source (.star body) offset
        (.success final (firstForest ++ remainingForest))
  | notAheadSuccess (offset : Nat) (body : PEGExpr) (failureOffset : Nat) :
      PrologPEGRecognizes grammar source body offset (.failure failureOffset) →
      PrologPEGRecognizes grammar source (.notAhead body) offset
        (.success offset [])
  | notAheadFailure (offset : Nat) (body : PEGExpr) (final : Nat)
      (forest : List ConcreteTree) :
      PrologPEGRecognizes grammar source body offset (.success final forest) →
      PrologPEGRecognizes grammar source (.notAhead body) offset
        (.failure offset)
  | andAheadSuccess (offset : Nat) (body : PEGExpr) (final : Nat)
      (forest : List ConcreteTree) :
      PrologPEGRecognizes grammar source body offset (.success final forest) →
      PrologPEGRecognizes grammar source (.andAhead body) offset
        (.success offset [])
  | andAheadFailure (offset : Nat) (body : PEGExpr) (failureOffset : Nat) :
      PrologPEGRecognizes grammar source body offset (.failure failureOffset) →
      PrologPEGRecognizes grammar source (.andAhead body) offset
        (.failure offset)
  | captureSuccess (offset : Nat) (name : CaptureName) (body : PEGExpr)
      (final : Nat) (forest : List ConcreteTree) :
      PrologPEGRecognizes grammar source body offset (.success final forest) →
      PrologPEGRecognizes grammar source (.capture name body) offset
        (.success final [.node name offset final forest])
  | captureFailure (offset : Nat) (name : CaptureName) (body : PEGExpr)
      (failureOffset : Nat) :
      PrologPEGRecognizes grammar source body offset (.failure failureOffset) →
      PrologPEGRecognizes grammar source (.capture name body) offset
        (.failure failureOffset)

theorem prologPEGRecognizes_iff {grammar source expression offset result} :
    PrologPEGRecognizes grammar source expression offset result ↔
      PEGRecognizes grammar source expression offset result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => exact .empty _
    | characterSuccess offset next value present successor =>
        cases present with | witness present =>
          cases successor with | witness successor =>
            subst next
            exact .characterSuccess offset value present
    | characterFailure offset value different =>
        cases different with | witness different =>
          exact .characterFailure offset value different
    | characterSetSuccess offset next accepts value present accepted successor =>
        cases present with | witness present =>
          cases accepted with | witness accepted =>
            cases successor with | witness successor =>
              subst next
              exact .characterSetSuccess offset accepts value present accepted
    | characterSetFailureAbsent offset accepts absent =>
        cases absent with | witness absent =>
          exact .characterSetFailureAbsent offset accepts absent
    | characterSetFailureRejected offset accepts value present rejected =>
        cases present with | witness present =>
          cases rejected with | witness rejected =>
            exact .characterSetFailureRejected offset accepts value present rejected
    | anySuccess offset next value present successor =>
        cases present with | witness present =>
          cases successor with | witness successor =>
            subst next
            exact .anySuccess offset value present
    | anyFailure offset absent =>
        cases absent with | witness absent => exact .anyFailure offset absent
    | nonterminalDefined offset name body result defined recognizes ih =>
        cases defined with | witness defined =>
          exact .nonterminalDefined offset name body result defined ih
    | nonterminalUndefined offset name undefined =>
        cases undefined with | witness undefined =>
          exact .nonterminalUndefined offset name undefined
    | sequenceFirstFailure offset first second failureOffset firstFails ih =>
        exact .sequenceFirstFailure offset first second failureOffset ih
    | sequenceSecondFailure offset first second middle firstForest failureOffset
        firstSucceeds secondFails firstIH secondIH =>
        exact .sequenceSecondFailure offset first second middle firstForest
          failureOffset firstIH secondIH
    | sequenceSuccess offset first second middle final firstForest secondForest
        firstSucceeds secondSucceeds firstIH secondIH =>
        exact .sequenceSuccess offset first second middle final firstForest
          secondForest firstIH secondIH
    | choiceLeftSuccess offset first second final forest left ih =>
        exact .choiceLeftSuccess offset first second final forest ih
    | choiceRight offset first second leftFailure result left right leftIH rightIH =>
        exact .choiceRight offset first second leftFailure result leftIH rightIH
    | starStop offset body failureOffset failure ih =>
        exact .starStop offset body failureOffset ih
    | starStep offset body middle final firstForest remainingForest first progress
        remaining firstIH remainingIH =>
        cases progress with | witness progress =>
          exact .starStep offset body middle final firstForest remainingForest
            firstIH progress remainingIH
    | notAheadSuccess offset body failureOffset failure ih =>
        exact .notAheadSuccess offset body failureOffset ih
    | notAheadFailure offset body final forest success ih =>
        exact .notAheadFailure offset body final forest ih
    | andAheadSuccess offset body final forest success ih =>
        exact .andAheadSuccess offset body final forest ih
    | andAheadFailure offset body failureOffset failure ih =>
        exact .andAheadFailure offset body failureOffset ih
    | captureSuccess offset name body final forest success ih =>
        exact .captureSuccess offset name body final forest ih
    | captureFailure offset name body failureOffset failure ih =>
        exact .captureFailure offset name body failureOffset ih
  · intro derivation
    induction derivation with
    | empty => exact .empty _
    | characterSuccess offset value present =>
        exact .characterSuccess offset (offset + 1) value
          (.witness present) (.witness rfl)
    | characterFailure offset value absent =>
        exact .characterFailure offset value (.witness absent)
    | characterSetSuccess offset accepts value present accepted =>
        exact .characterSetSuccess offset (offset + 1) accepts value
          (.witness present) (.witness accepted) (.witness rfl)
    | characterSetFailureAbsent offset accepts absent =>
        exact .characterSetFailureAbsent offset accepts (.witness absent)
    | characterSetFailureRejected offset accepts value present rejected =>
        exact .characterSetFailureRejected offset accepts value
          (.witness present) (.witness rejected)
    | anySuccess offset value present =>
        exact .anySuccess offset (offset + 1) value
          (.witness present) (.witness rfl)
    | anyFailure offset absent => exact .anyFailure offset (.witness absent)
    | nonterminalDefined offset name body result defined recognizes ih =>
        exact .nonterminalDefined offset name body result (.witness defined) ih
    | nonterminalUndefined offset name undefined =>
        exact .nonterminalUndefined offset name (.witness undefined)
    | sequenceFirstFailure offset first second failureOffset firstFails ih =>
        exact .sequenceFirstFailure offset first second failureOffset ih
    | sequenceSecondFailure offset first second middle firstForest failureOffset
        firstSucceeds secondFails firstIH secondIH =>
        exact .sequenceSecondFailure offset first second middle firstForest
          failureOffset firstIH secondIH
    | sequenceSuccess offset first second middle final firstForest secondForest
        firstSucceeds secondSucceeds firstIH secondIH =>
        exact .sequenceSuccess offset first second middle final firstForest
          secondForest firstIH secondIH
    | choiceLeftSuccess offset first second final forest left ih =>
        exact .choiceLeftSuccess offset first second final forest ih
    | choiceRight offset first second leftFailure result left right leftIH rightIH =>
        exact .choiceRight offset first second leftFailure result leftIH rightIH
    | starStop offset body failureOffset failure ih =>
        exact .starStop offset body failureOffset ih
    | starStep offset body middle final firstForest remainingForest first progress
        remaining firstIH remainingIH =>
        exact .starStep offset body middle final firstForest remainingForest
          firstIH (.witness progress) remainingIH
    | notAheadSuccess offset body failureOffset failure ih =>
        exact .notAheadSuccess offset body failureOffset ih
    | notAheadFailure offset body final forest success ih =>
        exact .notAheadFailure offset body final forest ih
    | andAheadSuccess offset body final forest success ih =>
        exact .andAheadSuccess offset body final forest ih
    | andAheadFailure offset body failureOffset failure ih =>
        exact .andAheadFailure offset body failureOffset ih
    | captureSuccess offset name body final forest success ih =>
        exact .captureSuccess offset name body final forest ih
    | captureFailure offset name body failureOffset failure ih =>
        exact .captureFailure offset name body failureOffset ih

inductive PrologPEGGrammarStart (grammar : PEGGrammar) : Nonterminal → Prop where
  | witness : PrologPEGGrammarStart grammar grammar.start

inductive PrologSourceTextLength (source : SourceText) : Nat → Prop where
  | witness : PrologSourceTextLength source source.length

inductive PrologPEGCompleteParse (grammar : PEGGrammar) (source : SourceText) :
    ConcreteTree → Prop where
  | parsed {start : Nonterminal} {length : Nat} {tree : ConcreteTree} :
      PrologPEGGrammarStart grammar start →
      PrologSourceTextLength source length →
      PrologPEGRecognizes grammar source (.nonterminal start) 0
        (.success length [tree]) →
      PrologPEGCompleteParse grammar source tree

theorem prologPEGCompleteParse_iff {grammar source tree} :
    PrologPEGCompleteParse grammar source tree ↔
      PEGCompleteParse grammar source tree := by
  constructor
  · intro derivation
    cases derivation with
    | parsed start length recognized =>
        cases start
        cases length
        exact prologPEGRecognizes_iff.mp recognized
  · intro parse
    exact .parsed .witness .witness (prologPEGRecognizes_iff.mpr parse)

/-! ## Concrete-tree projection -/

inductive PrologPEGTokenApplication {Value Metadata : Type}
    (semantics : PEGActionSemantics Value Metadata) (source : SourceText)
    (startOffset endOffset : Nat) : Value → Prop where
  | witness {value : Value} :
      semantics.token source ⟨startOffset, endOffset⟩ = value →
      PrologPEGTokenApplication semantics source startOffset endOffset value

inductive PrologSourceSliceApplication (source : SourceText)
    (startOffset endOffset : Nat) : SourceText → Prop where
  | witness {slice : SourceText} :
      sourceSlice source ⟨startOffset, endOffset⟩ = slice →
      PrologSourceSliceApplication source startOffset endOffset slice

inductive PrologPEGActionApplication {Value Metadata : Type}
    (semantics : PEGActionSemantics Value Metadata) (name : CaptureName)
    (startOffset endOffset : Nat) (values : List Value) (slice : SourceText) :
    Option (SemanticActionResult Value Metadata) → Prop where
  | witness {result : Option (SemanticActionResult Value Metadata)} :
      semantics.action name ⟨startOffset, endOffset⟩ values slice = result →
      PrologPEGActionApplication semantics name startOffset endOffset values
        slice result

inductive PrologEmitSemanticResult {Value Metadata : Type} :
    SemanticActionResult Value Metadata → List Metadata →
      List Value → List Metadata → Prop where
  | emit (value : Value) (metadata : List Metadata) :
      PrologEmitSemanticResult (.emit value) metadata [value] metadata
  | erase (metadata : List Metadata) :
      PrologEmitSemanticResult .erase metadata [] metadata
  | metadata (value : Metadata) (metadata : List Metadata) :
      PrologEmitSemanticResult (.metadata value) metadata []
        (metadata ++ [value])

theorem prologEmitSemanticResult_iff {Value Metadata : Type}
    {result : SemanticActionResult Value Metadata} {accumulated : List Metadata}
    {values : List Value} {metadata : List Metadata} :
    PrologEmitSemanticResult result accumulated values metadata ↔
      emitSemanticResult result accumulated = (values, metadata) := by
  cases result <;> constructor <;> intro premise
  · cases premise; rfl
  · have equal := Prod.mk.inj premise
    cases equal.1
    cases equal.2
    exact .emit _ _
  · cases premise; rfl
  · have equal := Prod.mk.inj premise
    cases equal.1
    cases equal.2
    exact .erase _
  · cases premise; rfl
  · have equal := Prod.mk.inj premise
    cases equal.1
    cases equal.2
    exact .metadata _ _

mutual
  inductive PrologProjectConcreteTree {Value Metadata : Type}
      (semantics : PEGActionSemantics Value Metadata) (source : SourceText) :
      ConcreteTree → List Value → List Metadata → Prop where
    | leaf (startOffset endOffset : Nat) (value : Value) :
        PrologPEGTokenApplication semantics source startOffset endOffset value →
        PrologProjectConcreteTree semantics source (.leaf startOffset endOffset)
          [value] []
    | node (name : CaptureName) (startOffset endOffset : Nat)
        (children : List ConcreteTree) (childValues values : List Value)
        (childMetadata metadata : List Metadata) (slice : SourceText)
        (result : SemanticActionResult Value Metadata) :
        PrologProjectConcreteForest semantics source children childValues
          childMetadata →
        PrologSourceSliceApplication source startOffset endOffset slice →
        PrologPEGActionApplication semantics name startOffset endOffset
          childValues slice (some result) →
        PrologEmitSemanticResult result childMetadata values metadata →
        PrologProjectConcreteTree semantics source
          (.node name startOffset endOffset children) values metadata

  inductive PrologProjectConcreteForest {Value Metadata : Type}
      (semantics : PEGActionSemantics Value Metadata) (source : SourceText) :
      List ConcreteTree → List Value → List Metadata → Prop where
    | nil : PrologProjectConcreteForest semantics source [] [] []
    | cons (tree : ConcreteTree) (remaining : List ConcreteTree)
        (firstValues restValues : List Value)
        (firstMetadata restMetadata : List Metadata) :
        PrologProjectConcreteTree semantics source tree firstValues firstMetadata →
        PrologProjectConcreteForest semantics source remaining restValues
          restMetadata →
        PrologProjectConcreteForest semantics source (tree :: remaining)
          (firstValues ++ restValues) (firstMetadata ++ restMetadata)
end

mutual
  theorem PrologProjectConcreteTree.sound {Value Metadata : Type}
      {semantics : PEGActionSemantics Value Metadata} {source tree values metadata}
      (derivation : PrologProjectConcreteTree semantics source tree values metadata) :
      projectConcreteTree semantics source tree = some (values, metadata) := by
    cases derivation with
    | leaf startOffset endOffset value token =>
        cases token with | witness token =>
          simp [projectConcreteTree, token]
    | node name startOffset endOffset children childValues values childMetadata
        metadata slice result forest sliceApplication action emitted =>
        cases sliceApplication with | witness sliceProof =>
          cases action with | witness actionProof =>
            have forestProof := PrologProjectConcreteForest.sound forest
            have emittedProof := prologEmitSemanticResult_iff.mp emitted
            simp [projectConcreteTree, forestProof, sliceProof, actionProof,
              emittedProof]

  theorem PrologProjectConcreteForest.sound {Value Metadata : Type}
      {semantics : PEGActionSemantics Value Metadata} {source trees values metadata}
      (derivation : PrologProjectConcreteForest semantics source trees values metadata) :
      projectConcreteForest semantics source trees = some (values, metadata) := by
    cases derivation with
    | nil => rfl
    | cons tree remaining firstValues restValues firstMetadata restMetadata
        first rest =>
        have firstProof := PrologProjectConcreteTree.sound first
        have restProof := PrologProjectConcreteForest.sound rest
        simp [projectConcreteForest, firstProof, restProof]
end

mutual
  theorem prologProjectConcreteTree_complete {Value Metadata : Type}
      {semantics : PEGActionSemantics Value Metadata} {source tree values metadata}
      (success : projectConcreteTree semantics source tree =
        some (values, metadata)) :
      PrologProjectConcreteTree semantics source tree values metadata := by
    cases tree with
    | leaf startOffset endOffset =>
        have equal :
            ([semantics.token source ⟨startOffset, endOffset⟩], []) =
              (values, metadata) := by
          exact Option.some.inj (by simpa [projectConcreteTree] using success)
        have components := Prod.mk.inj equal
        cases components.1
        cases components.2
        exact .leaf startOffset endOffset _ (.witness rfl)
    | node name startOffset endOffset children =>
        simp only [projectConcreteTree] at success
        cases forestResult : projectConcreteForest semantics source children with
        | none => simp [forestResult] at success
        | some projection =>
            cases projection with
            | mk childValues childMetadata =>
                simp [forestResult] at success
                cases actionResult : semantics.action name
                    ⟨startOffset, endOffset⟩ childValues
                    (sourceSlice source ⟨startOffset, endOffset⟩) with
                | none => simp [actionResult] at success
                | some result =>
                    have equal : emitSemanticResult result childMetadata =
                        (values, metadata) := by
                      exact Option.some.inj (by
                        simpa [forestResult, actionResult] using success)
                    have components := Prod.mk.inj equal
                    cases components.1
                    cases components.2
                    exact .node name startOffset endOffset children childValues
                      (emitSemanticResult result childMetadata).1 childMetadata
                      (emitSemanticResult result childMetadata).2
                      (sourceSlice source ⟨startOffset, endOffset⟩) result
                      (prologProjectConcreteForest_complete forestResult)
                      (.witness rfl) (.witness actionResult)
                      (prologEmitSemanticResult_iff.mpr rfl)

  theorem prologProjectConcreteForest_complete {Value Metadata : Type}
      {semantics : PEGActionSemantics Value Metadata} {source trees values metadata}
      (success : projectConcreteForest semantics source trees =
        some (values, metadata)) :
      PrologProjectConcreteForest semantics source trees values metadata := by
    cases trees with
    | nil =>
        have equal : ([], []) = (values, metadata) := by
          exact Option.some.inj (by
            simpa [projectConcreteForest] using success)
        have components := Prod.mk.inj equal
        cases components.1
        cases components.2
        exact .nil
    | cons tree remaining =>
        simp only [projectConcreteForest] at success
        cases firstResult : projectConcreteTree semantics source tree with
        | none => simp [firstResult] at success
        | some first =>
            cases first with
            | mk firstValues firstMetadata =>
                cases restResult : projectConcreteForest semantics source remaining with
                | none => simp [firstResult, restResult] at success
                | some rest =>
                    cases rest with
                    | mk restValues restMetadata =>
                        have equal :
                            (firstValues ++ restValues,
                              firstMetadata ++ restMetadata) =
                              (values, metadata) := by
                          exact Option.some.inj (by
                            simpa [firstResult, restResult] using success)
                        have components := Prod.mk.inj equal
                        cases components.1
                        cases components.2
                        exact .cons tree remaining firstValues restValues
                          firstMetadata restMetadata
                          (prologProjectConcreteTree_complete firstResult)
                          (prologProjectConcreteForest_complete restResult)
end

inductive PrologPEGProjects {Value Metadata : Type}
    (semantics : PEGActionSemantics Value Metadata) (source : SourceText)
    (tree : ConcreteTree) : Value → List Metadata → Prop where
  | projected {root : Value} {metadata : List Metadata} :
      PrologProjectConcreteTree semantics source tree [root] metadata →
      PrologPEGProjects semantics source tree root metadata

theorem prologPEGProjects_iff {Value Metadata : Type}
    {semantics : PEGActionSemantics Value Metadata} {source tree root metadata} :
    PrologPEGProjects semantics source tree root metadata ↔
      PEGProjects semantics source tree root metadata := by
  constructor
  · intro projection
    cases projection with
    | projected projected =>
        unfold PEGProjects projectPEGAST
        simp [projected.sound]
  · intro projection
    unfold PEGProjects projectPEGAST at projection
    cases treeProjection : projectConcreteTree semantics source tree with
    | none => simp [treeProjection] at projection
    | some result =>
        cases result with
        | mk values attached =>
            cases values with
            | nil => simp [treeProjection] at projection
            | cons first remaining =>
                cases remaining with
                | nil =>
                    have equal : (first, attached) = (root, metadata) := by
                      exact Option.some.inj (by
                        simpa [treeProjection] using projection)
                    have components := Prod.mk.inj equal
                    cases components.1
                    cases components.2
                    exact .projected
                      (prologProjectConcreteTree_complete treeProjection)
                | cons second tail => simp [treeProjection] at projection

inductive PrologPEGParsesAST {Value Metadata : Type}
    (grammar : PEGGrammar) (semantics : PEGActionSemantics Value Metadata)
    (source : SourceText) : Value → List Metadata → Prop where
  | parsed {tree : ConcreteTree} {root : Value} {metadata : List Metadata} :
      PrologPEGCompleteParse grammar source tree →
      PrologPEGProjects semantics source tree root metadata →
      PrologPEGParsesAST grammar semantics source root metadata

theorem prologPEGParsesAST_iff {Value Metadata : Type}
    {grammar : PEGGrammar} {semantics : PEGActionSemantics Value Metadata}
    {source root metadata} :
    PrologPEGParsesAST grammar semantics source root metadata ↔
      PEGParsesAST grammar semantics source root metadata := by
  constructor
  · intro derivation
    cases derivation with
    | parsed parse projection =>
        exact ⟨_, prologPEGCompleteParse_iff.mp parse,
          prologPEGProjects_iff.mp projection⟩
  · rintro ⟨tree, parse, projection⟩
    exact .parsed (prologPEGCompleteParse_iff.mpr parse)
      (prologPEGProjects_iff.mpr projection)

end PrologBridge
end Newspeak
