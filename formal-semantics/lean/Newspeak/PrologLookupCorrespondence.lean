import Newspeak.LookupRules
import Newspeak.Dispatch
import Newspeak.GeneratedPrologManifest
import Newspeak.SequentialStep
import Newspeak.SlotInitialization
import Newspeak.ExceptionBoundary
import Newspeak.TopLevel

/-!
# Correspondence with the relational Prolog bridge

This file is the first end-to-end correspondence slice for
`../../prolog/newspeak.pl`.  Its inductive relations are a shallow formal
reading of the checked Prolog clauses: constructor premises occur in the same
order and disjunctive LaTeX premises are represented by distinct constructors.

The source checker ties every concrete clause to its LaTeX label and Lean
constructor and rejects extra-logical Prolog features.  The theorems below
establish soundness and completeness of that relational schema with respect to
the existing named Lean lookup rules, and hence with respect to executable
`Program.Lookup`.
-/

namespace Newspeak
namespace PrologBridge

/-- The checked manifest makes the exact source revision and clause inventory
    visible to the correspondence development. -/
theorem prologManifest_clause_count : prologClauseManifest.length = 1353 := by
  native_decide

/-- The two ordinary list-membership clauses used by class membership. -/
inductive PrologListMember {α : Type} (value : α) : List α → Prop where
  | head {tail : List α} : PrologListMember value (value :: tail)
  | tail {other : α} {tail : List α} :
      PrologListMember value tail → PrologListMember value (other :: tail)

theorem prologListMember_iff {α : Type} {value : α} {values : List α} :
    PrologListMember value values ↔ value ∈ values := by
  constructor
  · intro derivation
    induction derivation with
    | head => simp
    | tail _ ih => exact List.mem_cons_of_mem _ ih
  · intro membership
    induction values with
    | nil => simp at membership
    | cons head tail ih =>
        rcases List.mem_cons.mp membership with h | h
        · subst head
          exact .head
        · exact .tail (ih h)

inductive PrologListAppend {α : Type} : List α → List α → List α → Prop where
  | nil {right : List α} : PrologListAppend [] right right
  | cons {head : α} {left right result : List α} :
      PrologListAppend left right result →
      PrologListAppend (head :: left) right (head :: result)

theorem prologListAppend_iff {α : Type} {left right result : List α} :
    PrologListAppend left right result ↔ left ++ right = result := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons _ ih => simp [ih]
  · intro equality
    induction left generalizing result with
    | nil =>
        simp at equality
        subst result
        exact .nil
    | cons head tail ih =>
        simp at equality
        subst result
        exact .cons (ih rfl)

/-- The two clauses for `class_chain/4`, read as an inductive relation. -/
inductive PrologClassChain (p : Program) (h : Heap) :
    ClassId → List ClassId → Prop where
  | top : PrologClassChain p h p.top [p.top]
  | step {c parent : ClassId} {tail : List ClassId} :
      c ≠ p.top →
      p.superclass? h c = some parent →
      PrologClassChain p h parent tail →
      PrologClassChain p h c (c :: tail)

theorem prologClassChain_iff {p : Program} {h : Heap} {c : ClassId}
    {chain : List ClassId} :
    PrologClassChain p h c chain ↔ p.ClassChain h c chain := by
  constructor
  · intro derivation
    induction derivation with
    | top => exact .top
    | step hne hparent _ ih => exact .step hne hparent ih
  · intro derivation
    induction derivation with
    | top => exact .top
    | step hne hparent _ ih => exact .step hne hparent ih

/-- Clauses `U-Top`, `U-Here`, and `U-Super`. -/
inductive PrologUnrestrictedLookup (p : Program) (h : Heap)
    (selector : Selector) : ClassId → Option LookupResult → Prop where
  | top : PrologUnrestrictedLookup p h selector p.top none
  | here {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      PrologUnrestrictedLookup p h selector c (some ⟨method, c⟩)
  | super {c parent : ClassId} {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      PrologUnrestrictedLookup p h selector parent result →
      PrologUnrestrictedLookup p h selector c result

theorem prologUnrestricted_iff_rules {p : Program} {h : Heap}
    {selector : Selector} {c : ClassId} {result : Option LookupResult} :
    PrologUnrestrictedLookup p h selector c result ↔
      p.UnrestrictedLookupRules h selector c result := by
  constructor
  · intro derivation
    induction derivation with
    | top => exact .top
    | here hne hd => exact .here hne hd
    | super hne hd hparent _ ih => exact .super hne hd hparent ih
  · intro derivation
    induction derivation with
    | top => exact .top
    | here hne hd => exact .here hne hd
    | super hne hd hparent _ ih => exact .super hne hd hparent ih

/-- The independent Defining-Top/Here/Super judgment from section 4. -/
inductive PrologDefiningClass (p : Program) (h : Heap)
    (selector : Selector) : ClassId → Option ClassId → Prop where
  | top : PrologDefiningClass p h selector p.top none
  | here {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      PrologDefiningClass p h selector c (some c)
  | super {c parent : ClassId} {result : Option ClassId} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      PrologDefiningClass p h selector parent result →
      PrologDefiningClass p h selector c result

theorem prologDefiningClass_of_unrestricted {p : Program} {h : Heap}
    {selector : Selector} {c : ClassId} {result : Option LookupResult}
    (derivation : PrologUnrestrictedLookup p h selector c result) :
    PrologDefiningClass p h selector c
      (result.map LookupResult.definingClass) := by
  induction derivation with
  | top => exact .top
  | here hne hd => exact .here hne hd
  | super hne hd hparent _ ih => exact .super hne hd hparent ih

theorem prologDefiningClass_of_unrestrictedSome {p : Program} {h : Heap}
    {selector : Selector} {c defining : ClassId} {method : MethodDef}
    (derivation :
      PrologUnrestrictedLookup p h selector c
        (some ⟨method, defining⟩)) :
    PrologDefiningClass p h selector c (some defining) :=
  prologDefiningClass_of_unrestricted derivation

theorem prologUnrestricted_of_definingClass {p : Program} {h : Heap}
    {selector : Selector} {c : ClassId} {result : Option ClassId}
    (derivation : PrologDefiningClass p h selector c result) :
    match result with
    | none => PrologUnrestrictedLookup p h selector c none
    | some defining => ∃ method,
        PrologUnrestrictedLookup p h selector c
          (some ⟨method, defining⟩) := by
  induction derivation with
  | top => exact .top
  | here hne hd => exact ⟨_, .here hne hd⟩
  | @super c parent result hne hd hparent _ ih =>
      cases result with
      | none => exact .super hne hd hparent ih
      | some defining =>
          rcases ih with ⟨method, ih⟩
          exact ⟨method, .super hne hd hparent ih⟩

theorem prologUnrestrictedSome_of_definingClass {p : Program} {h : Heap}
    {selector : Selector} {c defining : ClassId}
    (derivation : PrologDefiningClass p h selector c (some defining)) :
    ∃ method,
      PrologUnrestrictedLookup p h selector c
        (some ⟨method, defining⟩) :=
  prologUnrestricted_of_definingClass derivation

theorem prologDefiningNone_iff_unrestrictedNone {p : Program} {h : Heap}
    {selector : Selector} {c : ClassId} :
    PrologDefiningClass p h selector c none ↔
      PrologUnrestrictedLookup p h selector c none := by
  constructor
  · exact prologUnrestricted_of_definingClass
  · exact prologDefiningClass_of_unrestricted

/-- The five Horn clauses implementing the four public-lookup rules. -/
inductive PrologPublicLookup (p : Program) (h : Heap)
    (selector : Selector) : ClassId → Option LookupResult → Prop where
  | top : PrologPublicLookup p h selector p.top none
  | hit {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .publicAccess →
      PrologPublicLookup p h selector c (some ⟨method, c⟩)
  | protectedBarrier {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .protectedAccess →
      PrologPublicLookup p h selector c none
  | superAbsent {c parent : ClassId} {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      PrologPublicLookup p h selector parent result →
      PrologPublicLookup p h selector c result
  | superPrivate {c parent : ClassId} {method : MethodDef}
      {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .privateAccess →
      p.superclass? h c = some parent →
      PrologPublicLookup p h selector parent result →
      PrologPublicLookup p h selector c result

theorem prologPublic_iff_rules {p : Program} {h : Heap}
    {selector : Selector} {c : ClassId} {result : Option LookupResult} :
    PrologPublicLookup p h selector c result ↔
      p.PublicLookupRules h selector c result := by
  constructor
  · intro derivation
    induction derivation with
    | top => exact .top
    | hit hne hd ha => exact .hit hne hd ha
    | protectedBarrier hne hd ha => exact .protectedBarrier hne hd ha
    | superAbsent hne hd hparent _ ih =>
        exact .superAbsent hne hd hparent ih
    | superPrivate hne hd ha hparent _ ih =>
        exact .superPrivate hne hd ha hparent ih
  · intro derivation
    induction derivation with
    | top => exact .top
    | hit hne hd ha => exact .hit hne hd ha
    | protectedBarrier hne hd ha => exact .protectedBarrier hne hd ha
    | superAbsent hne hd hparent _ ih =>
        exact .superAbsent hne hd hparent ih
    | superPrivate hne hd ha hparent _ ih =>
        exact .superPrivate hne hd ha hparent ih

/-- The five Horn clauses implementing the three protected-lookup rules. -/
inductive PrologProtectedLookup (p : Program) (h : Heap)
    (selector : Selector) : ClassId → Option LookupResult → Prop where
  | top : PrologProtectedLookup p h selector p.top none
  | hitPublic {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .publicAccess →
      PrologProtectedLookup p h selector c (some ⟨method, c⟩)
  | hitProtected {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .protectedAccess →
      PrologProtectedLookup p h selector c (some ⟨method, c⟩)
  | superAbsent {c parent : ClassId} {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      PrologProtectedLookup p h selector parent result →
      PrologProtectedLookup p h selector c result
  | superPrivate {c parent : ClassId} {method : MethodDef}
      {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .privateAccess →
      p.superclass? h c = some parent →
      PrologProtectedLookup p h selector parent result →
      PrologProtectedLookup p h selector c result

theorem prologProtected_iff_rules {p : Program} {h : Heap}
    {selector : Selector} {c : ClassId} {result : Option LookupResult} :
    PrologProtectedLookup p h selector c result ↔
      p.ProtectedLookupRules h selector c result := by
  constructor
  · intro derivation
    induction derivation with
    | top => exact .top
    | hitPublic hne hd ha => exact .hitPublic hne hd ha
    | hitProtected hne hd ha => exact .hitProtected hne hd ha
    | superAbsent hne hd hparent _ ih =>
        exact .superAbsent hne hd hparent ih
    | superPrivate hne hd ha hparent _ ih =>
        exact .superPrivate hne hd ha hparent ih
  · intro derivation
    induction derivation with
    | top => exact .top
    | hitPublic hne hd ha => exact .hitPublic hne hd ha
    | hitProtected hne hd ha => exact .hitProtected hne hd ha
    | superAbsent hne hd hparent _ ih =>
        exact .superAbsent hne hd hparent ih
    | superPrivate hne hd ha hparent _ ih =>
        exact .superPrivate hne hd ha hparent ih

/-! The externally useful end-to-end theorems compose the schema-to-rules
correspondence with the pre-existing rules-to-function theorems. -/

theorem prologUnrestricted_iff_lookup {p : Program} {h : Heap}
    {selector : Selector} {start : ClassId} {result : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain) :
    PrologUnrestrictedLookup p h selector start result ↔
      p.Lookup h .unrestricted selector start result :=
  prologUnrestricted_iff_rules.trans
    (Program.unrestrictedRules_iff_lookup hasChain)

theorem prologPublic_iff_lookup {p : Program} {h : Heap}
    {selector : Selector} {start : ClassId} {result : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain) :
    PrologPublicLookup p h selector start result ↔
      p.Lookup h .publicOnly selector start result :=
  prologPublic_iff_rules.trans (Program.publicRules_iff_lookup hasChain)

theorem prologProtected_iff_lookup {p : Program} {h : Heap}
    {selector : Selector} {start : ClassId} {result : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain) :
    PrologProtectedLookup p h selector start result ↔
      p.Lookup h .protectedAccess selector start result :=
  prologProtected_iff_rules.trans (Program.protectedRules_iff_lookup hasChain)

/-! ## Dispatch clauses

These relations are the direct shallow reading of `ordinary_dispatch/5` and
`super_dispatch/5`.  They intentionally use the Prolog-bridge lookup
relations in their premises; the proofs therefore compose two independently
visible correspondence layers. -/

inductive PrologOrdinaryDispatch (p : Program) (h : Heap)
    (receiver : ObjRef) (message : Message) : DispatchResult → Prop where
  | hit {receiverClass definingClass : ClassId} {method : MethodDef} :
      h.classOf receiver = some receiverClass →
      PrologPublicLookup p h message.selector receiverClass
        (some ⟨method, definingClass⟩) →
      PrologOrdinaryDispatch p h receiver message
        (.invoke method receiver definingClass message)
  | missing {receiverClass : ClassId} :
      h.classOf receiver = some receiverClass →
      PrologPublicLookup p h message.selector receiverClass none →
      PrologOrdinaryDispatch p h receiver message
        (.missing receiver receiverClass message)

theorem prologOrdinaryDispatch_iff {p : Program} {h : Heap}
    {receiver : ObjRef} {message : Message} {result : DispatchResult} :
    PrologOrdinaryDispatch p h receiver message result ↔
      p.OrdinaryDispatch h receiver message result := by
  constructor
  · intro derivation
    cases derivation with
    | hit hclass lookup =>
        exact .hit hclass (prologPublic_iff_rules.mp lookup)
    | missing hclass lookup =>
        exact .missing hclass (prologPublic_iff_rules.mp lookup)
  · intro derivation
    cases derivation with
    | hit hclass lookup =>
        exact .hit hclass (prologPublic_iff_rules.mpr lookup)
    | missing hclass lookup =>
        exact .missing hclass (prologPublic_iff_rules.mpr lookup)

inductive PrologSuperDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (message : Message) :
    DispatchResult → Prop where
  | hit {activation : ActivationDef}
      {currentClass lookupStart definingClass : ClassId}
      {method : MethodDef} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      currentClass ≠ p.object →
      currentClass ≠ p.top →
      p.superclass? h currentClass = some lookupStart →
      PrologProtectedLookup p h message.selector lookupStart
        (some ⟨method, definingClass⟩) →
      PrologSuperDispatch p h activationId message
        (.invoke method activation.currentReceiver definingClass message)
  | missing {activation : ActivationDef}
      {currentClass lookupStart : ClassId} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      currentClass ≠ p.object →
      currentClass ≠ p.top →
      p.superclass? h currentClass = some lookupStart →
      PrologProtectedLookup p h message.selector lookupStart none →
      PrologSuperDispatch p h activationId message
        (.missing activation.currentReceiver lookupStart message)
  | objectError {activation : ActivationDef} :
      h.activations activationId = some activation →
      activation.currentClass = some p.object →
      PrologSuperDispatch p h activationId message (.invalidSuper p.object)
  | topError {activation : ActivationDef} :
      h.activations activationId = some activation →
      activation.currentClass = some p.top →
      PrologSuperDispatch p h activationId message (.invalidSuper p.top)

theorem prologSuperDispatch_iff {p : Program} {h : Heap}
    {activationId : ActivationId} {message : Message}
    {result : DispatchResult} :
    PrologSuperDispatch p h activationId message result ↔
      p.SuperDispatch h activationId message result := by
  constructor
  · intro derivation
    cases derivation with
    | hit ha hc hobject htop hsuper lookup =>
        exact .hit ha hc hobject htop hsuper
          (prologProtected_iff_rules.mp lookup)
    | missing ha hc hobject htop hsuper lookup =>
        exact .missing ha hc hobject htop hsuper
          (prologProtected_iff_rules.mp lookup)
    | objectError ha hc => exact .objectError ha hc
    | topError ha hc => exact .topError ha hc
  · intro derivation
    cases derivation with
    | hit ha hc hobject htop hsuper lookup =>
        exact .hit ha hc hobject htop hsuper
          (prologProtected_iff_rules.mpr lookup)
    | missing ha hc hobject htop hsuper lookup =>
        exact .missing ha hc hobject htop hsuper
          (prologProtected_iff_rules.mpr lookup)
    | objectError ha hc => exact .objectError ha hc
    | topError ha hc => exact .topError ha hc

/-! ## Lexical ancestry, enclosing receivers, and implicit dispatch

The following relations cover the second correspondence slice.  In
particular, lexical depth is not merely reachability at some depth: it is
computed over a complete finite lexical-class chain, including the negative
(`none`) result. -/

inductive PrologLexicalAncestor (p : Program) :
    ClassDeclId → Nat → ClassDeclId → Prop where
  | zero {start : ClassDeclId} :
      PrologLexicalAncestor p start 0 start
  | step {start parent target : ClassDeclId} {depth : Nat} :
      p.lexParent start = some parent →
      PrologLexicalAncestor p parent depth target →
      PrologLexicalAncestor p start (depth + 1) target

theorem prologLexicalAncestor_iff {p : Program} {start target : ClassDeclId}
    {depth : Nat} :
    PrologLexicalAncestor p start depth target ↔
      p.LexicalAncestor start depth target := by
  constructor <;> intro derivation <;> induction derivation with
  | zero => exact .zero
  | step hparent _ ih => exact .step hparent ih

inductive PrologLexicalClassChain (p : Program) :
    ClassDeclId → List ClassDeclId → Prop where
  | root {decl : ClassDeclId} :
      p.lexParent decl = none →
      PrologLexicalClassChain p decl [decl]
  | step {decl parent : ClassDeclId} {tail : List ClassDeclId} :
      p.lexParent decl = some parent →
      PrologLexicalClassChain p parent tail →
      PrologLexicalClassChain p decl (decl :: tail)

theorem prologLexicalClassChain_iff {p : Program} {start : ClassDeclId}
    {chain : List ClassDeclId} :
    PrologLexicalClassChain p start chain ↔
      p.LexicalClassChain start chain := by
  constructor <;> intro derivation <;> induction derivation with
  | root hparent => exact .root hparent
  | step hparent _ ih => exact .step hparent ih

inductive PrologLexicalDepthOnChain (target : ClassDeclId) :
    List ClassDeclId → Option Nat → Prop where
  | empty : PrologLexicalDepthOnChain target [] none
  | here {tail : List ClassDeclId} :
      PrologLexicalDepthOnChain target (target :: tail) (some 0)
  | deeper {other : ClassDeclId} {tail : List ClassDeclId} {depth : Nat} :
      other ≠ target →
      PrologLexicalDepthOnChain target tail (some depth) →
      PrologLexicalDepthOnChain target (other :: tail) (some (depth + 1))
  | absent {other : ClassDeclId} {tail : List ClassDeclId} :
      other ≠ target →
      PrologLexicalDepthOnChain target tail none →
      PrologLexicalDepthOnChain target (other :: tail) none

theorem prologLexicalDepthOnChain_iff {target : ClassDeclId}
    {chain : List ClassDeclId} {result : Option Nat} :
    PrologLexicalDepthOnChain target chain result ↔
      Program.lexicalDepthOnChain target chain = result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | here => simp [Program.lexicalDepthOnChain]
    | deeper hne _ ih => simp [Program.lexicalDepthOnChain, hne, ih]
    | absent hne _ ih => simp [Program.lexicalDepthOnChain, hne, ih]
  · intro equality
    induction chain generalizing result with
    | nil =>
        simp [Program.lexicalDepthOnChain] at equality
        subst result
        exact .empty
    | cons head tail ih =>
        by_cases hhead : head = target
        · subst head
          simp [Program.lexicalDepthOnChain] at equality
          subst result
          exact .here
        · cases htail : Program.lexicalDepthOnChain target tail with
          | none =>
              have tailDerivation :
                  PrologLexicalDepthOnChain target tail none := ih htail
              simp [Program.lexicalDepthOnChain, hhead, htail] at equality
              subst result
              exact .absent hhead tailDerivation
          | some depth =>
              have tailDerivation :
                  PrologLexicalDepthOnChain target tail (some depth) := ih htail
              simp [Program.lexicalDepthOnChain, hhead, htail] at equality
              subst result
              exact .deeper hhead tailDerivation

inductive PrologLexicalDepth (p : Program) (target start : ClassDeclId) :
    Option Nat → Prop where
  | derive {chain : List ClassDeclId} {result : Option Nat} :
      PrologLexicalClassChain p start chain →
      PrologLexicalDepthOnChain target chain result →
      PrologLexicalDepth p target start result

theorem prologLexicalDepth_iff {p : Program} {target start : ClassDeclId}
    {result : Option Nat} :
    PrologLexicalDepth p target start result ↔
      p.LexicalDepth target start result := by
  constructor
  · intro derivation
    cases derivation with
    | derive chain depth =>
        exact ⟨_, prologLexicalClassChain_iff.mp chain,
          prologLexicalDepthOnChain_iff.mp depth⟩
  · rintro ⟨chain, classChain, depth⟩
    exact .derive (prologLexicalClassChain_iff.mpr classChain)
      (prologLexicalDepthOnChain_iff.mpr depth)

def PrologClassMember (p : Program) (h : Heap)
    (candidate receiverClass : ClassId) : Prop :=
  ∃ chain, PrologClassChain p h receiverClass chain ∧ candidate ∈ chain

theorem prologClassMember_iff {p : Program} {h : Heap}
    {candidate receiverClass : ClassId} :
    PrologClassMember p h candidate receiverClass ↔
      p.ClassMember h candidate receiverClass := by
  simp only [PrologClassMember, Program.ClassMember]
  constructor <;> rintro ⟨chain, chainProof, member⟩
  · exact ⟨chain, prologClassChain_iff.mp chainProof, member⟩
  · exact ⟨chain, prologClassChain_iff.mpr chainProof, member⟩

inductive PrologEnclosingReceiver (p : Program) (h : Heap) :
    ObjRef → ClassId → Nat → ObjRef → Prop where
  | zero {receiver : ObjRef} {currentClass receiverClass : ClassId} :
      h.classOf receiver = some receiverClass →
      PrologClassMember p h currentClass receiverClass →
      PrologEnclosingReceiver p h receiver currentClass 0 receiver
  | one {receiver : ObjRef} {currentClass receiverClass : ClassId}
      {classDef : ClassDef} :
      h.classOf receiver = some receiverClass →
      PrologClassMember p h currentClass receiverClass →
      h.classes currentClass = some classDef →
      PrologEnclosingReceiver p h receiver currentClass 1
        classDef.enclosingObject
  | step {receiver previous : ObjRef} {currentClass previousClass : ClassId}
      {currentDecl ancestorDecl : ClassDeclId} {application : ClassId}
      {applicationDef : ClassDef} {depth : Nat} :
      PrologEnclosingReceiver p h receiver currentClass (depth + 1) previous →
      p.namedClassDeclaration? h currentClass = some currentDecl →
      PrologLexicalAncestor p currentDecl (depth + 1) ancestorDecl →
      h.classOf previous = some previousClass →
      p.NearestApplication h previousClass ancestorDecl (some application) →
      h.classes application = some applicationDef →
      PrologEnclosingReceiver p h receiver currentClass (depth + 2)
        applicationDef.enclosingObject

theorem prologEnclosingReceiver_iff {p : Program} {h : Heap}
    {receiver result : ObjRef} {currentClass : ClassId} {depth : Nat} :
    PrologEnclosingReceiver p h receiver currentClass depth result ↔
      p.EnclosingReceiver h receiver currentClass depth result := by
  constructor
  · intro derivation
    induction derivation with
    | zero hclass member =>
        exact .zero hclass (prologClassMember_iff.mp member)
    | one hclass member hdef =>
        exact .one hclass (prologClassMember_iff.mp member) hdef
    | step _ hnamed ancestor hclass happ hdef ih =>
        exact .step ih hnamed (prologLexicalAncestor_iff.mp ancestor)
          hclass happ hdef
  · intro derivation
    induction derivation with
    | zero hclass member =>
        exact .zero hclass (prologClassMember_iff.mpr member)
    | one hclass member hdef =>
        exact .one hclass (prologClassMember_iff.mpr member) hdef
    | step _ hnamed ancestor hclass happ hdef ih =>
        exact .step ih hnamed (prologLexicalAncestor_iff.mpr ancestor)
          hclass happ hdef

inductive PrologOuterDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (target immediate : ClassDeclId)
    (message : Message) : DispatchResult → Prop where
  | privateHit {activation : ActivationDef} {currentClass : ClassId}
      {depth : Nat} {receiver : ObjRef} {targetApplication : ClassId}
      {method : MethodDef} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      PrologLexicalDepth p target immediate (some depth) →
      PrologEnclosingReceiver p h activation.currentReceiver currentClass
        depth receiver →
      p.TargetApplication h receiver target (some targetApplication) →
      p.privateMethod target message.selector = some method →
      PrologOuterDispatch p h activationId target immediate message
        (.invoke method receiver targetApplication message)
  | protectedHit {activation : ActivationDef} {currentClass : ClassId}
      {depth : Nat} {receiver : ObjRef} {receiverClass definingClass : ClassId}
      {method : MethodDef} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      PrologLexicalDepth p target immediate (some depth) →
      PrologEnclosingReceiver p h activation.currentReceiver currentClass
        depth receiver →
      p.privateMethod target message.selector = none →
      h.classOf receiver = some receiverClass →
      PrologProtectedLookup p h message.selector receiverClass
        (some ⟨method, definingClass⟩) →
      PrologOuterDispatch p h activationId target immediate message
        (.invoke method receiver definingClass message)
  | missing {activation : ActivationDef} {currentClass : ClassId}
      {depth : Nat} {receiver : ObjRef} {receiverClass : ClassId} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      PrologLexicalDepth p target immediate (some depth) →
      PrologEnclosingReceiver p h activation.currentReceiver currentClass
        depth receiver →
      p.privateMethod target message.selector = none →
      h.classOf receiver = some receiverClass →
      PrologProtectedLookup p h message.selector receiverClass none →
      PrologOuterDispatch p h activationId target immediate message
        (.missing receiver receiverClass message)

theorem prologOuterDispatch_iff {p : Program} {h : Heap}
    {activationId : ActivationId} {target immediate : ClassDeclId}
    {message : Message} {result : DispatchResult} :
    PrologOuterDispatch p h activationId target immediate message result ↔
      p.OuterDispatch h activationId target immediate message result := by
  constructor
  · intro derivation
    cases derivation with
    | privateHit ha hc hd he happ hm =>
        exact .privateHit ha hc (prologLexicalDepth_iff.mp hd)
          (prologEnclosingReceiver_iff.mp he) happ hm
    | protectedHit ha hc hd he hm hclass lookup =>
        exact .protectedHit ha hc (prologLexicalDepth_iff.mp hd)
          (prologEnclosingReceiver_iff.mp he) hm hclass
          (prologProtected_iff_rules.mp lookup)
    | missing ha hc hd he hm hclass lookup =>
        exact .missing ha hc (prologLexicalDepth_iff.mp hd)
          (prologEnclosingReceiver_iff.mp he) hm hclass
          (prologProtected_iff_rules.mp lookup)
  · intro derivation
    cases derivation with
    | privateHit ha hc hd he happ hm =>
        exact .privateHit ha hc (prologLexicalDepth_iff.mpr hd)
          (prologEnclosingReceiver_iff.mpr he) happ hm
    | protectedHit ha hc hd he hm hclass lookup =>
        exact .protectedHit ha hc (prologLexicalDepth_iff.mpr hd)
          (prologEnclosingReceiver_iff.mpr he) hm hclass
          (prologProtected_iff_rules.mpr lookup)
    | missing ha hc hd he hm hclass lookup =>
        exact .missing ha hc (prologLexicalDepth_iff.mpr hd)
          (prologEnclosingReceiver_iff.mpr he) hm hclass
          (prologProtected_iff_rules.mpr lookup)

def PrologSelfDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (immediate : ClassDeclId)
    (message : Message) (result : DispatchResult) : Prop :=
  PrologOuterDispatch p h activationId immediate immediate message result

theorem prologSelfDispatch_iff {p : Program} {h : Heap}
    {activationId : ActivationId} {immediate : ClassDeclId}
    {message : Message} {result : DispatchResult} :
    PrologSelfDispatch p h activationId immediate message result ↔
      p.SelfDispatch h activationId immediate message result :=
  prologOuterDispatch_iff

inductive PrologImplicitDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (immediate : Option ClassDeclId)
    (annotation : Option ScopeDecl) (message : Message) :
    DispatchResult → Prop where
  | classScope {target currentClass : ClassDeclId} {result : DispatchResult} :
      annotation = some (.classDecl target) →
      immediate = some currentClass →
      PrologOuterDispatch p h activationId target currentClass message result →
      PrologImplicitDispatch p h activationId immediate annotation message result
  | objectLiteralScope {activation : ActivationDef}
      {declaration : ObjectLiteralDeclId} {receiver : ObjRef}
      {receiverClass definingClass : ClassId} {method : MethodDef} :
      annotation = some (.objectLiteralDecl declaration) →
      h.activations activationId = some activation →
      activation.objectLiteralScopes declaration = some receiver →
      h.classOf receiver = some receiverClass →
      PrologUnrestrictedLookup p h message.selector receiverClass
        (some ⟨method, definingClass⟩) →
      p.classBodyDeclaration? h definingClass =
        some (.objectLiteral declaration) →
      PrologImplicitDispatch p h activationId immediate annotation message
        (.invoke method receiver definingClass message)
  | activationScope {activation : ActivationDef}
      {declaration : ActivationDeclId} {targetActivation : ActivationId}
      {result : DispatchResult} :
      annotation = some (.activationDecl declaration) →
      h.activations activationId = some activation →
      activation.activationScopes declaration = some targetActivation →
      PrologOrdinaryDispatch p h (.activationObject targetActivation)
        message result →
      PrologImplicitDispatch p h activationId immediate annotation message result
  | self {currentClass : ClassDeclId} {result : DispatchResult} :
      annotation = none →
      immediate = some currentClass →
      PrologSelfDispatch p h activationId currentClass message result →
      PrologImplicitDispatch p h activationId immediate annotation message result

theorem prologImplicitDispatch_iff {p : Program} {h : Heap}
    {activationId : ActivationId} {immediate : Option ClassDeclId}
    {annotation : Option ScopeDecl} {message : Message}
    {result : DispatchResult} :
    PrologImplicitDispatch p h activationId immediate annotation message result ↔
      p.ImplicitDispatch h activationId immediate annotation message result := by
  constructor
  · intro derivation
    cases derivation with
    | classScope hann himmediate outer =>
        exact .classScope hann himmediate (prologOuterDispatch_iff.mp outer)
    | objectLiteralScope hann ha hs hc lookup hdecl =>
        exact .objectLiteralScope hann ha hs hc
          (prologUnrestricted_iff_rules.mp lookup) hdecl
    | activationScope hann ha hs ordinary =>
        exact .activationScope hann ha hs (prologOrdinaryDispatch_iff.mp ordinary)
    | self hann himmediate selfDispatch =>
        exact .self hann himmediate (prologSelfDispatch_iff.mp selfDispatch)
  · intro derivation
    cases derivation with
    | classScope hann himmediate outer =>
        exact .classScope hann himmediate (prologOuterDispatch_iff.mpr outer)
    | objectLiteralScope hann ha hs hc lookup hdecl =>
        exact .objectLiteralScope hann ha hs hc
          (prologUnrestricted_iff_rules.mpr lookup) hdecl
    | activationScope hann ha hs ordinary =>
        exact .activationScope hann ha hs (prologOrdinaryDispatch_iff.mpr ordinary)
    | self hann himmediate selfDispatch =>
        exact .self hann himmediate (prologSelfDispatch_iff.mpr selfDispatch)

/-! ## `doesNotUnderstand:` fallback

The Prolog clauses expose selection, allocation, and final invocation as
separate predicates.  `PrologDnuSelection` composes with the independently
proved unrestricted-lookup bridge.  The fallback relation then fixes the
fresh-message-mirror state transition using the same `finishDnu` graph that
the Prolog allocation clauses present field by field. -/

inductive PrologDnuSelection (p : Program) (h : Heap)
    (lookupStart : ClassId) : LookupResult → Prop where
  | found {result : LookupResult} :
      PrologUnrestrictedLookup p h Program.doesNotUnderstandSelector
        lookupStart (some result) →
      PrologDnuSelection p h lookupStart result

theorem prologDnuSelection_iff {p : Program} {h : Heap}
    {lookupStart : ClassId} {result : LookupResult} :
    PrologDnuSelection p h lookupStart result ↔
      p.DnuSelection h lookupStart result := by
  constructor
  · intro derivation
    cases derivation with
    | found lookup => exact .found (prologUnrestricted_iff_rules.mp lookup)
  · intro derivation
    cases derivation with
    | found lookup => exact .found (prologUnrestricted_iff_rules.mpr lookup)

inductive PrologAllocateMessageMirror (p : Program) (state : AllocationState)
    (message : Message) : AllocationState → ObjRef → Prop where
  | allocate :
      PrologAllocateMessageMirror p state message
        { state with
          heap := state.heap.installMirror ⟨state.nextMirror⟩
            (p.messageMirrorDefinition message)
          nextMirror := state.nextMirror + 1 }
        (.mirrorObject ⟨state.nextMirror⟩)

theorem prologAllocateMessageMirror_iff {p : Program}
    {state nextState : AllocationState} {message : Message}
    {reference : ObjRef} :
    PrologAllocateMessageMirror p state message nextState reference ↔
      p.allocateMessageMirror state message = (nextState, reference) := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    have stateEquality := congrArg Prod.fst equality
    have referenceEquality := congrArg Prod.snd equality
    simp [Program.allocateMessageMirror] at stateEquality referenceEquality
    subst nextState
    subst reference
    exact .allocate

inductive PrologFinishDnu (p : Program) (state : AllocationState)
    (receiver : ObjRef) (original : Message) (lookup : LookupResult) :
    AllocationState → DispatchResult → Prop where
  | finish {nextState : AllocationState} {mirror : ObjRef} :
      PrologAllocateMessageMirror p state original nextState mirror →
      PrologFinishDnu p state receiver original lookup nextState
        (.invoke lookup.method receiver lookup.definingClass
          ⟨Program.doesNotUnderstandSelector, [mirror]⟩)

theorem prologFinishDnu_iff {p : Program} {state nextState : AllocationState}
    {receiver : ObjRef} {original : Message} {lookup : LookupResult}
    {result : DispatchResult} :
    PrologFinishDnu p state receiver original lookup nextState result ↔
      p.finishDnu state receiver original lookup = (nextState, result) := by
  constructor
  · intro derivation
    cases derivation with
    | finish allocation =>
        have equality := prologAllocateMessageMirror_iff.mp allocation
        simp [Program.finishDnu, equality]
  · intro equality
    have canonical :
        PrologFinishDnu p state receiver original lookup
          (p.finishDnu state receiver original lookup).1
          (p.finishDnu state receiver original lookup).2 := by
      exact .finish .allocate
    have stateEquality := congrArg Prod.fst equality
    have resultEquality := congrArg Prod.snd equality
    rw [stateEquality, resultEquality] at canonical
    exact canonical

inductive PrologDnuFallback (p : Program) (state : AllocationState)
    (receiver : ObjRef) (lookupStart : ClassId) (original : Message) :
    AllocationState → DispatchResult → Prop where
  | apply {lookup : LookupResult} {nextState : AllocationState}
      {result : DispatchResult}
      (selection : PrologDnuSelection p state.heap lookupStart lookup)
      (finish : PrologFinishDnu p state receiver original lookup
        nextState result) :
      PrologDnuFallback p state receiver lookupStart original nextState result

theorem prologDnuFallback_iff {p : Program} {state : AllocationState}
    {receiver : ObjRef} {lookupStart : ClassId} {original : Message}
    {nextState : AllocationState} {result : DispatchResult} :
    PrologDnuFallback p state receiver lookupStart original nextState result ↔
      p.DnuFallback state receiver lookupStart original nextState result := by
  constructor
  · intro derivation
    cases derivation with
    | @apply lookup _ _ selection finish =>
        have equality := prologFinishDnu_iff.mp finish
        have stateEquality := congrArg Prod.fst equality
        have resultEquality := congrArg Prod.snd equality
        have canonical :
            p.DnuFallback state receiver lookupStart original
              (p.finishDnu state receiver original lookup).1
              (p.finishDnu state receiver original lookup).2 :=
          .apply (prologDnuSelection_iff.mp selection)
        rw [stateEquality, resultEquality] at canonical
        exact canonical
  · intro derivation
    cases derivation with
    | apply selection =>
        exact .apply (prologDnuSelection_iff.mpr selection)
          (prologFinishDnu_iff.mpr rfl)

/-! ## Request resolution and completion

`ResolveRequest` excludes direct closure-value calls from its ordinary branch.
The Prolog source expresses that complement positively, by object tag or by
the three ways a closure object can fail the call test. -/

inductive PrologNotClosureCall (h : Heap) : ObjRef → Message → Prop where
  | ordinaryObject {id : ObjectId} {message : Message} :
      PrologNotClosureCall h (.ordinaryObject id) message
  | classObject {id : ClassId} {message : Message} :
      PrologNotClosureCall h (.classObject id) message
  | mixinObject {id : MixinId} {message : Message} :
      PrologNotClosureCall h (.mixinObject id) message
  | activationObject {id : ActivationId} {message : Message} :
      PrologNotClosureCall h (.activationObject id) message
  | mirrorObject {id : MirrorId} {message : Message} :
      PrologNotClosureCall h (.mirrorObject id) message
  | actorObject {id : ActorId} {message : Message} :
      PrologNotClosureCall h (.actorObject id) message
  | closureAbsent {id : ClosureId} {message : Message} :
      h.closures id = none →
      PrologNotClosureCall h (.closureObject id) message
  | selectorMismatch {id : ClosureId} {message : Message}
      {closure : ClosureDef} :
      h.closures id = some closure →
      message.selector ≠ valueSelector closure.parameters.length →
      PrologNotClosureCall h (.closureObject id) message
  | arityMismatch {id : ClosureId} {message : Message}
      {closure : ClosureDef} :
      h.closures id = some closure →
      message.arguments.length ≠ closure.parameters.length →
      PrologNotClosureCall h (.closureObject id) message

theorem prologNotClosureCall_iff {h : Heap} {receiver : ObjRef}
    {message : Message} :
    PrologNotClosureCall h receiver message ↔
      ¬h.ClosureCall receiver message := by
  constructor
  · intro derivation call
    rcases call with ⟨id, closure, receiverEq, closureEq, selectorEq, arityEq⟩
    cases derivation with
    | ordinaryObject => cases receiverEq
    | classObject => cases receiverEq
    | mixinObject => cases receiverEq
    | activationObject => cases receiverEq
    | mirrorObject => cases receiverEq
    | actorObject => cases receiverEq
    | closureAbsent absent =>
        cases receiverEq
        rw [absent] at closureEq
        contradiction
    | selectorMismatch present mismatch =>
        cases receiverEq
        have closureIdentity := Option.some.inj (present.symm.trans closureEq)
        subst closure
        exact mismatch selectorEq
    | arityMismatch present mismatch =>
        cases receiverEq
        have closureIdentity := Option.some.inj (present.symm.trans closureEq)
        subst closure
        exact mismatch arityEq
  · intro notCall
    cases receiver with
    | ordinaryObject => exact .ordinaryObject
    | classObject => exact .classObject
    | mixinObject => exact .mixinObject
    | activationObject => exact .activationObject
    | mirrorObject => exact .mirrorObject
    | actorObject => exact .actorObject
    | closureObject id =>
        cases present : h.closures id with
        | none => exact .closureAbsent present
        | some closure =>
            by_cases selectorMatches :
                message.selector = valueSelector closure.parameters.length
            · by_cases arityMatches :
                  message.arguments.length = closure.parameters.length
              · exfalso
                exact notCall ⟨id, closure, rfl, present,
                  selectorMatches, arityMatches⟩
              · exact .arityMismatch present arityMatches
            · exact .selectorMismatch present selectorMatches

inductive PrologResolveRequest (p : Program) (h : Heap)
    (activationId : ActivationId) :
    SendRequest → Message → DispatchResult → Prop where
  | ordinary {receiver : ObjRef} {message : Message} {result : DispatchResult} :
      PrologNotClosureCall h receiver message →
      PrologOrdinaryDispatch p h receiver message result →
      PrologResolveRequest p h activationId (.ordinary receiver) message result
  | implicit {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {message : Message} {result : DispatchResult} :
      PrologImplicitDispatch p h activationId immediate annotation message result →
      PrologResolveRequest p h activationId (.implicit annotation immediate)
        message result
  | outer {target immediate : ClassDeclId} {message : Message}
      {result : DispatchResult} :
      PrologOuterDispatch p h activationId target immediate message result →
      PrologResolveRequest p h activationId (.outer target immediate) message result
  | self {immediate : ClassDeclId} {message : Message}
      {result : DispatchResult} :
      PrologSelfDispatch p h activationId immediate message result →
      PrologResolveRequest p h activationId (.self immediate) message result
  | super {message : Message} {result : DispatchResult} :
      PrologSuperDispatch p h activationId message result →
      PrologResolveRequest p h activationId .super message result

theorem prologResolveRequest_iff {p : Program} {h : Heap}
    {activationId : ActivationId} {request : SendRequest} {message : Message}
    {result : DispatchResult} :
    PrologResolveRequest p h activationId request message result ↔
      p.ResolveRequest h activationId request message result := by
  constructor
  · intro derivation
    cases derivation with
    | ordinary notClosure dispatch =>
        exact .ordinary (prologNotClosureCall_iff.mp notClosure)
          (prologOrdinaryDispatch_iff.mp dispatch)
    | implicit dispatch =>
        exact .implicit (prologImplicitDispatch_iff.mp dispatch)
    | outer dispatch => exact .outer (prologOuterDispatch_iff.mp dispatch)
    | self dispatch => exact .self (prologSelfDispatch_iff.mp dispatch)
    | super dispatch => exact .super (prologSuperDispatch_iff.mp dispatch)
  · intro derivation
    cases derivation with
    | ordinary notClosure dispatch =>
        exact .ordinary (prologNotClosureCall_iff.mpr notClosure)
          (prologOrdinaryDispatch_iff.mpr dispatch)
    | implicit dispatch =>
        exact .implicit (prologImplicitDispatch_iff.mpr dispatch)
    | outer dispatch => exact .outer (prologOuterDispatch_iff.mpr dispatch)
    | self dispatch => exact .self (prologSelfDispatch_iff.mpr dispatch)
    | super dispatch => exact .super (prologSuperDispatch_iff.mpr dispatch)

inductive PrologCompleteRequest (p : Program) (state : AllocationState)
    (activationId : ActivationId) (request : SendRequest) (message : Message) :
    AllocationState → DispatchResult → Prop where
  | invoke {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId} :
      PrologResolveRequest p state.heap activationId request message
        (.invoke method receiver definingClass message) →
      PrologCompleteRequest p state activationId request message state
        (.invoke method receiver definingClass message)
  | invalidSuper {currentClass : ClassId} :
      PrologResolveRequest p state.heap activationId request message
        (.invalidSuper currentClass) →
      PrologCompleteRequest p state activationId request message state
        (.invalidSuper currentClass)
  | dnu {receiver : ObjRef} {lookupStart : ClassId}
      {nextState : AllocationState} {result : DispatchResult}
      {chain : List ClassId} :
      PrologResolveRequest p state.heap activationId request message
        (.missing receiver lookupStart message) →
      PrologClassChain p state.heap lookupStart chain →
      PrologDnuFallback p state receiver lookupStart message nextState result →
      PrologCompleteRequest p state activationId request message nextState result

theorem prologCompleteRequest_iff {p : Program} {state : AllocationState}
    {activationId : ActivationId} {request : SendRequest} {message : Message}
    {nextState : AllocationState} {result : DispatchResult} :
    PrologCompleteRequest p state activationId request message nextState result ↔
      p.CompleteRequest state activationId request message nextState result := by
  constructor
  · intro derivation
    cases derivation with
    | invoke resolution =>
        exact .invoke (prologResolveRequest_iff.mp resolution)
    | invalidSuper resolution =>
        exact .invalidSuper (prologResolveRequest_iff.mp resolution)
    | dnu resolution chain fallback =>
        exact .dnu (prologResolveRequest_iff.mp resolution)
          ⟨_, prologClassChain_iff.mp chain⟩
          (prologDnuFallback_iff.mp fallback)
  · intro derivation
    cases derivation with
    | invoke resolution =>
        exact .invoke (prologResolveRequest_iff.mpr resolution)
    | invalidSuper resolution =>
        exact .invalidSuper (prologResolveRequest_iff.mpr resolution)
    | dnu resolution hasChain fallback =>
        rcases hasChain with ⟨chain, chainProof⟩
        exact .dnu (prologResolveRequest_iff.mpr resolution)
          (prologClassChain_iff.mpr chainProof)
          (prologDnuFallback_iff.mpr fallback)

/-! ## Method activation and invocation -/

inductive PrologAllocateMethodActivation (p : Program)
    (state : AllocationState) (method : MethodDef) (receiver : ObjRef)
    (definingClass : ClassId) (message : Message)
    (continuation : Option ActivationId) :
    AllocationState → ActivationId → Prop where
  | allocate :
      PrologAllocateMethodActivation p state method receiver definingClass
        message continuation
        { state with
          heap := state.heap.installActivation ⟨state.nextActivation⟩
            (p.methodActivationDefinition ⟨state.nextActivation⟩ method
              receiver definingClass message continuation)
          nextActivation := state.nextActivation + 1 }
        ⟨state.nextActivation⟩

theorem prologAllocateMethodActivation_iff {p : Program}
    {state nextState : AllocationState} {method : MethodDef}
    {receiver : ObjRef} {definingClass : ClassId} {message : Message}
    {continuation : Option ActivationId} {activation : ActivationId} :
    PrologAllocateMethodActivation p state method receiver definingClass
      message continuation nextState activation ↔
      p.allocateMethodActivation state method receiver definingClass message
        continuation = (nextState, activation) := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    have stateEquality := congrArg Prod.fst equality
    have activationEquality := congrArg Prod.snd equality
    simp [Program.allocateMethodActivation] at stateEquality
    simp [Program.allocateMethodActivation] at activationEquality
    subst nextState
    subst activation
    exact .allocate

inductive PrologMethodInvocationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | nonTail {state nextState : AllocationState} {rest : ActivationStack}
      {current newActivation : ActivationId} {frames : EvalStack}
      {topFrame : EvalFrame} {method : MethodDef} {receiver : ObjRef}
      {definingClass : ClassId} {message : Message}
      {locals : List LocalDeclarationGroup} {body : List Statement} :
      method.selector = message.selector →
      method.parameters.length = message.arguments.length →
      p.methodLocals method.identity = locals →
      p.methodBodies method.identity = some body →
      PrologAllocateMethodActivation p state method receiver definingClass
        message (some current) nextState newActivation →
      PrologMethodInvocationStep p
        ⟨state, .push rest ⟨current, .push frames topFrame⟩,
          .invoke method receiver definingClass message⟩
        (p.nonTailInvocationTarget state rest current (.push frames topFrame)
          method receiver definingClass message locals body)
  | tail {state nextState : AllocationState} {rest : ActivationStack}
      {current newActivation : ActivationId} {currentDef : ActivationDef}
      {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
      {message : Message} {locals : List LocalDeclarationGroup}
      {body : List Statement} :
      state.heap.activations current = some currentDef →
      method.selector = message.selector →
      method.parameters.length = message.arguments.length →
      p.methodLocals method.identity = locals →
      p.methodBodies method.identity = some body →
      PrologAllocateMethodActivation p state method receiver definingClass
        message currentDef.continuation nextState newActivation →
      PrologMethodInvocationStep p
        ⟨state, .push rest ⟨current, .empty⟩,
          .invoke method receiver definingClass message⟩
        (p.tailInvocationTarget state rest currentDef method receiver
          definingClass message locals body)

theorem prologMethodInvocationStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologMethodInvocationStep p before after ↔
      p.MethodInvocationStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | nonTail selector arity locals body allocation =>
        exact .nonTail selector arity locals body
    | tail current selector arity locals body allocation =>
        exact .tail current selector arity locals body
  · intro derivation
    cases derivation with
    | nonTail selector arity locals body =>
        exact .nonTail selector arity locals body
          (prologAllocateMethodActivation_iff.mpr rfl)
    | tail current selector arity locals body =>
        exact .tail current selector arity locals body
          (prologAllocateMethodActivation_iff.mpr rfl)

inductive PrologRequestCompletionStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | invoke {state nextState : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {request : SendRequest}
      {message finalMessage : Message} {method : MethodDef}
      {receiver : ObjRef} {definingClass : ClassId} :
      PrologCompleteRequest p state current request message nextState
        (.invoke method receiver definingClass finalMessage) →
      PrologRequestCompletionStep p
        ⟨state, .push rest ⟨current, frames⟩, .dispatch request message⟩
        ⟨nextState, .push rest ⟨current, frames⟩,
          .invoke method receiver definingClass finalMessage⟩
  | invalidSuper {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {request : SendRequest}
      {message : Message} {currentClass : ClassId} :
      PrologCompleteRequest p state current request message state
        (.invalidSuper currentClass) →
      PrologRequestCompletionStep p
        ⟨state, .push rest ⟨current, frames⟩, .dispatch request message⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .runtimeError (.invalidSuper currentClass)⟩

theorem prologRequestCompletionStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologRequestCompletionStep p before after ↔
      p.RequestCompletionStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | invoke completion =>
        exact .invoke (prologCompleteRequest_iff.mp completion)
    | invalidSuper completion =>
        exact .invalidSuper (prologCompleteRequest_iff.mp completion)
  · intro derivation
    cases derivation with
    | invoke completion =>
        exact .invoke (prologCompleteRequest_iff.mpr completion)
    | invalidSuper completion =>
        exact .invalidSuper (prologCompleteRequest_iff.mpr completion)

/-! ## Closure construction, dispatch, and invocation -/

inductive PrologAllocateClosureObject (p : Program)
    (state : AllocationState) (closure : ClosureDef) :
    AllocationState → ClosureId → Prop where
  | allocate :
      PrologAllocateClosureObject p state closure
        { state with
          heap := state.heap.installClosure ⟨state.nextClosure⟩ closure
          nextClosure := state.nextClosure + 1 }
        ⟨state.nextClosure⟩

theorem prologAllocateClosureObject_iff {p : Program}
    {state nextState : AllocationState} {closure : ClosureDef}
    {id : ClosureId} :
    PrologAllocateClosureObject p state closure nextState id ↔
      p.allocateClosureObject state closure = (nextState, id) := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    have stateEquality := congrArg Prod.fst equality
    have idEquality := congrArg Prod.snd equality
    simp [Program.allocateClosureObject] at stateEquality
    simp [Program.allocateClosureObject] at idEquality
    subst nextState
    subst id
    exact .allocate

inductive PrologClosureCreationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | create {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {defining : ActivationDef} {declaration : ActivationDeclId}
      {body : List Statement} {nextState : AllocationState}
      {id : ClosureId} :
      state.heap.activations current = some defining →
      p.closureBodies declaration = some body →
      PrologAllocateClosureObject p state
        (p.closureDefinition current defining declaration body) nextState id →
      PrologClosureCreationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.closureLiteral declaration)⟩
        (p.closureCreationTarget state rest current frames defining declaration body)
  | createCascade {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {defining : ActivationDef} {descriptor : CascadeDescriptor}
      {clauses : List (Selector × List CoreExpr)}
      {nextState : AllocationState} {id : ClosureId} :
      state.heap.activations current = some defining →
      PrologAllocateClosureObject p state
        (p.cascadeClosureDefinition current defining descriptor clauses)
        nextState id →
      PrologClosureCreationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.cascadeClosure descriptor clauses)⟩
        (p.cascadeClosureCreationTarget state rest current frames defining
          descriptor clauses)

theorem prologClosureCreationStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologClosureCreationStep p before after ↔
      p.ClosureCreationStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | create current body allocation => exact .create current body
    | createCascade current allocation => exact .createCascade current
  · intro derivation
    cases derivation with
    | create current body =>
        exact .create current body (prologAllocateClosureObject_iff.mpr rfl)
    | createCascade current =>
        exact .createCascade current
          (prologAllocateClosureObject_iff.mpr rfl)

inductive PrologClosureDispatchStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | value {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {id : ClosureId}
      {closure : ClosureDef} {message : Message} :
      state.heap.closures id = some closure →
      message.selector = valueSelector closure.parameters.length →
      message.arguments.length = closure.parameters.length →
      PrologClosureDispatchStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary (.closureObject id)) message⟩
        ⟨state, .push rest ⟨current, frames⟩, .invokeClosure id message⟩

theorem prologClosureDispatchStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologClosureDispatchStep p before after ↔
      p.ClosureDispatchStep before after := by
  constructor <;> intro derivation <;> cases derivation with
  | value live selector arity => exact .value live selector arity

inductive PrologAllocateClosureActivation (p : Program)
    (state : AllocationState) (closure : ClosureDef)
    (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId) :
    AllocationState → ActivationId → Prop where
  | allocate :
      PrologAllocateClosureActivation p state closure defining message
        continuation
        { state with
          heap := state.heap.installActivation ⟨state.nextActivation⟩
            (p.closureActivationDefinition ⟨state.nextActivation⟩ closure
              defining message continuation)
          nextActivation := state.nextActivation + 1 }
        ⟨state.nextActivation⟩

theorem prologAllocateClosureActivation_iff {p : Program}
    {state nextState : AllocationState} {closure : ClosureDef}
    {defining : ActivationDef} {message : Message}
    {continuation : Option ActivationId} {id : ActivationId} :
    PrologAllocateClosureActivation p state closure defining message
      continuation nextState id ↔
      p.allocateClosureActivation state closure defining message continuation =
        (nextState, id) := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    have stateEquality := congrArg Prod.fst equality
    have idEquality := congrArg Prod.snd equality
    simp [Program.allocateClosureActivation] at stateEquality
    simp [Program.allocateClosureActivation] at idEquality
    subst nextState
    subst id
    exact .allocate

inductive PrologClosureInvocationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | nonTail {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {topFrame : EvalFrame}
      {id : ClosureId} {closure : ClosureDef} {defining : ActivationDef}
      {message : Message} {nextState : AllocationState}
      {newActivation : ActivationId} :
      state.heap.closures id = some closure →
      state.heap.activations closure.definingActivation = some defining →
      message.selector = valueSelector closure.parameters.length →
      message.arguments.length = closure.parameters.length →
      PrologAllocateClosureActivation p state closure defining message
        (some current) nextState newActivation →
      PrologClosureInvocationStep p
        ⟨state, .push rest ⟨current, .push frames topFrame⟩,
          .invokeClosure id message⟩
        (p.nonTailClosureInvocationTarget state rest current
          (.push frames topFrame) closure defining message)
  | tail {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {caller defining : ActivationDef}
      {closure : ClosureDef} {id : ClosureId} {message : Message}
      {nextState : AllocationState} {newActivation : ActivationId} :
      state.heap.activations current = some caller →
      state.heap.closures id = some closure →
      state.heap.activations closure.definingActivation = some defining →
      message.selector = valueSelector closure.parameters.length →
      message.arguments.length = closure.parameters.length →
      PrologAllocateClosureActivation p state closure defining message
        caller.continuation nextState newActivation →
      PrologClosureInvocationStep p
        ⟨state, .push rest ⟨current, .empty⟩, .invokeClosure id message⟩
        (p.tailClosureInvocationTarget state rest caller closure defining message)

theorem prologClosureInvocationStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologClosureInvocationStep p before after ↔
      p.ClosureInvocationStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | nonTail live defining selector arity allocation =>
        exact .nonTail live defining selector arity
    | tail caller live defining selector arity allocation =>
        exact .tail caller live defining selector arity
  · intro derivation
    cases derivation with
    | nonTail live defining selector arity =>
        exact .nonTail live defining selector arity
          (prologAllocateClosureActivation_iff.mpr rfl)
    | tail caller live defining selector arity =>
        exact .tail caller live defining selector arity
          (prologAllocateClosureActivation_iff.mpr rfl)

inductive PrologClosureMachineStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | creation {before after : SequentialConfig} :
      PrologClosureCreationStep p before after →
      PrologClosureMachineStep p before after
  | dispatch {before after : SequentialConfig} :
      PrologClosureDispatchStep p before after →
      PrologClosureMachineStep p before after
  | invocation {before after : SequentialConfig} :
      PrologClosureInvocationStep p before after →
      PrologClosureMachineStep p before after

theorem prologClosureMachineStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologClosureMachineStep p before after ↔
      p.ClosureMachineStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | creation step => exact .creation (prologClosureCreationStep_iff.mp step)
    | dispatch step => exact .dispatch (prologClosureDispatchStep_iff.mp step)
    | invocation step => exact .invocation (prologClosureInvocationStep_iff.mp step)
  · intro derivation
    cases derivation with
    | creation step => exact .creation (prologClosureCreationStep_iff.mpr step)
    | dispatch step => exact .dispatch (prologClosureDispatchStep_iff.mpr step)
    | invocation step => exact .invocation (prologClosureInvocationStep_iff.mpr step)

/-! ## Expression and message evaluation order -/

inductive PrologNonOrdinaryRequest : CoreExpr → PendingSend → Prop where
  | implicit {selector : Selector} {arguments : List CoreExpr}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId} :
      PrologNonOrdinaryRequest
        (.implicitSend selector arguments annotation immediate)
        ⟨.implicit annotation immediate, selector, arguments⟩
  | self {selector : Selector} {arguments : List CoreExpr}
      {immediate : ClassDeclId} :
      PrologNonOrdinaryRequest
        (.selfSend selector arguments immediate)
        ⟨.self immediate, selector, arguments⟩
  | outer {selector : Selector} {arguments : List CoreExpr}
      {target immediate : ClassDeclId} :
      PrologNonOrdinaryRequest
        (.outerSend selector arguments target immediate)
        ⟨.outer target immediate, selector, arguments⟩
  | super {selector : Selector} {arguments : List CoreExpr} :
      PrologNonOrdinaryRequest
        (.superSend selector arguments)
        ⟨.super, selector, arguments⟩

theorem prologNonOrdinaryRequest_iff {expression : CoreExpr}
    {pending : PendingSend} :
    PrologNonOrdinaryRequest expression pending ↔
      nonOrdinaryRequest expression = some pending := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases expression with
    | implicitSend selector arguments annotation immediate =>
        simp [nonOrdinaryRequest] at equality
        subst pending
        exact .implicit
    | selfSend selector arguments immediate =>
        simp [nonOrdinaryRequest] at equality
        subst pending
        exact .self
    | outerSend selector arguments target immediate =>
        simp [nonOrdinaryRequest] at equality
        subst pending
        exact .outer
    | superSend selector arguments =>
        simp [nonOrdinaryRequest] at equality
        subst pending
        exact .super
    | value | selfValue | ordinarySend | eventualSend | closureLiteral
      | cascadeClosure | readLocal | writeLocal | classBody | mixinApply
      | objectLiteral | atom | tuple | pattern | cascade | readSlot
      | writeSlot | currentRead | currentWrite | lazyRead | nestedClass
      | newInstanceCurrent =>
        simp [nonOrdinaryRequest] at equality

inductive PrologStartPendingSend (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack) :
    PendingSend → SequentialConfig → Prop where
  | noArguments {request : SendRequest} {selector : Selector} :
      PrologStartPendingSend state rest current frames
        ⟨request, selector, []⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .dispatch request ⟨selector, []⟩⟩
  | firstArgument {request : SendRequest} {selector : Selector}
      {first : CoreExpr} {remaining : List CoreExpr} :
      PrologStartPendingSend state rest current frames
        ⟨request, selector, first :: remaining⟩
        ⟨state,
          .push rest ⟨current,
            .push frames (.arguments request selector [] remaining)⟩,
          .evaluate first⟩

theorem prologStartPendingSend_iff {state : AllocationState}
    {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
    {pending : PendingSend} {after : SequentialConfig} :
    PrologStartPendingSend state rest current frames pending after ↔
      startPendingSend state rest current frames pending = after := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    rcases pending with ⟨request, selector, arguments⟩
    cases arguments with
    | nil =>
        simp [startPendingSend] at equality
        subst after
        exact .noArguments
    | cons first remaining =>
        simp [startPendingSend] at equality
        subst after
        exact .firstArgument

inductive PrologContinueReceiver (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (receiver : ObjRef) (selector : Selector) :
    List CoreExpr → SequentialConfig → Prop where
  | noArguments :
      PrologContinueReceiver state rest current frames receiver selector []
        ⟨state, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary receiver) ⟨selector, []⟩⟩
  | firstArgument {first : CoreExpr} {remaining : List CoreExpr} :
      PrologContinueReceiver state rest current frames receiver selector
        (first :: remaining)
        ⟨state,
          .push rest ⟨current,
            .push frames (.arguments (.ordinary receiver) selector [] remaining)⟩,
          .evaluate first⟩

theorem prologContinueReceiver_iff {state : AllocationState}
    {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
    {receiver : ObjRef} {selector : Selector} {arguments : List CoreExpr}
    {after : SequentialConfig} :
    PrologContinueReceiver state rest current frames receiver selector
      arguments after ↔
      continueReceiver state rest current frames receiver selector arguments =
        after := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases arguments with
    | nil =>
        simp [continueReceiver] at equality
        subst after
        exact .noArguments
    | cons first remaining =>
        simp [continueReceiver] at equality
        subst after
        exact .firstArgument

inductive PrologContinueEventualReceiver (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (receiver : ObjRef) (selector : Selector) :
    List CoreExpr → SequentialConfig → Prop where
  | noArguments :
      PrologContinueEventualReceiver state rest current frames receiver selector
        []
        ⟨state, .push rest ⟨current, frames⟩,
          .dispatch (.eventual receiver) ⟨selector, []⟩⟩
  | firstArgument {first : CoreExpr} {remaining : List CoreExpr} :
      PrologContinueEventualReceiver state rest current frames receiver selector
        (first :: remaining)
        ⟨state,
          .push rest ⟨current,
            .push frames (.arguments (.eventual receiver) selector [] remaining)⟩,
          .evaluate first⟩

theorem prologContinueEventualReceiver_iff {state : AllocationState}
    {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
    {receiver : ObjRef} {selector : Selector} {arguments : List CoreExpr}
    {after : SequentialConfig} :
    PrologContinueEventualReceiver state rest current frames receiver selector
      arguments after ↔
      continueEventualReceiver state rest current frames receiver selector
        arguments = after := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases arguments with
    | nil =>
        simp [continueEventualReceiver] at equality
        subst after
        exact .noArguments
    | cons first remaining =>
        simp [continueEventualReceiver] at equality
        subst after
        exact .firstArgument

inductive PrologContinueArguments (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (request : SendRequest) (selector : Selector) (values : List ObjRef) :
    List CoreExpr → ObjRef → SequentialConfig → Prop where
  | dispatch {value : ObjRef} {accumulated : List ObjRef} :
      PrologListAppend values [value] accumulated →
      PrologContinueArguments state rest current frames request selector values
        [] value
        ⟨state, .push rest ⟨current, frames⟩,
          .dispatch request ⟨selector, accumulated⟩⟩
  | nextArgument {first : CoreExpr} {later : List CoreExpr}
      {value : ObjRef} {accumulated : List ObjRef} :
      PrologListAppend values [value] accumulated →
      PrologContinueArguments state rest current frames request selector values
        (first :: later) value
        ⟨state,
          .push rest ⟨current,
            .push frames (.arguments request selector accumulated later)⟩,
          .evaluate first⟩

theorem prologContinueArguments_iff {state : AllocationState}
    {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
    {request : SendRequest} {selector : Selector} {values : List ObjRef}
    {remaining : List CoreExpr} {value : ObjRef}
    {after : SequentialConfig} :
    PrologContinueArguments state rest current frames request selector values
      remaining value after ↔
      continueArguments state rest current frames request selector values
        remaining value = after := by
  constructor
  · intro derivation
    cases derivation with
    | dispatch append =>
        have accumulated := prologListAppend_iff.mp append
        simp [continueArguments, accumulated]
    | nextArgument append =>
        have accumulated := prologListAppend_iff.mp append
        simp [continueArguments, accumulated]
  · intro equality
    cases remaining with
    | nil =>
        simp [continueArguments] at equality
        subst after
        exact .dispatch (prologListAppend_iff.mpr rfl)
    | cons first later =>
        simp [continueArguments] at equality
        subst after
        exact .nextArgument (prologListAppend_iff.mpr rfl)

inductive PrologExpressionOrderStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | value {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjRef} :
      PrologExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate (.value object)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object object⟩
  | selfValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {activation : ActivationDef} :
      state.heap.activations current = some activation →
      PrologExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate .selfValue⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .object activation.currentReceiver⟩
  | ordinaryReceiver {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : CoreExpr}
      {selector : Selector} {arguments : List CoreExpr} :
      PrologExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.ordinarySend receiver selector arguments)⟩
        ⟨state,
          .push rest ⟨current, .push frames (.receiver selector arguments)⟩,
          .evaluate receiver⟩
  | eventualReceiver {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : CoreExpr}
      {selector : Selector} {arguments : List CoreExpr} :
      PrologExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.eventualSend receiver selector arguments)⟩
        ⟨state,
          .push rest ⟨current,
            .push frames (.asyncReceiver selector arguments)⟩,
          .evaluate receiver⟩
  | nonOrdinary {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {expression : CoreExpr}
      {pending : PendingSend} {after : SequentialConfig} :
      PrologNonOrdinaryRequest expression pending →
      PrologStartPendingSend state rest current frames pending after →
      PrologExpressionOrderStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expression⟩ after
  | receiverValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : ObjRef}
      {selector : Selector} {arguments : List CoreExpr}
      {after : SequentialConfig} :
      PrologContinueReceiver state rest current frames receiver selector
        arguments after →
      PrologExpressionOrderStep p
        ⟨state,
          .push rest ⟨current, .push frames (.receiver selector arguments)⟩,
          .object receiver⟩ after
  | eventualReceiverValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {receiver : ObjRef}
      {selector : Selector} {arguments : List CoreExpr}
      {after : SequentialConfig} :
      PrologContinueEventualReceiver state rest current frames receiver selector
        arguments after →
      PrologExpressionOrderStep p
        ⟨state,
          .push rest ⟨current,
            .push frames (.asyncReceiver selector arguments)⟩,
          .object receiver⟩ after
  | argumentValue {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {request : SendRequest}
      {selector : Selector} {values : List ObjRef}
      {remaining : List CoreExpr} {value : ObjRef}
      {after : SequentialConfig} :
      PrologContinueArguments state rest current frames request selector values
        remaining value after →
      PrologExpressionOrderStep p
        ⟨state,
          .push rest ⟨current,
            .push frames (.arguments request selector values remaining)⟩,
          .object value⟩ after

theorem prologExpressionOrderStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologExpressionOrderStep p before after ↔
      p.ExpressionOrderStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | value => exact .value
    | selfValue current => exact .selfValue current
    | ordinaryReceiver => exact .ordinaryReceiver
    | eventualReceiver => exact .eventualReceiver
    | @nonOrdinary state rest current frames expression pending after
        request start =>
        have requestData := prologNonOrdinaryRequest_iff.mp request
        have target := prologStartPendingSend_iff.mp start
        have step := Program.ExpressionOrderStep.nonOrdinary (p := p)
          (state := state) (rest := rest) (current := current)
          (frames := frames) requestData
        rw [target] at step
        exact step
    | @receiverValue state rest current frames receiver selector arguments
        after continuation =>
        have target := prologContinueReceiver_iff.mp continuation
        have step := Program.ExpressionOrderStep.receiverValue (p := p)
          (state := state) (rest := rest) (current := current)
          (frames := frames) (receiver := receiver) (selector := selector)
          (arguments := arguments)
        rw [target] at step
        exact step
    | @eventualReceiverValue state rest current frames receiver selector
        arguments after continuation =>
        have target := prologContinueEventualReceiver_iff.mp continuation
        have step := Program.ExpressionOrderStep.eventualReceiverValue (p := p)
          (state := state) (rest := rest) (current := current)
          (frames := frames) (receiver := receiver) (selector := selector)
          (arguments := arguments)
        rw [target] at step
        exact step
    | @argumentValue state rest current frames request selector values
        remaining value after continuation =>
        have target := prologContinueArguments_iff.mp continuation
        have step := Program.ExpressionOrderStep.argumentValue (p := p)
          (state := state) (rest := rest) (current := current)
          (frames := frames) (request := request) (selector := selector)
          (values := values) (remaining := remaining) (value := value)
        rw [target] at step
        exact step
  · intro derivation
    cases derivation with
    | value => exact .value
    | selfValue current => exact .selfValue current
    | ordinaryReceiver => exact .ordinaryReceiver
    | eventualReceiver => exact .eventualReceiver
    | nonOrdinary requestData =>
        exact .nonOrdinary
          (prologNonOrdinaryRequest_iff.mpr requestData)
          (prologStartPendingSend_iff.mpr rfl)
    | receiverValue =>
        exact .receiverValue (prologContinueReceiver_iff.mpr rfl)
    | eventualReceiverValue =>
        exact .eventualReceiverValue
          (prologContinueEventualReceiver_iff.mpr rfl)
    | argumentValue =>
        exact .argumentValue (prologContinueArguments_iff.mpr rfl)

inductive PrologStartMessageEvaluation (state : AllocationState)
    (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) :
    MessageTemplate → SequentialConfig → Prop where
  | empty {selector : Selector} :
      PrologStartMessageEvaluation state rest current frames
        ⟨selector, []⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .messageValue ⟨selector, []⟩⟩
  | first {selector : Selector} {first : CoreExpr}
      {remaining : List CoreExpr} :
      PrologStartMessageEvaluation state rest current frames
        ⟨selector, first :: remaining⟩
        ⟨state,
          .push rest ⟨current,
            .push frames (.messageArguments selector [] remaining)⟩,
          .evaluate first⟩

theorem prologStartMessageEvaluation_iff {state : AllocationState}
    {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack}
    {template : MessageTemplate} {after : SequentialConfig} :
    PrologStartMessageEvaluation state rest current frames template after ↔
      Program.startMessageEvaluation state rest current frames template =
        after := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    rcases template with ⟨selector, arguments⟩
    cases arguments with
    | nil =>
        simp [Program.startMessageEvaluation] at equality
        subst after
        exact .empty
    | cons first remaining =>
        simp [Program.startMessageEvaluation] at equality
        subst after
        exact .first

inductive PrologContinueMessageEvaluation (state : AllocationState)
    (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (selector : Selector)
    (values : List ObjRef) :
    List CoreExpr → ObjRef → SequentialConfig → Prop where
  | finish {value : ObjRef} {accumulated : List ObjRef} :
      PrologListAppend values [value] accumulated →
      PrologContinueMessageEvaluation state rest current frames selector
        values [] value
        ⟨state, .push rest ⟨current, frames⟩,
          .messageValue ⟨selector, accumulated⟩⟩
  | next {first : CoreExpr} {later : List CoreExpr}
      {value : ObjRef} {accumulated : List ObjRef} :
      PrologListAppend values [value] accumulated →
      PrologContinueMessageEvaluation state rest current frames selector
        values (first :: later) value
        ⟨state,
          .push rest ⟨current,
            .push frames (.messageArguments selector accumulated later)⟩,
          .evaluate first⟩

theorem prologContinueMessageEvaluation_iff {state : AllocationState}
    {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack} {selector : Selector}
    {values : List ObjRef} {remaining : List CoreExpr} {value : ObjRef}
    {after : SequentialConfig} :
    PrologContinueMessageEvaluation state rest current frames selector values
      remaining value after ↔
      Program.continueMessageEvaluation state rest current frames selector values
        remaining value = after := by
  constructor
  · intro derivation
    cases derivation with
    | finish append =>
        have accumulated := prologListAppend_iff.mp append
        simp [Program.continueMessageEvaluation, accumulated]
    | next append =>
        have accumulated := prologListAppend_iff.mp append
        simp [Program.continueMessageEvaluation, accumulated]
  · intro equality
    cases remaining with
    | nil =>
        simp [Program.continueMessageEvaluation] at equality
        subst after
        exact .finish (prologListAppend_iff.mpr rfl)
    | cons first later =>
        simp [Program.continueMessageEvaluation] at equality
        subst after
        exact .next (prologListAppend_iff.mpr rfl)

inductive PrologMessageEvaluationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | start {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {template : MessageTemplate} {after : SequentialConfig} :
      PrologStartMessageEvaluation state rest current frames template after →
      PrologMessageEvaluationStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluateMessage template⟩ after
  | argument {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {selector : Selector}
      {values : List ObjRef} {remaining : List CoreExpr} {value : ObjRef}
      {after : SequentialConfig} :
      PrologContinueMessageEvaluation state rest current frames selector
        values remaining value after →
      PrologMessageEvaluationStep p
        ⟨state, .push rest ⟨current,
          .push frames (.messageArguments selector values remaining)⟩,
          .object value⟩ after

theorem prologMessageEvaluationStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologMessageEvaluationStep p before after ↔
      p.MessageEvaluationStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | @start state rest current frames template after start =>
        have target := prologStartMessageEvaluation_iff.mp start
        have step := Program.MessageEvaluationStep.start (p := p)
          (state := state) (rest := rest) (current := current)
          (frames := frames) (template := template)
        rw [target] at step
        exact step
    | @argument state rest current frames selector values remaining value after
        continuation =>
        have target := prologContinueMessageEvaluation_iff.mp continuation
        have step := Program.MessageEvaluationStep.argument (p := p)
          (state := state) (rest := rest) (current := current)
          (frames := frames) (selector := selector) (values := values)
          (remaining := remaining) (value := value)
        rw [target] at step
        exact step
  · intro derivation
    cases derivation with
    | start =>
        exact .start (prologStartMessageEvaluation_iff.mpr rfl)
    | argument =>
        exact .argument (prologContinueMessageEvaluation_iff.mpr rfl)

inductive PrologLocalInstallExpression (p : Program)
    (activation : ActivationId) : LocalDeclaration → CoreExpr → Prop where
  | immutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalInstallExpression p activation (.immutable slot initializer)
        (.writeLocal activation slot
          (.ordinarySend (p.pastFutureExpression activation) computingSelector
            [initializer]))
  | mutableInitialized {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalInstallExpression p activation
        (.mutableInitialized slot initializer)
        (.writeLocal activation slot
          (.ordinarySend (p.pastFutureExpression activation) computingSelector
            [initializer]))
  | mutableUninitialized {slot : LocalSlotId} :
      PrologLocalInstallExpression p activation (.mutableUninitialized slot)
        (.writeLocal activation slot (.value p.nilObject))
  | lazyImmutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalInstallExpression p activation (.lazyImmutable slot initializer)
        (.writeLocal activation slot (.value p.nilObject))
  | lazyMutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalInstallExpression p activation (.lazyMutable slot initializer)
        (.writeLocal activation slot (.value p.nilObject))

theorem prologLocalInstallExpression_iff {p : Program}
    {activation : ActivationId} {declaration : LocalDeclaration}
    {expression : CoreExpr} :
    PrologLocalInstallExpression p activation declaration expression ↔
      p.localInstallExpression activation declaration = expression := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;>
      simp [Program.localInstallExpression] at equality <;>
      subst expression <;> constructor

inductive PrologLocalResolveExpression (activation : ActivationId) :
    LocalDeclaration → Option CoreExpr → Prop where
  | immutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalResolveExpression activation (.immutable slot initializer)
        (some (.ordinarySend (.readLocal activation slot) resolveSelector []))
  | mutableInitialized {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalResolveExpression activation
        (.mutableInitialized slot initializer)
        (some (.ordinarySend (.readLocal activation slot) resolveSelector []))
  | mutableUninitialized {slot : LocalSlotId} :
      PrologLocalResolveExpression activation (.mutableUninitialized slot) none
  | lazyImmutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalResolveExpression activation (.lazyImmutable slot initializer)
        none
  | lazyMutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologLocalResolveExpression activation (.lazyMutable slot initializer)
        none

theorem prologLocalResolveExpression_iff {activation : ActivationId}
    {declaration : LocalDeclaration} {expression : Option CoreExpr} :
    PrologLocalResolveExpression activation declaration expression ↔
      localResolveExpression activation declaration = expression := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;>
      simp [localResolveExpression, eagerLocalInitializer] at equality <;>
      subst expression <;> constructor

inductive PrologLocalInstallExpressions (p : Program)
    (activation : ActivationId) :
    List LocalDeclaration → List CoreExpr → Prop where
  | nil : PrologLocalInstallExpressions p activation [] []
  | cons {declaration : LocalDeclaration}
      {declarations : List LocalDeclaration} {expression : CoreExpr}
      {expressions : List CoreExpr} :
      PrologLocalInstallExpression p activation declaration expression →
      PrologLocalInstallExpressions p activation declarations expressions →
      PrologLocalInstallExpressions p activation (declaration :: declarations)
        (expression :: expressions)

theorem prologLocalInstallExpressions_iff {p : Program}
    {activation : ActivationId} {declarations : List LocalDeclaration}
    {expressions : List CoreExpr} :
    PrologLocalInstallExpressions p activation declarations expressions ↔
      declarations.map (p.localInstallExpression activation) = expressions := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons head tail ih =>
        simp [prologLocalInstallExpression_iff.mp head, ih]
  · intro equality
    induction declarations generalizing expressions with
    | nil =>
        simp at equality
        subst expressions
        exact .nil
    | cons declaration declarations ih =>
        simp at equality
        subst expressions
        exact .cons (prologLocalInstallExpression_iff.mpr rfl) (ih rfl)

inductive PrologLocalResolveExpressions (activation : ActivationId) :
    List LocalDeclaration → List CoreExpr → Prop where
  | nil : PrologLocalResolveExpressions activation [] []
  | some {declaration : LocalDeclaration}
      {declarations : List LocalDeclaration} {expression : CoreExpr}
      {expressions : List CoreExpr} :
      PrologLocalResolveExpression activation declaration (some expression) →
      PrologLocalResolveExpressions activation declarations expressions →
      PrologLocalResolveExpressions activation (declaration :: declarations)
        (expression :: expressions)
  | none {declaration : LocalDeclaration}
      {declarations : List LocalDeclaration} {expressions : List CoreExpr} :
      PrologLocalResolveExpression activation declaration none →
      PrologLocalResolveExpressions activation declarations expressions →
      PrologLocalResolveExpressions activation (declaration :: declarations)
        expressions

theorem prologLocalResolveExpressions_iff {activation : ActivationId}
    {declarations : List LocalDeclaration} {expressions : List CoreExpr} :
    PrologLocalResolveExpressions activation declarations expressions ↔
      declarations.filterMap (localResolveExpression activation) =
        expressions := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | some head tail ih =>
        simp [prologLocalResolveExpression_iff.mp head, ih]
    | none head tail ih =>
        simp [prologLocalResolveExpression_iff.mp head, ih]
  · intro equality
    induction declarations generalizing expressions with
    | nil =>
        simp at equality
        subst expressions
        exact .nil
    | cons declaration declarations ih =>
        cases resolution : localResolveExpression activation declaration with
        | none =>
            simp [resolution] at equality
            exact .none (prologLocalResolveExpression_iff.mpr resolution)
              (ih equality)
        | some expression =>
            simp [resolution] at equality
            subst expressions
            exact .some (prologLocalResolveExpression_iff.mpr resolution)
              (ih rfl)

inductive PrologLocalSimCode (p : Program) (activation : ActivationId) :
    List LocalDeclaration → List CoreExpr → Prop where
  | build {declarations : List LocalDeclaration}
      {installations resolutions code : List CoreExpr} :
      PrologLocalInstallExpressions p activation declarations installations →
      PrologLocalResolveExpressions activation declarations resolutions →
      PrologListAppend installations resolutions code →
      PrologLocalSimCode p activation declarations code

theorem prologLocalSimCode_iff {p : Program} {activation : ActivationId}
    {declarations : List LocalDeclaration} {code : List CoreExpr} :
    PrologLocalSimCode p activation declarations code ↔
      p.localSimCode activation declarations = code := by
  constructor
  · intro derivation
    cases derivation with
    | build installations resolutions append =>
        rw [Program.localSimCode]
        rw [prologLocalInstallExpressions_iff.mp installations]
        rw [prologLocalResolveExpressions_iff.mp resolutions]
        exact prologListAppend_iff.mp append
  · intro equality
    exact .build (prologLocalInstallExpressions_iff.mpr rfl)
      (prologLocalResolveExpressions_iff.mpr rfl)
      (prologListAppend_iff.mpr equality)

inductive PrologStartSimultaneousLocals (p : Program)
    (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack)
    (activation : ActivationId) (declarations : List LocalDeclaration)
    (remaining : List LocalDeclarationGroup) (body : List Statement)
    (target : InitializationTarget) : SequentialConfig → Prop where
  | empty :
      PrologLocalSimCode p activation declarations [] →
      PrologStartSimultaneousLocals p state rest current frames activation
        declarations remaining body target
        ⟨state, .push rest ⟨current, frames⟩,
          .initialize activation remaining body target⟩
  | nonempty {first : CoreExpr} {later : List CoreExpr} :
      PrologLocalSimCode p activation declarations (first :: later) →
      PrologStartSimultaneousLocals p state rest current frames activation
        declarations remaining body target
        ⟨state, .push rest ⟨current,
          .push frames
            (.simultaneousLocals later activation remaining body target)⟩,
          .evaluate first⟩

theorem prologStartSimultaneousLocals_iff {p : Program}
    {state : AllocationState} {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack}
    {activation : ActivationId} {declarations : List LocalDeclaration}
    {remaining : List LocalDeclarationGroup} {body : List Statement}
    {target : InitializationTarget} {after : SequentialConfig} :
    PrologStartSimultaneousLocals p state rest current frames activation
      declarations remaining body target after ↔
      startSimultaneousLocals p state rest current frames activation
        declarations remaining body target = after := by
  constructor
  · intro derivation
    cases derivation with
    | empty code =>
        have emptyCode := prologLocalSimCode_iff.mp code
        simp [startSimultaneousLocals, emptyCode]
    | nonempty code =>
        have nonemptyCode := prologLocalSimCode_iff.mp code
        simp [startSimultaneousLocals, nonemptyCode]
  · intro equality
    cases codeEquality : p.localSimCode activation declarations with
    | nil =>
        simp [startSimultaneousLocals, codeEquality] at equality
        subst after
        exact .empty (prologLocalSimCode_iff.mpr codeEquality)
    | cons first later =>
        simp [startSimultaneousLocals, codeEquality] at equality
        subst after
        exact .nonempty (prologLocalSimCode_iff.mpr codeEquality)

inductive PrologReadActivationLocalValue (h : Heap)
    (activation : ActivationId) (slot : LocalSlotId) : ObjRef → Prop where
  | found {definition : ActivationDef} {value : ObjRef} :
      h.activations activation = some definition →
      definition.locals slot = some (.value value) →
      PrologReadActivationLocalValue h activation slot value

theorem prologReadActivationLocalValue_iff {h : Heap}
    {activation : ActivationId} {slot : LocalSlotId} {value : ObjRef} :
    PrologReadActivationLocalValue h activation slot value ↔
      h.readActivationLocal activation slot = some value := by
  constructor
  · intro derivation
    cases derivation with
    | found activationLookup localLookup =>
        simp [Heap.readActivationLocal, activationLookup, localLookup]
  · intro equality
    cases activationLookup : h.activations activation with
    | none => simp [Heap.readActivationLocal, activationLookup] at equality
    | some definition =>
        cases localLookup : definition.locals slot with
        | none =>
            simp [Heap.readActivationLocal, activationLookup, localLookup]
              at equality
        | some cell =>
            cases cell with
            | uninitialized =>
                simp [Heap.readActivationLocal, activationLookup, localLookup]
                  at equality
            | value object =>
                simp [Heap.readActivationLocal, activationLookup, localLookup]
                  at equality
                subst object
                exact .found activationLookup localLookup

inductive PrologActivationWithLocalValue (definition : ActivationDef)
    (slot : LocalSlotId) (value : ObjRef) : ActivationDef → Prop where
  | update {old : LocalCell} :
      definition.locals slot = some old →
      PrologActivationWithLocalValue definition slot value
        { definition with
          locals := definition.locals.install slot (.value value) }

inductive PrologWriteActivationLocalHeap (h : Heap)
    (activation : ActivationId) (slot : LocalSlotId) (value : ObjRef) :
    Heap → Prop where
  | update {definition updated : ActivationDef} :
      h.activations activation = some definition →
      PrologActivationWithLocalValue definition slot value updated →
      PrologWriteActivationLocalHeap h activation slot value
        (h.installActivation activation updated)

theorem prologWriteActivationLocalHeap_iff {h next : Heap}
    {activation : ActivationId} {slot : LocalSlotId} {value : ObjRef} :
    PrologWriteActivationLocalHeap h activation slot value next ↔
      h.writeActivationLocal activation slot value = some next := by
  constructor
  · intro derivation
    cases derivation with
    | update activationLookup updated =>
        cases updated with
        | update localLookup =>
            simp [Heap.writeActivationLocal, activationLookup, localLookup]
  · intro equality
    cases activationLookup : h.activations activation with
    | none =>
        simp [Heap.writeActivationLocal, activationLookup] at equality
    | some definition =>
        cases localLookup : definition.locals slot with
        | none =>
            simp [Heap.writeActivationLocal, activationLookup, localLookup]
              at equality
        | some old =>
            simp [Heap.writeActivationLocal, activationLookup, localLookup]
              at equality
            subst next
            exact .update activationLookup (.update localLookup)

inductive PrologActivationWithoutContinuation (definition : ActivationDef) :
    ActivationDef → Prop where
  | update : PrologActivationWithoutContinuation definition
      { definition with continuation := none }

inductive PrologSeverActivationContinuationHeap (h : Heap)
    (activation : ActivationId) : Heap → Prop where
  | update {definition updated : ActivationDef} :
      h.activations activation = some definition →
      PrologActivationWithoutContinuation definition updated →
      PrologSeverActivationContinuationHeap h activation
        (h.installActivation activation updated)

theorem prologSeverActivationContinuationHeap_iff {h next : Heap}
    {activation : ActivationId} :
    PrologSeverActivationContinuationHeap h activation next ↔
      h.severActivationContinuation activation = some next := by
  constructor
  · intro derivation
    cases derivation with
    | update activationLookup updated =>
        cases updated
        simp [Heap.severActivationContinuation, activationLookup]
  · intro equality
    cases activationLookup : h.activations activation with
    | none =>
        simp [Heap.severActivationContinuation, activationLookup] at equality
    | some definition =>
        simp [Heap.severActivationContinuation, activationLookup] at equality
        subst next
        exact .update activationLookup .update

inductive PrologEagerLocalInitializer :
    LocalDeclaration → Option (LocalSlotId × CoreExpr) → Prop where
  | immutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologEagerLocalInitializer (.immutable slot initializer)
        (some (slot, initializer))
  | mutableInitialized {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologEagerLocalInitializer (.mutableInitialized slot initializer)
        (some (slot, initializer))
  | mutableUninitialized {slot : LocalSlotId} :
      PrologEagerLocalInitializer (.mutableUninitialized slot) none
  | lazyImmutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologEagerLocalInitializer (.lazyImmutable slot initializer) none
  | lazyMutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologEagerLocalInitializer (.lazyMutable slot initializer) none

theorem prologEagerLocalInitializer_iff {declaration : LocalDeclaration}
    {result : Option (LocalSlotId × CoreExpr)} :
    PrologEagerLocalInitializer declaration result ↔
      eagerLocalInitializer declaration = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;> simp [eagerLocalInitializer] at equality <;>
      subst result <;> constructor

inductive PrologNilInitializedLocal :
    LocalDeclaration → Option LocalSlotId → Prop where
  | immutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologNilInitializedLocal (.immutable slot initializer) none
  | mutableInitialized {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologNilInitializedLocal (.mutableInitialized slot initializer) none
  | mutableUninitialized {slot : LocalSlotId} :
      PrologNilInitializedLocal (.mutableUninitialized slot) (some slot)
  | lazyImmutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologNilInitializedLocal (.lazyImmutable slot initializer) (some slot)
  | lazyMutable {slot : LocalSlotId} {initializer : CoreExpr} :
      PrologNilInitializedLocal (.lazyMutable slot initializer) (some slot)

theorem prologNilInitializedLocal_iff {declaration : LocalDeclaration}
    {result : Option LocalSlotId} :
    PrologNilInitializedLocal declaration result ↔
      nilInitializedLocal declaration = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;> simp [nilInitializedLocal] at equality <;>
      subst result <;> constructor

inductive PrologEmptyBodyResult (p : Program) :
    InitializationTarget → ObjRef → Prop where
  | method {receiver : ObjRef} :
      PrologEmptyBodyResult p (.methodBody receiver) receiver
  | closure : PrologEmptyBodyResult p .closureBody p.nilObject

theorem prologEmptyBodyResult_iff {p : Program}
    {target : InitializationTarget} {result : ObjRef} :
    PrologEmptyBodyResult p target result ↔
      emptyBodyResult p target = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases target <;> simp [emptyBodyResult] at equality <;>
      subst result <;> constructor

inductive PrologLastBodyResult : InitializationTarget → ObjRef → ObjRef → Prop where
  | method {receiver value : ObjRef} :
      PrologLastBodyResult (.methodBody receiver) value receiver
  | closure {value : ObjRef} :
      PrologLastBodyResult .closureBody value value

theorem prologLastBodyResult_iff {target : InitializationTarget}
    {value result : ObjRef} :
    PrologLastBodyResult target value result ↔
      lastBodyResult target value = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases target <;> simp [lastBodyResult] at equality <;>
      subst result <;> constructor

inductive PrologStartStatement (frames : EvalStack) :
    Statement → EvalStack → CoreExpr → Prop where
  | expression {value : CoreExpr} :
      PrologStartStatement frames (.expression value) frames value
  | return {value : CoreExpr} :
      PrologStartStatement frames (.return value) (.push frames .returnFrame)
        value

theorem prologStartStatement_iff {frames nextFrames : EvalStack}
    {statement : Statement} {expression : CoreExpr} :
    PrologStartStatement frames statement nextFrames expression ↔
      startStatement frames statement = (nextFrames, expression) := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases statement <;> simp [startStatement] at equality <;>
      rcases equality with ⟨rfl, rfl⟩ <;> constructor

inductive PrologResumeActivation :
    ActivationStack → ActivationId → Option ActivationStack → Prop where
  | empty {target : ActivationId} :
      PrologResumeActivation .empty target none
  | found {rest : ActivationStack} {target : ActivationId}
      {frames : EvalStack} :
      PrologResumeActivation (.push rest ⟨target, frames⟩) target
        (some (.push rest ⟨target, frames⟩))
  | skip {rest : ActivationStack} {other target : ActivationId}
      {frames : EvalStack} {result : Option ActivationStack} :
      other ≠ target →
      PrologResumeActivation rest target result →
      PrologResumeActivation (.push rest ⟨other, frames⟩) target result

theorem prologResumeActivation_iff {stack : ActivationStack}
    {target : ActivationId} {result : Option ActivationStack} :
    PrologResumeActivation stack target result ↔
      resumeActivation stack target = result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | found => simp [resumeActivation]
    | skip different _ ih => simp [resumeActivation, different, ih]
  · intro equality
    induction stack generalizing result with
    | empty =>
        simp [resumeActivation] at equality
        subst result
        exact .empty
    | push rest frame ih =>
        rcases frame with ⟨other, frames⟩
        by_cases same : other = target
        · subst other
          simp [resumeActivation] at equality
          subst result
          exact .found
        · simp [resumeActivation, same] at equality
          exact .skip same (ih equality)

inductive PrologBodyMachineStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | initializeEmpty {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {body : List Statement} {target : InitializationTarget} :
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initialize current [] body target⟩
        ⟨state, .push rest ⟨current, frames⟩, .body target body⟩
  | initializeEager {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {declaration : LocalDeclaration}
      {remaining : List LocalDeclarationGroup} {body : List Statement}
      {target : InitializationTarget} {slot : LocalSlotId}
      {initializer : CoreExpr} :
      PrologEagerLocalInitializer declaration (some (slot, initializer)) →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initialize current (.sequential declaration :: remaining) body target⟩
        ⟨state, .push rest ⟨current,
          .push frames (.initializeLocal slot remaining body target)⟩,
          .evaluate initializer⟩
  | initializeNil {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {declaration : LocalDeclaration}
      {remaining : List LocalDeclarationGroup} {body : List Statement}
      {target : InitializationTarget} {slot : LocalSlotId} {heap : Heap} :
      PrologEagerLocalInitializer declaration none →
      PrologNilInitializedLocal declaration (some slot) →
      PrologWriteActivationLocalHeap state.heap current slot p.nilObject heap →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initialize current (.sequential declaration :: remaining) body target⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .initialize current remaining body target⟩
  | initializeSimultaneous {state : AllocationState}
      {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
      {declarations : List LocalDeclaration}
      {remaining : List LocalDeclarationGroup} {body : List Statement}
      {target : InitializationTarget} {after : SequentialConfig} :
      PrologStartSimultaneousLocals p state rest current frames current
        declarations remaining body target after →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initialize current (.simultaneous declarations :: remaining) body
            target⟩ after
  | readLocal {state : AllocationState} {rest : ActivationStack}
      {current activation : ActivationId} {frames : EvalStack}
      {slot : LocalSlotId} {value : ObjRef} :
      PrologReadActivationLocalValue state.heap activation slot value →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.readLocal activation slot)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object value⟩
  | writeLocal {state : AllocationState} {rest : ActivationStack}
      {current activation : ActivationId} {frames : EvalStack}
      {slot : LocalSlotId} {expression : CoreExpr} :
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.writeLocal activation slot expression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.localWrite activation slot)⟩,
          .evaluate expression⟩
  | initializeCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {slot : LocalSlotId}
      {remaining : List LocalDeclarationGroup} {body : List Statement}
      {target : InitializationTarget} {value : ObjRef} {heap : Heap} :
      PrologWriteActivationLocalHeap state.heap current slot value heap →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current,
          .push frames (.initializeLocal slot remaining body target)⟩,
          .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .initialize current remaining body target⟩
  | localWriteCommit {state : AllocationState} {rest : ActivationStack}
      {current activation : ActivationId} {frames : EvalStack}
      {slot : LocalSlotId} {value : ObjRef} {heap : Heap} :
      PrologWriteActivationLocalHeap state.heap activation slot value heap →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current,
          .push frames (.localWrite activation slot)⟩, .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .object value⟩
  | simultaneousDone {state : AllocationState} {rest : ActivationStack}
      {current activation : ActivationId} {frames : EvalStack}
      {remaining : List LocalDeclarationGroup} {body : List Statement}
      {target : InitializationTarget} {value : ObjRef} :
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current,
          .push frames (.simultaneousLocals [] activation remaining body target)⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .initialize activation remaining body target⟩
  | simultaneousNext {state : AllocationState} {rest : ActivationStack}
      {current activation : ActivationId} {frames : EvalStack}
      {first : CoreExpr} {later : List CoreExpr}
      {remaining : List LocalDeclarationGroup} {body : List Statement}
      {target : InitializationTarget} {value : ObjRef} :
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current,
          .push frames
            (.simultaneousLocals (first :: later) activation remaining body
              target)⟩, .object value⟩
        ⟨state, .push rest ⟨current,
          .push frames
            (.simultaneousLocals later activation remaining body target)⟩,
          .evaluate first⟩
  | sequenceDone {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {target : InitializationTarget} {value result : ObjRef} :
      PrologLastBodyResult target value result →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, .push frames (.sequence target [])⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .finish result⟩
  | sequenceNext {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames nextFrames : EvalStack}
      {target : InitializationTarget} {statement : Statement}
      {later : List Statement} {value : ObjRef} {expression : CoreExpr} :
      PrologStartStatement (.push frames (.sequence target later)) statement
        nextFrames expression →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current,
          .push frames (.sequence target (statement :: later))⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, nextFrames⟩, .evaluate expression⟩
  | bodyEmpty {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {target : InitializationTarget} {result : ObjRef} :
      PrologEmptyBodyResult p target result →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩, .body target []⟩
        ⟨state, .push rest ⟨current, frames⟩, .finish result⟩
  | bodyNext {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames nextFrames : EvalStack}
      {target : InitializationTarget} {statement : Statement}
      {remaining : List Statement} {expression : CoreExpr} :
      PrologStartStatement (.push frames (.sequence target remaining)) statement
        nextFrames expression →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .body target (statement :: remaining)⟩
        ⟨state, .push rest ⟨current, nextFrames⟩, .evaluate expression⟩
  | finishHalt {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {value : ObjRef}
      {activation : ActivationDef} {heap : Heap} :
      state.heap.activations current = some activation →
      activation.continuation = none →
      PrologSeverActivationContinuationHeap state.heap current heap →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩, .finish value⟩
        ⟨{state with heap := heap}, .empty, .halt value⟩
  | finishResume {state : AllocationState} {rest resumed : ActivationStack}
      {current continuation : ActivationId} {frames : EvalStack}
      {value : ObjRef} {activation : ActivationDef} {heap : Heap} :
      state.heap.activations current = some activation →
      activation.continuation = some continuation →
      PrologSeverActivationContinuationHeap state.heap current heap →
      PrologResumeActivation (.push rest ⟨current, frames⟩) continuation
        (some resumed) →
      PrologBodyMachineStep p
        ⟨state, .push rest ⟨current, frames⟩, .finish value⟩
        ⟨{state with heap := heap}, resumed, .object value⟩

theorem prologBodyMachineStep_sound {p : Program}
    {before after : SequentialConfig}
    (derivation : PrologBodyMachineStep p before after) :
    p.bodyMachineNext before = some after := by
  cases derivation with
  | initializeEmpty => simp [Program.bodyMachineNext]
  | initializeEager eager =>
      simp [Program.bodyMachineNext, prologEagerLocalInitializer_iff.mp eager]
  | initializeNil eager nil write =>
      simp [Program.bodyMachineNext, prologEagerLocalInitializer_iff.mp eager,
        prologNilInitializedLocal_iff.mp nil,
        prologWriteActivationLocalHeap_iff.mp write]
  | initializeSimultaneous start =>
      have target := prologStartSimultaneousLocals_iff.mp start
      simp [Program.bodyMachineNext, target]
  | readLocal read =>
      simp [Program.bodyMachineNext, prologReadActivationLocalValue_iff.mp read]
  | writeLocal => simp [Program.bodyMachineNext]
  | initializeCommit write =>
      simp [Program.bodyMachineNext, prologWriteActivationLocalHeap_iff.mp write]
  | localWriteCommit write =>
      simp [Program.bodyMachineNext, prologWriteActivationLocalHeap_iff.mp write]
  | simultaneousDone => simp [Program.bodyMachineNext]
  | simultaneousNext => simp [Program.bodyMachineNext]
  | sequenceDone result =>
      simp [Program.bodyMachineNext, prologLastBodyResult_iff.mp result]
  | sequenceNext start =>
      have target := prologStartStatement_iff.mp start
      simp [Program.bodyMachineNext, target]
  | bodyEmpty result =>
      simp [Program.bodyMachineNext, prologEmptyBodyResult_iff.mp result]
  | bodyNext start =>
      have target := prologStartStatement_iff.mp start
      simp [Program.bodyMachineNext, target]
  | finishHalt live continuation sever =>
      simp [Program.bodyMachineNext, live, continuation,
        prologSeverActivationContinuationHeap_iff.mp sever]
  | finishResume live continuation sever resume =>
      simp [Program.bodyMachineNext, live, continuation,
        prologSeverActivationContinuationHeap_iff.mp sever,
        prologResumeActivation_iff.mp resume]

theorem prologBodyMachineStep_complete {p : Program}
    {before after : SequentialConfig}
    (next : p.bodyMachineNext before = some after) :
    PrologBodyMachineStep p before after := by
  rcases before with ⟨state, stack, control⟩
  cases stack with
  | empty => simp [Program.bodyMachineNext] at next
  | push rest frame =>
      rcases frame with ⟨current, frames⟩
      cases control
      case «initialize» activation groups body target =>
        by_cases same : activation = current
        · subst activation
          cases groups with
          | nil =>
              simp [Program.bodyMachineNext] at next
              subst after
              exact .initializeEmpty
          | cons group remaining =>
              cases group with
              | sequential declaration =>
                  cases eager : eagerLocalInitializer declaration with
                  | none =>
                      cases nilResult : nilInitializedLocal declaration with
                      | none =>
                          simp [Program.bodyMachineNext, eager, nilResult] at next
                      | some slot =>
                          cases write : state.heap.writeActivationLocal current
                              slot p.nilObject with
                          | none =>
                              simp [Program.bodyMachineNext, eager, nilResult,
                                write] at next
                          | some heap =>
                              simp [Program.bodyMachineNext, eager, nilResult,
                                write] at next
                              subst after
                              exact .initializeNil
                                (prologEagerLocalInitializer_iff.mpr eager)
                                (prologNilInitializedLocal_iff.mpr nilResult)
                                (prologWriteActivationLocalHeap_iff.mpr write)
                  | some eagerResult =>
                      rcases eagerResult with ⟨slot, initializer⟩
                      simp [Program.bodyMachineNext, eager] at next
                      subst after
                      exact .initializeEager
                        (prologEagerLocalInitializer_iff.mpr eager)
              | simultaneous declarations =>
                  simp [Program.bodyMachineNext] at next
                  exact .initializeSimultaneous
                    (prologStartSimultaneousLocals_iff.mpr next)
        · simp [Program.bodyMachineNext, same] at next
      case evaluate expression =>
        cases expression
        case readLocal activation slot =>
          cases read : state.heap.readActivationLocal activation slot with
          | none => simp [Program.bodyMachineNext, read] at next
          | some value =>
              simp [Program.bodyMachineNext, read] at next
              subst after
              exact .readLocal (prologReadActivationLocalValue_iff.mpr read)
        case writeLocal activation slot expression =>
          simp [Program.bodyMachineNext] at next
          subst after
          exact .writeLocal
        all_goals simp [Program.bodyMachineNext] at next
      case object value =>
        cases frames with
        | empty => simp [Program.bodyMachineNext] at next
        | push below top =>
            cases top
            case initializeLocal slot remaining body target =>
              cases write : state.heap.writeActivationLocal current slot value with
              | none => simp [Program.bodyMachineNext, write] at next
              | some heap =>
                  simp [Program.bodyMachineNext, write] at next
                  subst after
                  exact .initializeCommit
                    (prologWriteActivationLocalHeap_iff.mpr write)
            case localWrite activation slot =>
              cases write : state.heap.writeActivationLocal activation slot value with
              | none => simp [Program.bodyMachineNext, write] at next
              | some heap =>
                  simp [Program.bodyMachineNext, write] at next
                  subst after
                  exact .localWriteCommit
                    (prologWriteActivationLocalHeap_iff.mpr write)
            case simultaneousLocals code activation remaining body target =>
              cases code with
              | nil =>
                  simp [Program.bodyMachineNext] at next
                  subst after
                  exact .simultaneousDone
              | cons first later =>
                  simp [Program.bodyMachineNext] at next
                  subst after
                  exact .simultaneousNext
            case sequence target remaining =>
              cases remaining with
              | nil =>
                  simp [Program.bodyMachineNext] at next
                  subst after
                  exact .sequenceDone (prologLastBodyResult_iff.mpr rfl)
              | cons statement later =>
                  cases statement with
                  | expression expression =>
                      simp [Program.bodyMachineNext, startStatement] at next
                      subst after
                      exact .sequenceNext (prologStartStatement_iff.mpr rfl)
                  | «return» expression =>
                      simp [Program.bodyMachineNext, startStatement] at next
                      subst after
                      exact .sequenceNext (prologStartStatement_iff.mpr rfl)
            all_goals simp [Program.bodyMachineNext] at next
      case body target statements =>
        cases statements with
        | nil =>
            simp [Program.bodyMachineNext] at next
            subst after
            exact .bodyEmpty (prologEmptyBodyResult_iff.mpr rfl)
        | cons statement remaining =>
            cases statement with
            | expression expression =>
                simp [Program.bodyMachineNext, startStatement] at next
                subst after
                exact .bodyNext (prologStartStatement_iff.mpr rfl)
            | «return» expression =>
                simp [Program.bodyMachineNext, startStatement] at next
                subst after
                exact .bodyNext (prologStartStatement_iff.mpr rfl)
      case finish value =>
        cases live : state.heap.activations current with
        | none => simp [Program.bodyMachineNext, live] at next
        | some activation =>
            cases sever : state.heap.severActivationContinuation current with
            | none => simp [Program.bodyMachineNext, live, sever] at next
            | some heap =>
                cases continuation : activation.continuation with
                | none =>
                    simp [Program.bodyMachineNext, live, sever, continuation]
                      at next
                    subst after
                    exact .finishHalt live continuation
                      (prologSeverActivationContinuationHeap_iff.mpr sever)
                | some continuationId =>
                    cases resume : resumeActivation
                        (.push rest ⟨current, frames⟩) continuationId with
                    | none =>
                        simp [Program.bodyMachineNext, live, sever, continuation,
                          resume] at next
                    | some resumed =>
                        simp [Program.bodyMachineNext, live, sever, continuation,
                          resume] at next
                        subst after
                        exact .finishResume live continuation
                          (prologSeverActivationContinuationHeap_iff.mpr sever)
                          (prologResumeActivation_iff.mpr resume)
      all_goals simp [Program.bodyMachineNext] at next

theorem prologBodyMachineStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologBodyMachineStep p before after ↔ p.BodyMachineStep before after := by
  constructor
  · intro derivation
    exact .graph (prologBodyMachineStep_sound derivation)
  · intro derivation
    cases derivation with
    | graph next => exact prologBodyMachineStep_complete next

inductive PrologProgramAtomObject (p : Program) : AtomPayload → ObjRef → Prop where
  | object {payload : AtomPayload} :
      PrologProgramAtomObject p payload (p.atoms payload)

theorem prologProgramAtomObject_iff {p : Program} {payload : AtomPayload}
    {object : ObjRef} :
    PrologProgramAtomObject p payload object ↔ p.atoms payload = object := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst object
    exact .object

inductive PrologReadObjectSlotValue (h : Heap) (object : ObjectId)
    (slot : PhysicalSlotId) : ObjRef → Prop where
  | found {definition : ObjectDef} {value : ObjRef} :
      h.objects object = some definition →
      definition.slots slot = some value →
      PrologReadObjectSlotValue h object slot value

theorem prologReadObjectSlotValue_iff {h : Heap} {object : ObjectId}
    {slot : PhysicalSlotId} {value : ObjRef} :
    PrologReadObjectSlotValue h object slot value ↔
      h.readObjectSlot object slot = some value := by
  constructor
  · intro derivation
    cases derivation with
    | found objectLookup slotLookup =>
        simp [Heap.readObjectSlot, objectLookup, slotLookup]
  · intro equality
    cases objectLookup : h.objects object with
    | none => simp [Heap.readObjectSlot, objectLookup] at equality
    | some definition =>
        cases slotLookup : definition.slots slot with
        | none =>
            simp [Heap.readObjectSlot, objectLookup, slotLookup] at equality
        | some found =>
            simp [Heap.readObjectSlot, objectLookup, slotLookup] at equality
            subst found
            exact .found objectLookup slotLookup

inductive PrologObjectWithSlotValue (definition : ObjectDef)
    (slot : PhysicalSlotId) (value : ObjRef) : ObjectDef → Prop where
  | update {old : ObjRef} :
      definition.slots slot = some old →
      PrologObjectWithSlotValue definition slot value
        (Heap.objectSlotTransform slot value definition)

inductive PrologWriteObjectSlotHeap (h : Heap) (object : ObjectId)
    (slot : PhysicalSlotId) (value : ObjRef) : Heap → Prop where
  | update {definition updated : ObjectDef} :
      h.objects object = some definition →
      PrologObjectWithSlotValue definition slot value updated →
      PrologWriteObjectSlotHeap h object slot value
        (h.installObject object updated)

theorem prologWriteObjectSlotHeap_iff {h next : Heap} {object : ObjectId}
    {slot : PhysicalSlotId} {value : ObjRef} :
    PrologWriteObjectSlotHeap h object slot value next ↔
      h.writeObjectSlot object slot value = some next := by
  constructor
  · intro derivation
    cases derivation with
    | update objectLookup updated =>
        cases updated with
        | update slotLookup =>
            simp [Heap.writeObjectSlot, objectLookup, slotLookup]
  · intro equality
    cases objectLookup : h.objects object with
    | none => simp [Heap.writeObjectSlot, objectLookup] at equality
    | some definition =>
        cases slotLookup : definition.slots slot with
        | none =>
            simp [Heap.writeObjectSlot, objectLookup, slotLookup] at equality
        | some old =>
            simp [Heap.writeObjectSlot, objectLookup, slotLookup] at equality
            subst next
            exact .update objectLookup (.update slotLookup)

inductive PrologObjectSlotStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | atom {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {payload : AtomPayload}
      {object : ObjRef} :
      PrologProgramAtomObject p payload object →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate (.atom payload)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object object⟩
  | read {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : PhysicalSlotId} {value : ObjRef} :
      PrologReadObjectSlotValue state.heap object slot value →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.readSlot object slot)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object value⟩
  | writeStart {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : PhysicalSlotId} {expression : CoreExpr} :
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.writeSlot object slot expression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.slotWrite object slot)⟩, .evaluate expression⟩
  | writeCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : PhysicalSlotId} {value : ObjRef} {heap : Heap} :
      PrologWriteObjectSlotHeap state.heap object slot value heap →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current,
          .push frames (.slotWrite object slot)⟩, .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .object value⟩
  | currentRead {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {application : ClassId} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .ordinaryObject object →
      activation.currentClass = some application →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.currentRead slot)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.readSlot object ⟨application, slot⟩)⟩
  | currentWrite {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {application : ClassId} {expression : CoreExpr} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .ordinaryObject object →
      activation.currentClass = some application →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.currentWrite slot expression)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.writeSlot object ⟨application, slot⟩ expression)⟩
  | lazyHit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {application : ClassId} {initializer : CoreExpr}
      {value : ObjRef} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .ordinaryObject object →
      activation.currentClass = some application →
      PrologReadObjectSlotValue state.heap object ⟨application, slot⟩ value →
      value ≠ p.nilObject →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.lazyRead slot initializer)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object value⟩
  | lazyMiss {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {application : ClassId} {initializer : CoreExpr} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .ordinaryObject object →
      activation.currentClass = some application →
      PrologReadObjectSlotValue state.heap object ⟨application, slot⟩ p.nilObject →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.lazyRead slot initializer)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.lazySlotStore object ⟨application, slot⟩)⟩, .evaluate initializer⟩
  | lazyCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : PhysicalSlotId} {value : ObjRef} {heap : Heap} :
      PrologWriteObjectSlotHeap state.heap object slot value heap →
      PrologObjectSlotStep p
        ⟨state, .push rest ⟨current,
          .push frames (.lazySlotStore object slot)⟩, .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .object value⟩

theorem prologObjectSlotStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologObjectSlotStep p before after ↔ p.ObjectSlotStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | atom atomObject =>
        have equal := prologProgramAtomObject_iff.mp atomObject
        subst equal
        exact .atom
    | read found => exact .read (prologReadObjectSlotValue_iff.mp found)
    | writeStart => exact .writeStart
    | writeCommit written =>
        exact .writeCommit (prologWriteObjectSlotHeap_iff.mp written)
    | currentRead activation receiver selectedClass => exact .currentRead activation receiver selectedClass
    | currentWrite activation receiver selectedClass =>
        exact .currentWrite activation receiver selectedClass
    | lazyHit activation receiver selectedClass found notNil =>
        exact .lazyHit activation receiver selectedClass
          (prologReadObjectSlotValue_iff.mp found) notNil
    | lazyMiss activation receiver selectedClass found =>
        exact .lazyMiss activation receiver selectedClass
          (prologReadObjectSlotValue_iff.mp found)
    | lazyCommit written =>
        exact .lazyCommit (prologWriteObjectSlotHeap_iff.mp written)
  · intro derivation
    cases derivation with
    | atom => exact .atom .object
    | read found => exact .read (prologReadObjectSlotValue_iff.mpr found)
    | writeStart => exact .writeStart
    | writeCommit written =>
        exact .writeCommit (prologWriteObjectSlotHeap_iff.mpr written)
    | currentRead activation receiver selectedClass => exact .currentRead activation receiver selectedClass
    | currentWrite activation receiver selectedClass =>
        exact .currentWrite activation receiver selectedClass
    | lazyHit activation receiver selectedClass found notNil =>
        exact .lazyHit activation receiver selectedClass
          (prologReadObjectSlotValue_iff.mpr found) notNil
    | lazyMiss activation receiver selectedClass found =>
        exact .lazyMiss activation receiver selectedClass
          (prologReadObjectSlotValue_iff.mpr found)
    | lazyCommit written =>
        exact .lazyCommit (prologWriteObjectSlotHeap_iff.mpr written)

inductive PrologReturnTarget (h : Heap) (current : ActivationId) :
    Option ActivationId → Prop where
  | absent :
      h.activations current = none →
      PrologReturnTarget h current none
  | top {activation : ActivationDef} :
      h.activations current = some activation →
      activation.provenance = .top →
      PrologReturnTarget h current none
  | method {activation : ActivationDef} {method : MethodId} :
      h.activations current = some activation →
      activation.provenance = .method method →
      PrologReturnTarget h current (some current)
  | closure {activation : ActivationDef} {declaration : ActivationDeclId}
      {target : Option ActivationId} :
      h.activations current = some activation →
      activation.provenance = .closure declaration →
      activation.homeMethod = target →
      PrologReturnTarget h current target
  | initializer {activation : ActivationDef}
      {declaration : ActivationDeclId} :
      h.activations current = some activation →
      activation.provenance = .initializer declaration →
      PrologReturnTarget h current (some current)

theorem prologReturnTarget_iff {h : Heap} {current : ActivationId}
    {target : Option ActivationId} :
    PrologReturnTarget h current target ↔ h.returnTarget current = target := by
  constructor
  · intro derivation
    cases derivation with
    | absent missing =>
        simp [Heap.returnTarget, missing]
    | top live provenance =>
        simp [Heap.returnTarget, live, provenance]
    | method live provenance =>
        simp [Heap.returnTarget, live, provenance]
    | closure live provenance home =>
        simp [Heap.returnTarget, live, provenance, home]
    | initializer live provenance =>
        simp [Heap.returnTarget, live, provenance]
  · intro equality
    cases live : h.activations current with
    | none =>
        simp [Heap.returnTarget, live] at equality
        subst target
        exact .absent live
    | some activation =>
        cases provenance : activation.provenance with
        | top =>
            simp [Heap.returnTarget, live, provenance] at equality
            subst target
            exact .top live provenance
        | method method =>
            simp [Heap.returnTarget, live, provenance] at equality
            subst target
            exact .method live provenance
        | closure declaration =>
            simp [Heap.returnTarget, live, provenance] at equality
            subst target
            exact .closure live provenance rfl
        | initializer declaration =>
            simp [Heap.returnTarget, live, provenance] at equality
            subst target
            exact .initializer live provenance

inductive PrologDependentActivation (h : Heap) (target : ActivationId) :
    ActivationId → Prop where
  | target : PrologDependentActivation h target target
  | child {parent child : ActivationId} {activation : ActivationDef} :
      PrologDependentActivation h target parent →
      h.activations child = some activation →
      activation.continuation = some parent →
      PrologDependentActivation h target child

theorem prologDependentActivation_iff {h : Heap}
    {target candidate : ActivationId} :
    PrologDependentActivation h target candidate ↔
      DependentActivation h target candidate := by
  constructor
  · intro derivation
    induction derivation with
    | target => exact .target
    | child parent live continuation ih =>
        exact .child ih live continuation
  · intro derivation
    induction derivation with
    | target => exact .target
    | child parent live continuation ih =>
        exact .child ih live continuation

inductive PrologMarkActivationUncontinuable (activation : ActivationDef) :
    ActivationDef → Prop where
  | update : PrologMarkActivationUncontinuable activation
      (markActivationUncontinuable activation)

theorem prologMarkActivationUncontinuable_iff {activation updated : ActivationDef} :
    PrologMarkActivationUncontinuable activation updated ↔
      updated = markActivationUncontinuable activation := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst updated
    exact .update

inductive PrologMarkUncontinuable (h : Heap) (target : ActivationId) :
    Heap → Prop where
  | update : PrologMarkUncontinuable h target (h.markUncontinuable target)

theorem prologMarkUncontinuable_iff {h marked : Heap}
    {target : ActivationId} :
    PrologMarkUncontinuable h target marked ↔
      marked = h.markUncontinuable target := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst marked
    exact .update

inductive PrologReturnMachineStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | value {state : AllocationState} {rest : ActivationStack}
      {current target : ActivationId} {frames : EvalStack} {value : ObjRef} :
      PrologReturnTarget state.heap current (some target) →
      PrologReturnMachineStep p
        ⟨state, .push rest ⟨current, .push frames .returnFrame⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .transfer target value⟩
  | transfer {state : AllocationState} {rest : ActivationStack}
      {current target continuation : ActivationId} {frames : EvalStack}
      {value : ObjRef} {targetActivation : ActivationDef}
      {marked : Heap} {resumed : ActivationStack} :
      PrologReturnTarget state.heap current (some target) →
      state.heap.activations target = some targetActivation →
      targetActivation.continuable = true →
      targetActivation.continuation = some continuation →
      PrologMarkUncontinuable state.heap target marked →
      PrologResumeActivation (.push rest ⟨current, frames⟩)
        continuation (some resumed) →
      PrologReturnMachineStep p
        ⟨state, .push rest ⟨current, frames⟩, .transfer target value⟩
        ⟨{state with heap := marked}, resumed, .object value⟩
  | cannotNoContinuation {state : AllocationState} {rest : ActivationStack}
      {current target : ActivationId} {frames : EvalStack} {value : ObjRef}
      {targetActivation : ActivationDef} {marked : Heap} :
      PrologReturnTarget state.heap current (some target) →
      state.heap.activations target = some targetActivation →
      targetActivation.continuable = true →
      targetActivation.continuation = none →
      PrologMarkUncontinuable state.heap target marked →
      PrologReturnMachineStep p
        ⟨state, .push rest ⟨current, frames⟩, .transfer target value⟩
        ⟨{state with heap := marked}, .push rest ⟨current, frames⟩,
          .throw .cannotReturn⟩
  | cannotUncontinuable {state : AllocationState} {rest : ActivationStack}
      {current target : ActivationId} {frames : EvalStack} {value : ObjRef}
      {targetActivation : ActivationDef} {marked : Heap} :
      PrologReturnTarget state.heap current (some target) →
      state.heap.activations target = some targetActivation →
      targetActivation.continuable = false →
      PrologMarkUncontinuable state.heap target marked →
      PrologReturnMachineStep p
        ⟨state, .push rest ⟨current, frames⟩, .transfer target value⟩
        ⟨{state with heap := marked}, .push rest ⟨current, frames⟩,
          .throw .cannotReturn⟩

theorem prologReturnMachineStep_sound {p : Program}
    {before after : SequentialConfig}
    (derivation : PrologReturnMachineStep p before after) :
    p.returnMachineNext before = some after := by
  cases derivation with
  | value target =>
      simp [Program.returnMachineNext, prologReturnTarget_iff.mp target]
  | transfer target live continuable continuation marked resumed =>
      simp [Program.returnMachineNext, prologReturnTarget_iff.mp target,
        live, continuable, continuation,
        prologMarkUncontinuable_iff.mp marked,
        prologResumeActivation_iff.mp resumed]
  | cannotNoContinuation target live continuable continuation marked =>
      simp [Program.returnMachineNext, prologReturnTarget_iff.mp target,
        live, continuable, continuation,
        prologMarkUncontinuable_iff.mp marked]
  | cannotUncontinuable target live continuable marked =>
      simp [Program.returnMachineNext, prologReturnTarget_iff.mp target,
        live, continuable, prologMarkUncontinuable_iff.mp marked]

theorem prologReturnMachineStep_complete {p : Program}
    {before after : SequentialConfig}
    (next : p.returnMachineNext before = some after) :
    PrologReturnMachineStep p before after := by
  cases before with
  | mk state stack control =>
    cases stack with
    | empty => simp [Program.returnMachineNext] at next
    | push rest frame =>
      cases frame with
      | mk current frames =>
        have relevant :
            (∃ value, control = .object value) ∨
            (∃ target value, control = .transfer target value) := by
          cases control <;> simp_all [Program.returnMachineNext]
        rcases relevant with ⟨value, rfl⟩ | ⟨target, value, rfl⟩
        · cases frames with
          | empty => simp [Program.returnMachineNext] at next
          | push below top =>
            cases top <;> try { simp [Program.returnMachineNext] at next }
            case returnFrame =>
              cases targetResult : state.heap.returnTarget current with
              | none =>
                  simp [Program.returnMachineNext, targetResult] at next
              | some target =>
                  simp [Program.returnMachineNext, targetResult] at next
                  subst after
                  exact .value (prologReturnTarget_iff.mpr targetResult)
        · cases expectedResult : state.heap.returnTarget current with
          | none =>
              simp [Program.returnMachineNext, expectedResult] at next
          | some expected =>
              by_cases mismatch : target ≠ expected
              · simp [Program.returnMachineNext, expectedResult, mismatch] at next
              · have targetEq : target = expected :=
                  Decidable.not_not.mp mismatch
                subst expected
                cases live : state.heap.activations target with
                | none =>
                    simp [Program.returnMachineNext, expectedResult, live] at next
                | some targetActivation =>
                    cases continuable : targetActivation.continuable with
                    | false =>
                        simp [Program.returnMachineNext, expectedResult, live,
                          continuable] at next
                        subst after
                        exact .cannotUncontinuable
                          (prologReturnTarget_iff.mpr expectedResult) live
                          continuable (.update)
                    | true =>
                        cases continuationResult : targetActivation.continuation with
                        | none =>
                            simp [Program.returnMachineNext, expectedResult, live,
                              continuable, continuationResult] at next
                            subst after
                            exact .cannotNoContinuation
                              (prologReturnTarget_iff.mpr expectedResult) live
                              continuable continuationResult (.update)
                        | some continuation =>
                            cases resumeResult : resumeActivation
                                (.push rest ⟨current, frames⟩) continuation with
                            | none =>
                                simp [Program.returnMachineNext, expectedResult,
                                  live, continuable, continuationResult,
                                  resumeResult] at next
                            | some resumed =>
                                simp [Program.returnMachineNext, expectedResult,
                                  live, continuable, continuationResult,
                                  resumeResult] at next
                                subst after
                                exact .transfer
                                  (prologReturnTarget_iff.mpr expectedResult) live
                                  continuable continuationResult (.update)
                                  (prologResumeActivation_iff.mpr resumeResult)

theorem prologReturnMachineStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologReturnMachineStep p before after ↔ p.ReturnMachineStep before after := by
  constructor
  · intro derivation
    exact .graph (prologReturnMachineStep_sound derivation)
  · intro derivation
    cases derivation with
    | graph next => exact prologReturnMachineStep_complete next

inductive PrologEagerSlotInitializer :
    SlotDeclaration → Option (SlotId × CoreExpr × ActivationDeclId) → Prop where
  | immutable {slot : SlotId} {initializer : CoreExpr}
      {thunk : ActivationDeclId} :
      PrologEagerSlotInitializer (.immutable slot initializer thunk)
        (some (slot, initializer, thunk))
  | mutableInitialized {slot : SlotId} {initializer : CoreExpr}
      {thunk : ActivationDeclId} :
      PrologEagerSlotInitializer (.mutableInitialized slot initializer thunk)
        (some (slot, initializer, thunk))
  | mutableUninitialized {slot : SlotId} :
      PrologEagerSlotInitializer (.mutableUninitialized slot) none

theorem prologEagerSlotInitializer_iff {declaration : SlotDeclaration}
    {result : Option (SlotId × CoreExpr × ActivationDeclId)} :
    PrologEagerSlotInitializer declaration result ↔
      eagerSlotInitializer declaration = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;> simp [eagerSlotInitializer] at equality <;>
      subst result <;> constructor

inductive PrologSlotFutureInstallExpression (p : Program)
    (activation : ActivationId) (object : ObjectId) (application : ClassId) :
    SlotDeclaration → Option CoreExpr → Prop where
  | immutable {slot : SlotId} {initializer : CoreExpr}
      {thunk : ActivationDeclId} :
      PrologSlotFutureInstallExpression p activation object application
        (.immutable slot initializer thunk)
        (some (.writeSlot object ⟨application, slot⟩
          (.ordinarySend (p.pastFutureExpression activation) computingSelector
            [.closureLiteral thunk])))
  | mutableInitialized {slot : SlotId} {initializer : CoreExpr}
      {thunk : ActivationDeclId} :
      PrologSlotFutureInstallExpression p activation object application
        (.mutableInitialized slot initializer thunk)
        (some (.writeSlot object ⟨application, slot⟩
          (.ordinarySend (p.pastFutureExpression activation) computingSelector
            [.closureLiteral thunk])))
  | mutableUninitialized {slot : SlotId} :
      PrologSlotFutureInstallExpression p activation object application
        (.mutableUninitialized slot) none

theorem prologSlotFutureInstallExpression_iff {p : Program}
    {activation : ActivationId} {object : ObjectId} {application : ClassId}
    {declaration : SlotDeclaration} {result : Option CoreExpr} :
    PrologSlotFutureInstallExpression p activation object application declaration result ↔
      p.slotFutureInstallExpression activation object application declaration = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;>
      simp [Program.slotFutureInstallExpression] at equality <;>
      subst result <;> constructor

inductive PrologSlotFutureResolveExpression (object : ObjectId) (application : ClassId) :
    SlotDeclaration → Option CoreExpr → Prop where
  | immutable {slot : SlotId} {initializer : CoreExpr}
      {thunk : ActivationDeclId} :
      PrologSlotFutureResolveExpression object application
        (.immutable slot initializer thunk)
        (some (.ordinarySend (.readSlot object ⟨application, slot⟩) resolveSelector []))
  | mutableInitialized {slot : SlotId} {initializer : CoreExpr}
      {thunk : ActivationDeclId} :
      PrologSlotFutureResolveExpression object application
        (.mutableInitialized slot initializer thunk)
        (some (.ordinarySend (.readSlot object ⟨application, slot⟩) resolveSelector []))
  | mutableUninitialized {slot : SlotId} :
      PrologSlotFutureResolveExpression object application (.mutableUninitialized slot) none

theorem prologSlotFutureResolveExpression_iff {object : ObjectId} {application : ClassId}
    {declaration : SlotDeclaration} {result : Option CoreExpr} :
    PrologSlotFutureResolveExpression object application declaration result ↔
      slotFutureResolveExpression object application declaration = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases declaration <;>
      simp [slotFutureResolveExpression] at equality <;>
      subst result <;> constructor

inductive PrologSlotFutureInstallExpressions (p : Program)
    (activation : ActivationId) (object : ObjectId) (application : ClassId) :
    List SlotDeclaration → List CoreExpr → Prop where
  | nil : PrologSlotFutureInstallExpressions p activation object application [] []
  | keep {declaration : SlotDeclaration}
      {declarations : List SlotDeclaration} {expression : CoreExpr}
      {expressions : List CoreExpr} :
      PrologSlotFutureInstallExpression p activation object application declaration
        (some expression) →
      PrologSlotFutureInstallExpressions p activation object application declarations
        expressions →
      PrologSlotFutureInstallExpressions p activation object application
        (declaration :: declarations) (expression :: expressions)
  | skip {declaration : SlotDeclaration}
      {declarations : List SlotDeclaration} {expressions : List CoreExpr} :
      PrologSlotFutureInstallExpression p activation object application declaration none →
      PrologSlotFutureInstallExpressions p activation object application declarations
        expressions →
      PrologSlotFutureInstallExpressions p activation object application
        (declaration :: declarations) expressions

theorem prologSlotFutureInstallExpressions_iff {p : Program}
    {activation : ActivationId} {object : ObjectId} {application : ClassId}
    {declarations : List SlotDeclaration} {expressions : List CoreExpr} :
    PrologSlotFutureInstallExpressions p activation object application declarations
      expressions ↔
      declarations.filterMap
        (p.slotFutureInstallExpression activation object application) = expressions := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | keep head tail ih =>
        simp [prologSlotFutureInstallExpression_iff.mp head, ih]
    | skip head tail ih =>
        simp [prologSlotFutureInstallExpression_iff.mp head, ih]
  · intro equality
    induction declarations generalizing expressions with
    | nil =>
        simp at equality
        subst expressions
        exact .nil
    | cons declaration declarations ih =>
        cases result : p.slotFutureInstallExpression activation object application
            declaration with
        | none =>
            simp [result] at equality
            exact .skip (prologSlotFutureInstallExpression_iff.mpr result)
              (ih equality)
        | some expression =>
            simp [result] at equality
            subst expressions
            exact .keep (prologSlotFutureInstallExpression_iff.mpr result)
              (ih rfl)

inductive PrologSlotFutureResolveExpressions (object : ObjectId) (application : ClassId) :
    List SlotDeclaration → List CoreExpr → Prop where
  | nil : PrologSlotFutureResolveExpressions object application [] []
  | keep {declaration : SlotDeclaration}
      {declarations : List SlotDeclaration} {expression : CoreExpr}
      {expressions : List CoreExpr} :
      PrologSlotFutureResolveExpression object application declaration (some expression) →
      PrologSlotFutureResolveExpressions object application declarations expressions →
      PrologSlotFutureResolveExpressions object application (declaration :: declarations)
        (expression :: expressions)
  | skip {declaration : SlotDeclaration}
      {declarations : List SlotDeclaration} {expressions : List CoreExpr} :
      PrologSlotFutureResolveExpression object application declaration none →
      PrologSlotFutureResolveExpressions object application declarations expressions →
      PrologSlotFutureResolveExpressions object application (declaration :: declarations)
        expressions

theorem prologSlotFutureResolveExpressions_iff {object : ObjectId} {application : ClassId}
    {declarations : List SlotDeclaration} {expressions : List CoreExpr} :
    PrologSlotFutureResolveExpressions object application declarations expressions ↔
      declarations.filterMap (slotFutureResolveExpression object application) =
        expressions := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | keep head tail ih =>
        simp [prologSlotFutureResolveExpression_iff.mp head, ih]
    | skip head tail ih =>
        simp [prologSlotFutureResolveExpression_iff.mp head, ih]
  · intro equality
    induction declarations generalizing expressions with
    | nil =>
        simp at equality
        subst expressions
        exact .nil
    | cons declaration declarations ih =>
        cases result : slotFutureResolveExpression object application declaration with
        | none =>
            simp [result] at equality
            exact .skip (prologSlotFutureResolveExpression_iff.mpr result)
              (ih equality)
        | some expression =>
            simp [result] at equality
            subst expressions
            exact .keep (prologSlotFutureResolveExpression_iff.mpr result)
              (ih rfl)

inductive PrologSlotSimCode (p : Program) (activation : ActivationId)
    (object : ObjectId) (application : ClassId) : List SlotDeclaration → List CoreExpr → Prop where
  | build {declarations : List SlotDeclaration}
      {installations resolutions code : List CoreExpr} :
      PrologSlotFutureInstallExpressions p activation object application declarations
        installations →
      PrologSlotFutureResolveExpressions object application declarations resolutions →
      PrologListAppend installations resolutions code →
      PrologSlotSimCode p activation object application declarations code

theorem prologSlotSimCode_iff {p : Program} {activation : ActivationId}
    {object : ObjectId} {application : ClassId} {declarations : List SlotDeclaration}
    {code : List CoreExpr} :
    PrologSlotSimCode p activation object application declarations code ↔
      p.slotSimCode activation object application declarations = code := by
  constructor
  · intro derivation
    cases derivation with
    | build installations resolutions append =>
        rw [Program.slotSimCode]
        rw [prologSlotFutureInstallExpressions_iff.mp installations]
        rw [prologSlotFutureResolveExpressions_iff.mp resolutions]
        exact prologListAppend_iff.mp append
  · intro equality
    exact .build (prologSlotFutureInstallExpressions_iff.mpr rfl)
      (prologSlotFutureResolveExpressions_iff.mpr rfl)
      (prologListAppend_iff.mpr equality)

inductive PrologStartSimultaneousSlots (p : Program)
    (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (object : ObjectId) (application : ClassId)
    (declarations : List SlotDeclaration)
    (remaining : List SlotDeclarationGroup) (body : List Statement) :
    SequentialConfig → Prop where
  | empty :
      PrologSlotSimCode p current object application declarations [] →
      PrologStartSimultaneousSlots p state rest current frames object application
        declarations remaining body
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object remaining body⟩
  | nonempty {first : CoreExpr} {later : List CoreExpr} :
      PrologSlotSimCode p current object application declarations (first :: later) →
      PrologStartSimultaneousSlots p state rest current frames object application
        declarations remaining body
        ⟨state, .push rest ⟨current,
          .push frames (.simultaneousSlots later object remaining body)⟩,
          .evaluate first⟩

theorem prologStartSimultaneousSlots_iff {p : Program}
    {state : AllocationState} {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack} {object : ObjectId} {application : ClassId}
    {declarations : List SlotDeclaration}
    {remaining : List SlotDeclarationGroup} {body : List Statement}
    {after : SequentialConfig} :
    PrologStartSimultaneousSlots p state rest current frames object application declarations
      remaining body after ↔
      p.startSimultaneousSlots state rest current frames object application declarations
        remaining body = after := by
  constructor
  · intro derivation
    cases derivation with
    | empty code =>
        simp [Program.startSimultaneousSlots,
          prologSlotSimCode_iff.mp code]
    | nonempty code =>
        simp [Program.startSimultaneousSlots,
          prologSlotSimCode_iff.mp code]
  · intro equality
    cases codeResult : p.slotSimCode current object application declarations with
    | nil =>
        simp [Program.startSimultaneousSlots, codeResult] at equality
        subst after
        exact .empty (prologSlotSimCode_iff.mpr codeResult)
    | cons first later =>
        simp [Program.startSimultaneousSlots, codeResult] at equality
        subst after
        exact .nonempty (prologSlotSimCode_iff.mpr codeResult)

inductive PrologSlotInitializationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | groupsEmpty {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {body : List Statement} :
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object [] body⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .body (.methodBody (.ordinaryObject object)) body⟩
  | groupsSequential {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {declarations : List SlotDeclaration}
      {remaining : List SlotDeclarationGroup} {body : List Statement} :
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object
            (.sequential declarations :: remaining) body⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSequentialSlots object declarations remaining body⟩
  | groupsSimultaneous {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {declarations : List SlotDeclaration}
      {remaining : List SlotDeclarationGroup} {body : List Statement}
      {after : SequentialConfig} :
      ∀ {activation : ActivationDef} {application : ClassId},
      state.heap.activations current = some activation →
      activation.currentClass = some application →
      PrologStartSimultaneousSlots p state rest current frames object application
        declarations remaining body after →
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object
            (.simultaneous declarations :: remaining) body⟩ after
  | sequentialEmpty {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {remaining : List SlotDeclarationGroup} {body : List Statement} :
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSequentialSlots object [] remaining body⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object remaining body⟩
  | sequentialUninitialized {state : AllocationState}
      {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
      {object : ObjectId} {slot : SlotId}
      {later : List SlotDeclaration} {remaining : List SlotDeclarationGroup}
      {body : List Statement} :
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSequentialSlots object
            (.mutableUninitialized slot :: later) remaining body⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSequentialSlots object later remaining body⟩
  | sequentialEager {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {declaration : SlotDeclaration} {slot : SlotId}
      {initializer : CoreExpr} {thunk : ActivationDeclId}
      {later : List SlotDeclaration} {remaining : List SlotDeclarationGroup}
      {body : List Statement} :
      ∀ {activation : ActivationDef} {application : ClassId},
      state.heap.activations current = some activation →
      activation.currentClass = some application →
      PrologEagerSlotInitializer declaration (some (slot, initializer, thunk)) →
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSequentialSlots object (declaration :: later) remaining
            body⟩
        ⟨state, .push rest ⟨current,
          .push frames (.storeInitializedSlot object ⟨application, slot⟩ later remaining body)⟩,
          .evaluate initializer⟩
  | store {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : PhysicalSlotId} {later : List SlotDeclaration}
      {remaining : List SlotDeclarationGroup} {body : List Statement}
      {value : ObjRef} {heap : Heap} :
      PrologWriteObjectSlotHeap state.heap object slot value heap →
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current,
          .push frames (.storeInitializedSlot object slot later remaining body)⟩,
          .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .initializeSequentialSlots object later remaining body⟩
  | simultaneousDone {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {remaining : List SlotDeclarationGroup} {body : List Statement}
      {value : ObjRef} :
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current,
          .push frames (.simultaneousSlots [] object remaining body)⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object remaining body⟩
  | simultaneousNext {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {first : CoreExpr} {later : List CoreExpr}
      {remaining : List SlotDeclarationGroup} {body : List Statement}
      {value : ObjRef} :
      PrologSlotInitializationStep p
        ⟨state, .push rest ⟨current,
          .push frames
            (.simultaneousSlots (first :: later) object remaining body)⟩,
          .object value⟩
        ⟨state, .push rest ⟨current,
          .push frames (.simultaneousSlots later object remaining body)⟩,
          .evaluate first⟩

theorem prologSlotInitializationStep_sound {p : Program}
    {before after : SequentialConfig}
    (derivation : PrologSlotInitializationStep p before after) :
    p.slotInitializationNext before = some after := by
  cases derivation with
  | groupsEmpty => simp [Program.slotInitializationNext]
  | groupsSequential => simp [Program.slotInitializationNext]
  | groupsSimultaneous activation selectedClass start =>
      simp [Program.slotInitializationNext, activation, selectedClass,
        prologStartSimultaneousSlots_iff.mp start]
  | sequentialEmpty => simp [Program.slotInitializationNext]
  | sequentialUninitialized => simp [Program.slotInitializationNext]
  | sequentialEager activation selectedClass eager =>
      cases eager <;> simp [Program.slotInitializationNext, activation, selectedClass]
  | store write =>
      simp [Program.slotInitializationNext,
        prologWriteObjectSlotHeap_iff.mp write]
  | simultaneousDone => simp [Program.slotInitializationNext]
  | simultaneousNext => simp [Program.slotInitializationNext]

theorem prologSlotInitializationStep_complete {p : Program}
    {before after : SequentialConfig}
    (next : p.slotInitializationNext before = some after) :
    PrologSlotInitializationStep p before after := by
  rcases before with ⟨state, stack, control⟩
  cases stack with
  | empty => simp [Program.slotInitializationNext] at next
  | push rest frame =>
      rcases frame with ⟨current, frames⟩
      cases control
      case initializeSlotGroups object groups body =>
        cases groups with
        | nil =>
            simp [Program.slotInitializationNext] at next
            subst after
            exact .groupsEmpty
        | cons group remaining =>
            cases group with
            | sequential declarations =>
                simp [Program.slotInitializationNext] at next
                subst after
                exact .groupsSequential
            | simultaneous declarations =>
                simp [Program.slotInitializationNext, Option.bind_eq_some_iff] at next
                rcases next with ⟨activation, lookup, application, selectedClass, next⟩
                exact .groupsSimultaneous lookup selectedClass
                  (prologStartSimultaneousSlots_iff.mpr next)
      case initializeSequentialSlots object declarations remaining body =>
        cases declarations with
        | nil =>
            simp [Program.slotInitializationNext] at next
            subst after
            exact .sequentialEmpty
        | cons declaration later =>
            cases declaration with
            | mutableUninitialized slot =>
                simp [Program.slotInitializationNext] at next
                subst after
                exact .sequentialUninitialized
            | immutable slot initializer thunk =>
                simp [Program.slotInitializationNext, Option.bind_eq_some_iff] at next
                rcases next with ⟨activation, lookup, application, selectedClass, next⟩
                subst after
                exact .sequentialEager lookup selectedClass (.immutable)
            | mutableInitialized slot initializer thunk =>
                simp [Program.slotInitializationNext, Option.bind_eq_some_iff] at next
                rcases next with ⟨activation, lookup, application, selectedClass, next⟩
                subst after
                exact .sequentialEager lookup selectedClass (.mutableInitialized)
      case object value =>
        cases frames with
        | empty => simp [Program.slotInitializationNext] at next
        | push below top =>
            cases top
            case storeInitializedSlot object slot later remaining body =>
              cases write : state.heap.writeObjectSlot object slot value with
              | none =>
                  simp [Program.slotInitializationNext, write] at next
              | some heap =>
                  simp [Program.slotInitializationNext, write] at next
                  subst after
                  exact .store (prologWriteObjectSlotHeap_iff.mpr write)
            case simultaneousSlots code object remaining body =>
              cases code with
              | nil =>
                  simp [Program.slotInitializationNext] at next
                  subst after
                  exact .simultaneousDone
              | cons first later =>
                  simp [Program.slotInitializationNext] at next
                  subst after
                  exact .simultaneousNext
            all_goals simp [Program.slotInitializationNext] at next
      all_goals simp [Program.slotInitializationNext] at next

theorem prologSlotInitializationStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologSlotInitializationStep p before after ↔
      p.SlotInitializationStep before after := by
  constructor
  · intro derivation
    exact .graph (prologSlotInitializationStep_sound derivation)
  · intro derivation
    cases derivation with
    | graph next => exact prologSlotInitializationStep_complete next

inductive PrologActivationParameterValues (activation : ActivationDef) :
    List ParameterId → List ObjRef → Prop where
  | nil : PrologActivationParameterValues activation [] []
  | cons {parameter : ParameterId} {parameters : List ParameterId}
      {value : ObjRef} {values : List ObjRef} :
      activation.parameters parameter = some value →
      PrologActivationParameterValues activation parameters values →
      PrologActivationParameterValues activation (parameter :: parameters)
        (value :: values)

theorem prologActivationParameterValues_iff {activation : ActivationDef}
    {parameters : List ParameterId} {values : List ObjRef} :
    PrologActivationParameterValues activation parameters values ↔
      Program.activationParameterValues activation parameters = some values := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons found _ ih =>
        simp [Program.activationParameterValues, found, ih]
  · intro equality
    induction parameters generalizing values with
    | nil =>
        simp [Program.activationParameterValues] at equality
        subst values
        exact .nil
    | cons parameter parameters ih =>
        cases found : activation.parameters parameter with
        | none =>
            simp [Program.activationParameterValues, found] at equality
        | some value =>
            cases tail : Program.activationParameterValues activation parameters with
            | none =>
                simp [Program.activationParameterValues, found, tail] at equality
            | some valuesTail =>
                simp [Program.activationParameterValues, found, tail] at equality
                subst values
                exact .cons found (ih tail)

inductive PrologApplicationSlots (classId : ClassId) :
    List SlotId → List PhysicalSlotId → Prop where
  | nil : PrologApplicationSlots classId [] []
  | cons {slot : SlotId} {declarations : List SlotId} {slots : List PhysicalSlotId} :
      PrologApplicationSlots classId declarations slots →
      PrologApplicationSlots classId (slot :: declarations) (⟨classId, slot⟩ :: slots)

theorem prologApplicationSlots_iff {classId : ClassId}
    {declarations : List SlotId} {slots : List PhysicalSlotId} :
    PrologApplicationSlots classId declarations slots ↔
      Program.applicationSlots classId declarations = slots := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons tail ih => simp [Program.applicationSlots] at ih ⊢; exact ih
  · intro equal
    subst slots
    induction declarations with
    | nil => exact .nil
    | cons slot declarations ih => exact .cons ih

inductive PrologOwnSlots (p : Program) (h : Heap) (classId : ClassId) :
    List PhysicalSlotId → Prop where
  | missingClass :
      h.classes classId = none →
      PrologOwnSlots p h classId []
  | missingMixin {classDef : ClassDef} :
      h.classes classId = some classDef →
      p.mixins classDef.mixin = none →
      PrologOwnSlots p h classId []
  | found {classDef : ClassDef} {mixin : MixinDef} {slots : List PhysicalSlotId} :
      h.classes classId = some classDef →
      p.mixins classDef.mixin = some mixin →
      PrologApplicationSlots classId mixin.ownSlots slots →
      PrologOwnSlots p h classId slots

theorem prologOwnSlots_iff {p : Program} {h : Heap} {classId : ClassId}
    {slots : List PhysicalSlotId} :
    PrologOwnSlots p h classId slots ↔ p.ownSlots h classId = slots := by
  constructor
  · intro derivation
    cases derivation with
    | missingClass missing => simp [Program.ownSlots, missing]
    | missingMixin live missing => simp [Program.ownSlots, live, missing]
    | found live found qualified =>
        simp [Program.ownSlots, live, found, prologApplicationSlots_iff.mp qualified]
  · intro equality
    cases live : h.classes classId with
    | none =>
        simp [Program.ownSlots, live] at equality
        subst slots
        exact .missingClass live
    | some classDef =>
        cases found : p.mixins classDef.mixin with
        | none =>
            simp [Program.ownSlots, live, found] at equality
            subst slots
            exact .missingMixin live found
        | some mixin =>
            simp [Program.ownSlots, live, found] at equality
            subst slots
            exact .found live found (prologApplicationSlots_iff.mpr rfl)

inductive PrologLayoutForChain (p : Program) (h : Heap) :
    List ClassId → List PhysicalSlotId → Prop where
  | nil : PrologLayoutForChain p h [] []
  | cons {classId : ClassId} {ancestors : List ClassId}
      {ancestorLayout ownSlots layout : List PhysicalSlotId} :
      PrologLayoutForChain p h ancestors ancestorLayout →
      PrologOwnSlots p h classId ownSlots →
      PrologListAppend ancestorLayout ownSlots layout →
      PrologLayoutForChain p h (classId :: ancestors) layout

theorem prologLayoutForChain_iff {p : Program} {h : Heap}
    {chain : List ClassId} {layout : List PhysicalSlotId} :
    PrologLayoutForChain p h chain layout ↔
      p.layoutForChain h chain = layout := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons ancestors own append ih =>
        simp [Program.layoutForChain, ih, prologOwnSlots_iff.mp own,
          prologListAppend_iff.mp append]
  · intro equality
    induction chain generalizing layout with
    | nil =>
        simp [Program.layoutForChain] at equality
        subst layout
        exact .nil
    | cons classId ancestors ih =>
        exact .cons (ih rfl) (prologOwnSlots_iff.mpr rfl)
          (prologListAppend_iff.mpr equality)

inductive PrologListNotMember {α : Type} (value : α) : List α → Prop where
  | nil : PrologListNotMember value []
  | cons {head : α} {tail : List α} :
      value ≠ head →
      PrologListNotMember value tail →
      PrologListNotMember value (head :: tail)

theorem prologListNotMember_iff {α : Type} {value : α}
    {values : List α} :
    PrologListNotMember value values ↔ value ∉ values := by
  constructor
  · intro derivation
    induction derivation with
    | nil => simp
    | cons different _ ih => simp [different, ih]
  · intro notMember
    induction values with
    | nil => exact .nil
    | cons head tail ih =>
        simp only [List.mem_cons, not_or] at notMember
        exact .cons notMember.1 (ih notMember.2)

inductive PrologListNodup {α : Type} : List α → Prop where
  | nil : PrologListNodup []
  | cons {head : α} {tail : List α} :
      PrologListNotMember head tail →
      PrologListNodup tail →
      PrologListNodup (head :: tail)

theorem prologListNodup_iff {α : Type} {values : List α} :
    PrologListNodup values ↔ values.Nodup := by
  constructor
  · intro derivation
    induction derivation with
    | nil => exact .nil
    | cons fresh _ ih =>
        exact List.pairwise_cons.mpr ⟨fun candidate member equal =>
          prologListNotMember_iff.mp fresh (equal ▸ member), ih⟩
  · intro nodup
    induction nodup with
    | nil => exact .nil
    | cons fresh _ ih =>
        have notMember : _ := fun member => fresh _ member rfl
        exact .cons (prologListNotMember_iff.mpr notMember) ih

inductive PrologInstanceLayout (p : Program) (h : Heap)
    (classId : ClassId) : List PhysicalSlotId → Prop where
  | witness {chain : List ClassId} {layout : List PhysicalSlotId} :
      PrologClassChain p h classId chain →
      PrologLayoutForChain p h chain layout →
      PrologListNodup layout →
      PrologInstanceLayout p h classId layout

theorem prologInstanceLayout_iff {p : Program} {h : Heap}
    {classId : ClassId} {layout : List PhysicalSlotId} :
    PrologInstanceLayout p h classId layout ↔
      p.InstanceLayout h classId layout := by
  constructor
  · intro derivation
    cases derivation with
    | witness chain layout nodup =>
        exact ⟨_, prologClassChain_iff.mp chain,
          prologLayoutForChain_iff.mp layout,
          prologListNodup_iff.mp nodup⟩
  · rintro ⟨chain, chainWitness, layoutResult, nodup⟩
    exact .witness (prologClassChain_iff.mpr chainWitness)
      (prologLayoutForChain_iff.mpr layoutResult)
      (prologListNodup_iff.mpr nodup)

inductive PrologSlotsInitializedTo (layout : List PhysicalSlotId) (value : ObjRef) :
    FiniteStore PhysicalSlotId ObjRef → Prop where
  | build : PrologSlotsInitializedTo layout value
      (Program.slotsInitializedTo layout value)

theorem prologSlotsInitializedTo_iff {layout : List PhysicalSlotId} {value : ObjRef}
    {slots : FiniteStore PhysicalSlotId ObjRef} :
    PrologSlotsInitializedTo layout value slots ↔
      slots = Program.slotsInitializedTo layout value := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst slots
    exact .build

inductive PrologAllocateInstance (p : Program) (state : AllocationState)
    (classId : ClassId) (layout : List PhysicalSlotId) (nilObject : ObjRef) :
    AllocationState → ObjectId → Prop where
  | allocate :
      PrologAllocateInstance p state classId layout nilObject
        (p.allocateInstance state classId layout nilObject).1
        (p.allocateInstance state classId layout nilObject).2

theorem prologAllocateInstance_iff {p : Program} {state next : AllocationState}
    {classId : ClassId} {layout : List PhysicalSlotId} {nilObject : ObjRef}
    {object : ObjectId} :
    PrologAllocateInstance p state classId layout nilObject next object ↔
      p.allocateInstance state classId layout nilObject = (next, object) := by
  constructor
  · intro derivation
    cases derivation
    exact Prod.ext rfl rfl
  · intro equality
    rcases equality with ⟨rfl, rfl⟩
    exact .allocate

inductive PrologInitializerActivationDefinition (p : Program)
    (id : ActivationId) (factory : FactoryDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) : ActivationDef → Prop where
  | build :
      PrologInitializerActivationDefinition p id factory classId object message
        continuation
        (p.initializerActivationDefinition id factory classId object message
          continuation)

theorem prologInitializerActivationDefinition_iff {p : Program}
    {id : ActivationId} {factory : FactoryDef} {classId : ClassId}
    {object : ObjectId} {message : Message}
    {continuation : Option ActivationId} {activation : ActivationDef} :
    PrologInitializerActivationDefinition p id factory classId object message
      continuation activation ↔
      activation = p.initializerActivationDefinition id factory classId object
        message continuation := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst activation
    exact .build

inductive PrologAllocateInitializerActivation (p : Program)
    (state : AllocationState) (factory : FactoryDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    AllocationState → ActivationId → Prop where
  | allocate :
      PrologAllocateInitializerActivation p state factory classId object
        message continuation
        (p.allocateInitializerActivation state factory classId object message
          continuation).1
        (p.allocateInitializerActivation state factory classId object message
          continuation).2

theorem prologAllocateInitializerActivation_iff {p : Program}
    {state next : AllocationState} {factory : FactoryDef} {classId : ClassId}
    {object : ObjectId} {message : Message}
    {continuation : Option ActivationId} {activation : ActivationId} :
    PrologAllocateInitializerActivation p state factory classId object message
      continuation next activation ↔
      p.allocateInitializerActivation state factory classId object message
        continuation = (next, activation) := by
  constructor
  · intro derivation
    cases derivation
    exact Prod.ext rfl rfl
  · intro equality
    rcases equality with ⟨rfl, rfl⟩
    exact .allocate

inductive PrologAllocateInitialInstance (p : Program)
    (state : AllocationState) (classId : ClassId) (layout : List PhysicalSlotId)
    (factory : FactoryDef) (message : Message)
    (continuation : Option ActivationId) :
    AllocationState → ObjectId → ActivationId → Prop where
  | allocate :
      PrologAllocateInitialInstance p state classId layout factory message
        continuation
        (p.allocateInitialInstance state classId layout factory message
          continuation).state
        (p.allocateInitialInstance state classId layout factory message
          continuation).object
        (p.allocateInitialInstance state classId layout factory message
          continuation).initializer

theorem prologAllocateInitialInstance_iff {p : Program}
    {state next : AllocationState} {classId : ClassId} {layout : List PhysicalSlotId}
    {factory : FactoryDef} {message : Message}
    {continuation : Option ActivationId} {object : ObjectId}
    {initializer : ActivationId} :
    PrologAllocateInitialInstance p state classId layout factory message
      continuation next object initializer ↔
      let allocation := p.allocateInitialInstance state classId layout factory
        message continuation
      allocation.state = next ∧ allocation.object = object ∧
        allocation.initializer = initializer := by
  constructor
  · intro derivation
    cases derivation
    exact ⟨rfl, rfl, rfl⟩
  · intro equality
    dsimp only at equality
    rcases equality with ⟨stateEq, objectEq, initializerEq⟩
    subst next
    subst object
    subst initializer
    exact .allocate

inductive PrologFactoryNewResult (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (classId : ClassId) (layout : List PhysicalSlotId) (factory : FactoryDef)
    (message : Message) : SequentialConfig → Prop where
  | build :
      PrologFactoryNewResult p state rest current frames classId layout factory
        message
        (p.factoryNewResult state rest current frames classId layout factory
          message)

theorem prologFactoryNewResult_iff {p : Program} {state : AllocationState}
    {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
    {classId : ClassId} {layout : List PhysicalSlotId} {factory : FactoryDef}
    {message : Message} {after : SequentialConfig} :
    PrologFactoryNewResult p state rest current frames classId layout factory
      message after ↔
      p.factoryNewResult state rest current frames classId layout factory
        message = after := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst after
    exact .build

inductive PrologFactoryNewStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | allocate {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {activation : ActivationDef} {classId : ClassId} {classDef : ClassDef}
      {factory : FactoryDef} {selector : Selector}
      {parameters : List ParameterId} {arguments : List ObjRef}
      {layout : List PhysicalSlotId} {after : SequentialConfig} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .classObject classId →
      state.heap.classes classId = some classDef →
      classDef.primaryFactory = some factory →
      selector = factory.selector →
      parameters = factory.parameters →
      PrologActivationParameterValues activation parameters arguments →
      PrologInstanceLayout p state.heap classId layout →
      PrologFactoryNewResult p state rest current frames classId layout factory
        ⟨selector, arguments⟩ after →
      PrologFactoryNewStep p
        ⟨state, .push rest ⟨current, .push frames .returnFrame⟩,
          .evaluate (.newInstanceCurrent selector parameters)⟩ after

theorem prologFactoryNewStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologFactoryNewStep p before after ↔ p.FactoryNewStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | allocate activationLive receiver classLive factoryLive selectorMatches
        parametersMatch argumentsRead layoutWitness result =>
        have resultEq := prologFactoryNewResult_iff.mp result
        subst after
        exact .allocate activationLive receiver classLive factoryLive
          selectorMatches parametersMatch
          (prologActivationParameterValues_iff.mp argumentsRead)
          (prologInstanceLayout_iff.mp layoutWitness)
  · intro derivation
    cases derivation with
    | allocate activationLive receiver classLive factoryLive selectorMatches
        parametersMatch argumentsRead layoutWitness =>
        exact .allocate activationLive receiver classLive factoryLive
          selectorMatches parametersMatch
          (prologActivationParameterValues_iff.mpr argumentsRead)
          (prologInstanceLayout_iff.mpr layoutWitness) (.build)

inductive PrologMessageInitializerMatch (message : Message)
    (selector : Selector) (parameters : List ParameterId) : Bool → Prop where
  | success :
      message.selector = selector →
      message.arguments.length = parameters.length →
      PrologMessageInitializerMatch message selector parameters true
  | selectorMismatch :
      message.selector ≠ selector →
      PrologMessageInitializerMatch message selector parameters false
  | arityMismatch :
      message.selector = selector →
      message.arguments.length ≠ parameters.length →
      PrologMessageInitializerMatch message selector parameters false

private theorem message_matches_initializer_eq_true {message : Message}
    {selector : Selector} {parameters : List ParameterId} :
    message.matchesInitializer selector parameters = true ↔
      message.selector = selector ∧
        message.arguments.length = parameters.length := by
  simp [Message.matchesInitializer, Bool.and_eq_true]

theorem prologMessageInitializerMatch_iff {message : Message}
    {selector : Selector} {parameters : List ParameterId} {result : Bool} :
    PrologMessageInitializerMatch message selector parameters result ↔
      message.matchesInitializer selector parameters = result := by
  constructor
  · intro derivation
    cases derivation with
    | success selectorMatches arityMatches =>
        simp [Message.matchesInitializer, selectorMatches, arityMatches]
    | selectorMismatch different =>
        simp [Message.matchesInitializer, different]
    | arityMismatch selectorMatches different =>
        simp [Message.matchesInitializer, selectorMatches, different]
  · intro equality
    by_cases selectorMatches : message.selector = selector
    · by_cases arityMatches : message.arguments.length = parameters.length
      · have matchTrue :
            message.matchesInitializer selector parameters = true :=
          message_matches_initializer_eq_true.mpr
            ⟨selectorMatches, arityMatches⟩
        have resultTrue : result = true := equality.symm.trans matchTrue
        rw [resultTrue]
        exact .success selectorMatches arityMatches
      · have matchFalse :
            message.matchesInitializer selector parameters = false := by
          cases matchResult : message.matchesInitializer selector parameters with
          | false => rfl
          | true =>
              exact (arityMatches
                (message_matches_initializer_eq_true.mp matchResult).2).elim
        have resultFalse : result = false := equality.symm.trans matchFalse
        rw [resultFalse]
        exact .arityMismatch selectorMatches arityMatches
    · have matchFalse :
          message.matchesInitializer selector parameters = false := by
        cases matchResult : message.matchesInitializer selector parameters with
        | false => rfl
        | true =>
            exact (selectorMatches
              (message_matches_initializer_eq_true.mp matchResult).1).elim
      have resultFalse : result = false := equality.symm.trans matchFalse
      rw [resultFalse]
      exact .selectorMismatch selectorMatches

inductive PrologMixinInitializerActivationDefinition (p : Program)
    (id : ActivationId) (mixin : MixinDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) : ActivationDef → Prop where
  | build :
      PrologMixinInitializerActivationDefinition p id mixin classId object
        message continuation
        (p.mixinInitializerActivationDefinition id mixin classId object message
          continuation)

theorem prologMixinInitializerActivationDefinition_iff {p : Program}
    {id : ActivationId} {mixin : MixinDef} {classId : ClassId}
    {object : ObjectId} {message : Message}
    {continuation : Option ActivationId} {activation : ActivationDef} :
    PrologMixinInitializerActivationDefinition p id mixin classId object
      message continuation activation ↔
      activation = p.mixinInitializerActivationDefinition id mixin classId
        object message continuation := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst activation
    exact .build

inductive PrologAllocateMixinInitializerActivation (p : Program)
    (state : AllocationState) (mixin : MixinDef) (classId : ClassId)
    (object : ObjectId) (message : Message)
    (continuation : Option ActivationId) :
    AllocationState → ActivationId → Prop where
  | allocate :
      PrologAllocateMixinInitializerActivation p state mixin classId object
        message continuation
        (p.allocateMixinInitializerActivation state mixin classId object message
          continuation).1
        (p.allocateMixinInitializerActivation state mixin classId object message
          continuation).2

theorem prologAllocateMixinInitializerActivation_iff {p : Program}
    {state next : AllocationState} {mixin : MixinDef} {classId : ClassId}
    {object : ObjectId} {message : Message}
    {continuation : Option ActivationId} {activation : ActivationId} :
    PrologAllocateMixinInitializerActivation p state mixin classId object
      message continuation next activation ↔
      p.allocateMixinInitializerActivation state mixin classId object message
        continuation = (next, activation) := by
  constructor
  · intro derivation
    cases derivation
    exact Prod.ext rfl rfl
  · intro equality
    rcases equality with ⟨rfl, rfl⟩
    exact .allocate

inductive PrologStartSuperclassInitialization (p : Program)
    (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (classId : ClassId)
    (object : ObjectId) (original : Message) (factory : FactoryDef) :
    SequentialConfig → Prop where
  | build :
      PrologStartSuperclassInitialization p state rest current frames classId
        object original factory
        (p.startSuperclassInitialization state rest current frames classId object
          original factory)

theorem prologStartSuperclassInitialization_iff {p : Program}
    {state : AllocationState} {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack} {classId : ClassId}
    {object : ObjectId} {original : Message} {factory : FactoryDef}
    {after : SequentialConfig} :
    PrologStartSuperclassInitialization p state rest current frames classId
      object original factory after ↔
      p.startSuperclassInitialization state rest current frames classId object
        original factory = after := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst after
    exact .build

inductive PrologInvokeSuperclassInitializer (p : Program)
    (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (classId superclass : ClassId)
    (object : ObjectId) (original : Message) (factory : FactoryDef)
    (message : Message) : SequentialConfig → Prop where
  | build :
      PrologInvokeSuperclassInitializer p state rest current frames classId
        superclass object original factory message
        (p.invokeSuperclassInitializer state rest current frames classId
          superclass object original factory message)

theorem prologInvokeSuperclassInitializer_iff {p : Program}
    {state : AllocationState} {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack}
    {classId superclass : ClassId} {object : ObjectId} {original : Message}
    {factory : FactoryDef} {message : Message} {after : SequentialConfig} :
    PrologInvokeSuperclassInitializer p state rest current frames classId
      superclass object original factory message after ↔
      p.invokeSuperclassInitializer state rest current frames classId superclass
        object original factory message = after := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst after
    exact .build

inductive PrologStartMixinInitialization (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (classId : ClassId) (object : ObjectId) (message : MessageTemplate) :
    SequentialConfig → Prop where
  | build :
      PrologStartMixinInitialization state rest current frames classId object
        message
        (Program.startMixinInitialization state rest current frames classId
          object message)

theorem prologStartMixinInitialization_iff {state : AllocationState}
    {rest : ActivationStack} {current : ActivationId} {frames : EvalStack}
    {classId : ClassId} {object : ObjectId} {message : MessageTemplate}
    {after : SequentialConfig} :
    PrologStartMixinInitialization state rest current frames classId object
      message after ↔
      Program.startMixinInitialization state rest current frames classId object
        message = after := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst after
    exact .build

inductive PrologInvokeMixinInitializer (p : Program)
    (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (classId : ClassId)
    (object : ObjectId) (mixin : MixinDef) (message : Message) :
    SequentialConfig → Prop where
  | build :
      PrologInvokeMixinInitializer p state rest current frames classId object
        mixin message
        (p.invokeMixinInitializer state rest current frames classId object mixin
          message)

theorem prologInvokeMixinInitializer_iff {p : Program}
    {state : AllocationState} {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack} {classId : ClassId}
    {object : ObjectId} {mixin : MixinDef} {message : Message}
    {after : SequentialConfig} :
    PrologInvokeMixinInitializer p state rest current frames classId object mixin
      message after ↔
      p.invokeMixinInitializer state rest current frames classId object mixin
        message = after := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst after
    exact .build

inductive PrologInitializationCoordinatorStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | atTop {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original : Message} {classDef : ClassDef} :
      state.heap.classes classId = some classDef →
      classDef.superclass = p.top →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initClass classId object original⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .ownInitialization classId object original⟩
  | startSuperclass {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original : Message} {classDef : ClassDef}
      {factory : FactoryDef} {after : SequentialConfig} :
      state.heap.classes classId = some classDef →
      classDef.superclass ≠ p.top →
      classDef.primaryFactory = some factory →
      PrologStartSuperclassInitialization p state rest current frames classId
        object original factory after →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .initClass classId object original⟩ after
  | invokeSuperclass {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original message : Message} {classDef : ClassDef}
      {superclassDef : ClassDef} {factory : FactoryDef}
      {after : SequentialConfig} :
      state.heap.classes classId = some classDef →
      state.heap.classes classDef.superclass = some superclassDef →
      superclassDef.primaryFactory = some factory →
      PrologMessageInitializerMatch message factory.selector factory.parameters
        true →
      PrologInvokeSuperclassInitializer p state rest current frames classId
        classDef.superclass object original factory message after →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current,
          .push frames (.superclassMessage classId object original)⟩,
          .messageValue message⟩ after
  | wrongSuperclassFactory {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original message : Message} {classDef : ClassDef}
      {superclassDef : ClassDef} {factory : FactoryDef} :
      state.heap.classes classId = some classDef →
      state.heap.classes classDef.superclass = some superclassDef →
      superclassDef.primaryFactory = some factory →
      PrologMessageInitializerMatch message factory.selector factory.parameters
        false →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current,
          .push frames (.superclassMessage classId object original)⟩,
          .messageValue message⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError .wrongFactory⟩
  | invokeMixin {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {message : Message} {classDef : ClassDef}
      {mixin : MixinDef} {after : SequentialConfig} :
      state.heap.classes classId = some classDef →
      p.mixins classDef.mixin = some mixin →
      PrologMessageInitializerMatch message mixin.initializerSelector
        mixin.initializerParameters true →
      PrologInvokeMixinInitializer p state rest current frames classId object
        mixin message after →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinMessage classId object)⟩, .messageValue message⟩
        after
  | wrongMixinFactory {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {message : Message} {classDef : ClassDef}
      {mixin : MixinDef} :
      state.heap.classes classId = some classDef →
      p.mixins classDef.mixin = some mixin →
      PrologMessageInitializerMatch message mixin.initializerSelector
        mixin.initializerParameters false →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinMessage classId object)⟩, .messageValue message⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError .wrongFactory⟩
  | afterSuperclass {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original : Message} :
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current,
          .push frames (.afterSuperclass classId object original)⟩,
          .object (.ordinaryObject object)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .ownInitialization classId object original⟩
  | afterMixin {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} :
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current,
          .push frames (.afterMixin classId object)⟩,
          .object (.ordinaryObject object)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .finish (.ordinaryObject object)⟩
  | ownBody {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original : Message} {classDef : ClassDef}
      {factory : FactoryDef} {mixin : MixinDef}
      {superclassMessage : MessageTemplate} :
      state.heap.classes classId = some classDef →
      classDef.primaryFactory = some factory →
      p.mixins classDef.mixin = some mixin →
      factory.plan = .body superclassMessage →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .ownInitialization classId object original⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .initializeSlotGroups object mixin.initializerGroups
            mixin.initializerBody⟩
  | ownAppliedMixin {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {classId : ClassId}
      {object : ObjectId} {original : Message} {classDef : ClassDef}
      {factory : FactoryDef} {mixin : MixinDef}
      {superclassMessage mixinMessage : MessageTemplate}
      {after : SequentialConfig} :
      state.heap.classes classId = some classDef →
      classDef.primaryFactory = some factory →
      p.mixins classDef.mixin = some mixin →
      factory.plan = .appliedMixin superclassMessage mixinMessage →
      PrologStartMixinInitialization state rest current frames classId object
        mixinMessage after →
      PrologInitializationCoordinatorStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .ownInitialization classId object original⟩ after

theorem prologInitializationCoordinatorStep_sound {p : Program}
    {before after : SequentialConfig}
    (derivation : PrologInitializationCoordinatorStep p before after) :
    p.initializationCoordinatorNext before = some after := by
  cases derivation with
  | atTop live superclass =>
      simp [Program.initializationCoordinatorNext, live, superclass]
  | startSuperclass live notTop factory start =>
      simp [Program.initializationCoordinatorNext, live, notTop, factory,
        prologStartSuperclassInitialization_iff.mp start]
  | invokeSuperclass live superclass factory matchWitness invoke =>
      simp [Program.initializationCoordinatorNext, live, superclass, factory,
        prologMessageInitializerMatch_iff.mp matchWitness,
        prologInvokeSuperclassInitializer_iff.mp invoke]
  | wrongSuperclassFactory live superclass factory matchWitness =>
      simp [Program.initializationCoordinatorNext, live, superclass, factory,
        prologMessageInitializerMatch_iff.mp matchWitness]
  | invokeMixin live found matchWitness invoke =>
      simp [Program.initializationCoordinatorNext, live, found,
        prologMessageInitializerMatch_iff.mp matchWitness,
        prologInvokeMixinInitializer_iff.mp invoke]
  | wrongMixinFactory live found matchWitness =>
      simp [Program.initializationCoordinatorNext, live, found,
        prologMessageInitializerMatch_iff.mp matchWitness]
  | afterSuperclass => simp [Program.initializationCoordinatorNext]
  | afterMixin => simp [Program.initializationCoordinatorNext]
  | ownBody live factory found plan =>
      simp [Program.initializationCoordinatorNext, live, factory, found, plan]
  | ownAppliedMixin live factory found plan start =>
      simp [Program.initializationCoordinatorNext, live, factory, found, plan,
        prologStartMixinInitialization_iff.mp start]

theorem prologInitializationCoordinatorStep_complete {p : Program}
    {before after : SequentialConfig}
    (next : p.initializationCoordinatorNext before = some after) :
    PrologInitializationCoordinatorStep p before after := by
  rcases before with ⟨state, stack, control⟩
  cases stack with
  | empty => simp [Program.initializationCoordinatorNext] at next
  | push rest frame =>
      rcases frame with ⟨current, frames⟩
      cases control
      case initClass classId object original =>
        cases live : state.heap.classes classId with
        | none => simp [Program.initializationCoordinatorNext, live] at next
        | some classDef =>
            by_cases atTop : classDef.superclass = p.top
            · simp [Program.initializationCoordinatorNext, live, atTop] at next
              subst after
              exact .atTop live atTop
            · cases factory : classDef.primaryFactory with
              | none =>
                  simp [Program.initializationCoordinatorNext, live, atTop,
                    factory] at next
              | some factoryDef =>
                  simp [Program.initializationCoordinatorNext, live, atTop,
                    factory] at next
                  exact .startSuperclass live atTop factory
                    (prologStartSuperclassInitialization_iff.mpr next)
      case messageValue message =>
        cases frames with
        | empty => simp [Program.initializationCoordinatorNext] at next
        | push below top =>
            cases top
            case superclassMessage classId object original =>
              cases live : state.heap.classes classId with
              | none =>
                  simp [Program.initializationCoordinatorNext, live] at next
              | some classDef =>
                  cases superclassLive : state.heap.classes classDef.superclass with
                  | none =>
                      simp [Program.initializationCoordinatorNext, live,
                        superclassLive] at next
                  | some superclassDef =>
                      cases factory : superclassDef.primaryFactory with
                      | none =>
                          simp [Program.initializationCoordinatorNext, live,
                            superclassLive, factory] at next
                      | some factoryDef =>
                          cases matchResult : message.matchesInitializer
                              factoryDef.selector factoryDef.parameters with
                          | false =>
                              simp [Program.initializationCoordinatorNext, live,
                                superclassLive, factory, matchResult] at next
                              subst after
                              exact .wrongSuperclassFactory live superclassLive
                                factory
                                (prologMessageInitializerMatch_iff.mpr matchResult)
                          | true =>
                              simp [Program.initializationCoordinatorNext, live,
                                superclassLive, factory, matchResult] at next
                              exact .invokeSuperclass live superclassLive factory
                                (prologMessageInitializerMatch_iff.mpr matchResult)
                                (prologInvokeSuperclassInitializer_iff.mpr next)
            case mixinMessage classId object =>
              cases live : state.heap.classes classId with
              | none =>
                  simp [Program.initializationCoordinatorNext, live] at next
              | some classDef =>
                  cases found : p.mixins classDef.mixin with
                  | none =>
                      simp [Program.initializationCoordinatorNext, live, found]
                        at next
                  | some mixin =>
                      cases matchResult : message.matchesInitializer
                          mixin.initializerSelector mixin.initializerParameters with
                      | false =>
                          simp [Program.initializationCoordinatorNext, live, found,
                            matchResult] at next
                          subst after
                          exact .wrongMixinFactory live found
                            (prologMessageInitializerMatch_iff.mpr matchResult)
                      | true =>
                          simp [Program.initializationCoordinatorNext, live, found,
                            matchResult] at next
                          exact .invokeMixin live found
                            (prologMessageInitializerMatch_iff.mpr matchResult)
                            (prologInvokeMixinInitializer_iff.mpr next)
            all_goals simp [Program.initializationCoordinatorNext] at next
      case object value =>
        cases value with
        | ordinaryObject result =>
            cases frames with
            | empty => simp [Program.initializationCoordinatorNext] at next
            | push below top =>
                cases top
                case afterSuperclass classId object original =>
                  by_cases same : result = object
                  · subst result
                    simp [Program.initializationCoordinatorNext] at next
                    subst after
                    exact .afterSuperclass
                  · simp [Program.initializationCoordinatorNext, same] at next
                case afterMixin classId object =>
                  by_cases same : result = object
                  · subst result
                    simp [Program.initializationCoordinatorNext] at next
                    subst after
                    exact .afterMixin
                  · simp [Program.initializationCoordinatorNext, same] at next
                all_goals simp [Program.initializationCoordinatorNext] at next
        | classObject classId =>
            simp [Program.initializationCoordinatorNext] at next
        | mixinObject mixinId =>
            simp [Program.initializationCoordinatorNext] at next
        | activationObject activationId =>
            simp [Program.initializationCoordinatorNext] at next
        | closureObject closureId =>
            simp [Program.initializationCoordinatorNext] at next
        | mirrorObject mirrorId =>
            simp [Program.initializationCoordinatorNext] at next
        | actorObject actorId =>
            simp [Program.initializationCoordinatorNext] at next
      case ownInitialization classId object original =>
        cases live : state.heap.classes classId with
        | none => simp [Program.initializationCoordinatorNext, live] at next
        | some classDef =>
            cases factory : classDef.primaryFactory with
            | none =>
                simp [Program.initializationCoordinatorNext, live, factory] at next
            | some factoryDef =>
                cases found : p.mixins classDef.mixin with
                | none =>
                    simp [Program.initializationCoordinatorNext, live, factory,
                      found] at next
                | some mixin =>
                    cases plan : factoryDef.plan with
                    | body superclassMessage =>
                        simp [Program.initializationCoordinatorNext, live, factory,
                          found, plan] at next
                        subst after
                        exact .ownBody live factory found plan
                    | appliedMixin superclassMessage mixinMessage =>
                        simp [Program.initializationCoordinatorNext, live, factory,
                          found, plan] at next
                        exact .ownAppliedMixin live factory found plan
                          (prologStartMixinInitialization_iff.mpr next)
      all_goals simp [Program.initializationCoordinatorNext] at next

theorem prologInitializationCoordinatorStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologInitializationCoordinatorStep p before after ↔
      p.InitializationCoordinatorStep before after := by
  constructor
  · intro derivation
    exact .graph (prologInitializationCoordinatorStep_sound derivation)
  · intro derivation
    cases derivation with
    | graph next => exact prologInitializationCoordinatorStep_complete next

inductive PrologInstanceInitializationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | factory {before after : SequentialConfig} :
      PrologFactoryNewStep p before after →
        PrologInstanceInitializationStep p before after
  | coordinator {before after : SequentialConfig} :
      PrologInitializationCoordinatorStep p before after →
        PrologInstanceInitializationStep p before after
  | slots {before after : SequentialConfig} :
      PrologSlotInitializationStep p before after →
        PrologInstanceInitializationStep p before after

theorem prologInstanceInitializationStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologInstanceInitializationStep p before after ↔
      p.InstanceInitializationStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | factory step => exact .factory (prologFactoryNewStep_iff.mp step)
    | coordinator step =>
        exact .coordinator (prologInitializationCoordinatorStep_iff.mp step)
    | slots step => exact .slots (prologSlotInitializationStep_iff.mp step)
  · intro derivation
    cases derivation with
    | factory step => exact .factory (prologFactoryNewStep_iff.mpr step)
    | coordinator step =>
        exact .coordinator (prologInitializationCoordinatorStep_iff.mpr step)
    | slots step => exact .slots (prologSlotInitializationStep_iff.mpr step)

inductive PrologClassEnclosingObjectFromActivation :
    Option ActivationDef → Option ObjRef → Prop where
  | missing : PrologClassEnclosingObjectFromActivation none none
  | live {activation : ActivationDef} :
      PrologClassEnclosingObjectFromActivation (some activation)
        (some activation.currentReceiver)

theorem prologClassEnclosingObjectFromActivation_iff
    {activation : Option ActivationDef} {result : Option ObjRef} :
    PrologClassEnclosingObjectFromActivation activation result ↔
      activation.map ActivationDef.currentReceiver = result := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases activation with
    | none =>
        simp at equality
        subst result
        exact .missing
    | some definition =>
        simp at equality
        subst result
        exact .live

inductive PrologClassEnclosingObject (p : Program) (h : Heap)
    (activation : ActivationId) (declaration : ClassDeclId) :
    Option ObjRef → Prop where
  | activationOwner :
      p.classOwner declaration = .activationOwner →
      PrologClassEnclosingObject p h activation declaration
        (some (.activationObject activation))
  | classOwner {activationResult : Option ActivationDef}
      {result : Option ObjRef} :
      p.classOwner declaration = .classOwner →
      h.activations activation = activationResult →
      PrologClassEnclosingObjectFromActivation activationResult result →
      PrologClassEnclosingObject p h activation declaration result
  | objectLiteralOwner {activationResult : Option ActivationDef}
      {result : Option ObjRef} :
      p.classOwner declaration = .objectLiteralOwner →
      h.activations activation = activationResult →
      PrologClassEnclosingObjectFromActivation activationResult result →
      PrologClassEnclosingObject p h activation declaration result
  | topOwner :
      p.classOwner declaration = .topOwner →
      PrologClassEnclosingObject p h activation declaration (some p.nilObject)

theorem prologClassEnclosingObject_iff {p : Program} {h : Heap}
    {activation : ActivationId} {declaration : ClassDeclId}
    {result : Option ObjRef} :
    PrologClassEnclosingObject p h activation declaration result ↔
      p.classEnclosingObject h activation declaration = result := by
  constructor
  · intro derivation
    cases derivation with
    | activationOwner owner =>
        simp [Program.classEnclosingObject, owner]
    | classOwner owner activationFound receiver =>
        simpa [Program.classEnclosingObject, owner, activationFound] using
          prologClassEnclosingObjectFromActivation_iff.mp receiver
    | objectLiteralOwner owner activationFound receiver =>
        simpa [Program.classEnclosingObject, owner, activationFound] using
          prologClassEnclosingObjectFromActivation_iff.mp receiver
    | topOwner owner => simp [Program.classEnclosingObject, owner]
  · intro equality
    cases owner : p.classOwner declaration with
    | activationOwner =>
        simp [Program.classEnclosingObject, owner] at equality
        subst result
        exact .activationOwner owner
    | classOwner =>
        cases activationFound : h.activations activation with
        | none =>
            simp [Program.classEnclosingObject, owner, activationFound] at equality
            subst result
            exact .classOwner owner activationFound .missing
        | some definition =>
            simp [Program.classEnclosingObject, owner, activationFound] at equality
            subst result
            exact .classOwner owner activationFound .live
    | objectLiteralOwner =>
        cases activationFound : h.activations activation with
        | none =>
            simp [Program.classEnclosingObject, owner, activationFound] at equality
            subst result
            exact .objectLiteralOwner owner activationFound .missing
        | some definition =>
            simp [Program.classEnclosingObject, owner, activationFound] at equality
            subst result
            exact .objectLiteralOwner owner activationFound .live
    | topOwner =>
        simp [Program.classEnclosingObject, owner] at equality
        subst result
        exact .topOwner owner

inductive PrologInheritanceError (h : Heap) :
    ObjRef → MessageTemplate → Option RuntimeError → Prop where
  | missingClass {classId : ClassId} {message : MessageTemplate} :
      h.classes classId = none →
      PrologInheritanceError h (.classObject classId) message
        (some .classExpected)
  | nonInstantiable {classId : ClassId} {classDef : ClassDef}
      {message : MessageTemplate} :
      h.classes classId = some classDef →
      classDef.primaryFactory = none →
      PrologInheritanceError h (.classObject classId) message
        (some .classNotInstantiable)
  | valid {classId : ClassId} {classDef : ClassDef} {factory : FactoryDef}
      {message : MessageTemplate} :
      h.classes classId = some classDef →
      classDef.primaryFactory = some factory →
      factory.selector = message.selector →
      PrologInheritanceError h (.classObject classId) message none
  | wrongFactory {classId : ClassId} {classDef : ClassDef}
      {factory : FactoryDef} {message : MessageTemplate} :
      h.classes classId = some classDef →
      classDef.primaryFactory = some factory →
      factory.selector ≠ message.selector →
      PrologInheritanceError h (.classObject classId) message
        (some .wrongFactory)
  | ordinaryObject {object : ObjectId} {message : MessageTemplate} :
      PrologInheritanceError h (.ordinaryObject object) message
        (some .classExpected)
  | mixinObject {mixin : MixinId} {message : MessageTemplate} :
      PrologInheritanceError h (.mixinObject mixin) message
        (some .classExpected)
  | activationObject {activation : ActivationId} {message : MessageTemplate} :
      PrologInheritanceError h (.activationObject activation) message
        (some .classExpected)
  | closureObject {closure : ClosureId} {message : MessageTemplate} :
      PrologInheritanceError h (.closureObject closure) message
        (some .classExpected)
  | mirrorObject {mirror : MirrorId} {message : MessageTemplate} :
      PrologInheritanceError h (.mirrorObject mirror) message
        (some .classExpected)
  | actorObject {actor : ActorId} {message : MessageTemplate} :
      PrologInheritanceError h (.actorObject actor) message
        (some .classExpected)

theorem prologInheritanceError_iff {h : Heap} {value : ObjRef}
    {message : MessageTemplate} {result : Option RuntimeError} :
    PrologInheritanceError h value message result ↔
      Program.inheritanceError h value message = result := by
  constructor
  · intro derivation
    cases derivation with
    | missingClass missing =>
        simp [Program.inheritanceError, missing]
    | nonInstantiable live noFactory =>
        simp [Program.inheritanceError, live, noFactory]
    | valid live factory selector =>
        simp [Program.inheritanceError, live, factory, selector]
    | wrongFactory live factory selector =>
        simp [Program.inheritanceError, live, factory, selector]
    | ordinaryObject | mixinObject | activationObject | closureObject |
        mirrorObject | actorObject =>
        rfl
  · intro equality
    cases value with
    | classObject classId =>
        cases live : h.classes classId with
        | none =>
            simp [Program.inheritanceError, live] at equality
            subst result
            exact .missingClass live
        | some classDef =>
            cases factoryFound : classDef.primaryFactory with
            | none =>
                simp [Program.inheritanceError, live, factoryFound] at equality
                subst result
                exact .nonInstantiable live factoryFound
            | some factory =>
                by_cases selectorMatches : factory.selector = message.selector
                · simp [Program.inheritanceError, live, factoryFound,
                    selectorMatches] at equality
                  subst result
                  exact .valid live factoryFound selectorMatches
                · simp [Program.inheritanceError, live, factoryFound,
                    selectorMatches] at equality
                  subst result
                  exact .wrongFactory live factoryFound selectorMatches
    | ordinaryObject object =>
        simp [Program.inheritanceError] at equality
        subst result
        exact .ordinaryObject
    | mixinObject mixin =>
        simp [Program.inheritanceError] at equality
        subst result
        exact .mixinObject
    | activationObject activation =>
        simp [Program.inheritanceError] at equality
        subst result
        exact .activationObject
    | closureObject closure =>
        simp [Program.inheritanceError] at equality
        subst result
        exact .closureObject
    | mirrorObject mirror =>
        simp [Program.inheritanceError] at equality
        subst result
        exact .mirrorObject
    | actorObject actor =>
        simp [Program.inheritanceError] at equality
        subst result
        exact .actorObject

inductive PrologBodyFactory (descriptor : ClassBodyDescriptor) :
    FactoryDef → Prop where
  | build : PrologBodyFactory descriptor (Program.bodyFactory descriptor)

theorem prologBodyFactory_iff {descriptor : ClassBodyDescriptor}
    {factory : FactoryDef} :
    PrologBodyFactory descriptor factory ↔
      factory = Program.bodyFactory descriptor := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst factory
    exact .build

inductive PrologApplicationFactory
    (descriptor : MixinApplicationDescriptor) : FactoryDef → Prop where
  | build :
      PrologApplicationFactory descriptor (Program.applicationFactory descriptor)

theorem prologApplicationFactory_iff
    {descriptor : MixinApplicationDescriptor} {factory : FactoryDef} :
    PrologApplicationFactory descriptor factory ↔
      factory = Program.applicationFactory descriptor := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    subst factory
    exact .build

inductive PrologAllocateClassPair (p : Program) (state : AllocationState)
    (origin : ClassOrigin) (instanceMixin classMixin : MixinId)
    (superclass : ClassId) (enclosingObject : ObjRef) (factory : FactoryDef) :
    AllocationState → ClassId → ClassId → Prop where
  | allocate :
      PrologAllocateClassPair p state origin instanceMixin classMixin superclass
        enclosingObject factory
        (p.allocateClassPair state origin instanceMixin classMixin superclass
          enclosingObject factory).1
        (p.allocateClassPair state origin instanceMixin classMixin superclass
          enclosingObject factory).2.1
        (p.allocateClassPair state origin instanceMixin classMixin superclass
          enclosingObject factory).2.2

theorem prologAllocateClassPair_iff {p : Program} {state next : AllocationState}
    {origin : ClassOrigin} {instanceMixin classMixin : MixinId}
    {superclass : ClassId} {enclosingObject : ObjRef} {factory : FactoryDef}
    {classId metaclassId : ClassId} :
    PrologAllocateClassPair p state origin instanceMixin classMixin superclass
      enclosingObject factory next classId metaclassId ↔
      p.allocateClassPair state origin instanceMixin classMixin superclass
        enclosingObject factory = (next, classId, metaclassId) := by
  constructor
  · intro derivation
    cases derivation
    exact Prod.ext rfl (Prod.ext rfl rfl)
  · intro equality
    rcases equality with ⟨rfl, rfl, rfl⟩
    exact .allocate

inductive PrologValidTopSuperclass (p : Program) (enclosingObject : ObjRef)
    (superclassSyntax : SuperclassSyntax) (superclass : ClassId) : Bool → Prop where
  | nonTop :
      enclosingObject ≠ p.nilObject →
      PrologValidTopSuperclass p enclosingObject superclassSyntax superclass true
  | implicitObject :
      enclosingObject = p.nilObject →
      superclassSyntax = .implicitSuperclass →
      superclass = p.object →
      PrologValidTopSuperclass p enclosingObject superclassSyntax superclass true
  | explicitTop :
      enclosingObject = p.nilObject →
      superclassSyntax = .explicitSuperclass →
      PrologValidTopSuperclass p enclosingObject superclassSyntax superclass false
  | implicitNonObject :
      enclosingObject = p.nilObject →
      superclassSyntax = .implicitSuperclass →
      superclass ≠ p.object →
      PrologValidTopSuperclass p enclosingObject superclassSyntax superclass false

private theorem lawful_beq_eq_false_of_ne {alpha : Type}
    [BEq alpha] [LawfulBEq alpha] {left right : alpha}
    (different : left ≠ right) : (left == right) = false := by
  cases equal : left == right with
  | false => rfl
  | true => exact (different (beq_iff_eq.mp equal)).elim

theorem prologValidTopSuperclass_iff {p : Program} {enclosingObject : ObjRef}
    {superclassSyntax : SuperclassSyntax} {superclass : ClassId}
    {result : Bool} :
    PrologValidTopSuperclass p enclosingObject superclassSyntax superclass result ↔
      p.validTopSuperclass enclosingObject superclassSyntax superclass = result := by
  constructor
  · intro derivation
    cases derivation with
    | nonTop different =>
        simp [Program.validTopSuperclass, different]
    | implicitObject enclosing syntaxMatches superclassMatches =>
        simp [Program.validTopSuperclass, enclosing, syntaxMatches,
          superclassMatches]
    | explicitTop enclosing syntaxMatches =>
        simp [Program.validTopSuperclass, enclosing, syntaxMatches]
    | implicitNonObject enclosing syntaxMatches superclassDifferent =>
        simp [Program.validTopSuperclass, enclosing, syntaxMatches,
          superclassDifferent]
  · intro equality
    by_cases enclosingMatches : enclosingObject = p.nilObject
    · cases superclassSyntax with
      | implicitSuperclass =>
          by_cases superclassMatches : superclass = p.object
          · have resultTrue : result = true := by
              simpa [Program.validTopSuperclass, enclosingMatches,
                superclassMatches] using equality.symm
            rw [resultTrue]
            exact .implicitObject enclosingMatches rfl superclassMatches
          · have resultFalse : result = false := by
              have superclassBeqFalse :=
                lawful_beq_eq_false_of_ne superclassMatches
              simpa [Program.validTopSuperclass, enclosingMatches,
                superclassBeqFalse] using equality.symm
            rw [resultFalse]
            exact .implicitNonObject enclosingMatches rfl superclassMatches
      | explicitSuperclass =>
          have resultFalse : result = false := by
            have syntaxBeqFalse :
                ((SuperclassSyntax.explicitSuperclass ==
                  SuperclassSyntax.implicitSuperclass) = false) :=
              lawful_beq_eq_false_of_ne (by decide)
            simpa [Program.validTopSuperclass, enclosingMatches,
              syntaxBeqFalse] using equality.symm
          rw [resultFalse]
          exact .explicitTop enclosingMatches rfl
    · have resultTrue : result = true := by
        have enclosingBneTrue :
            (enclosingObject != p.nilObject) = true :=
          bne_iff_ne.mpr enclosingMatches
        simpa [Program.validTopSuperclass, enclosingBneTrue] using equality.symm
      rw [resultTrue]
      exact .nonTop enclosingMatches

/-- The nine operational class-construction clauses exactly as printed in the
    LaTeX semantics.  In particular, commit is not guarded by a meta-level
    proof about the resulting heap. -/
inductive PrologClassConstructionStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | bodyStart {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {declaration : ClassDeclId}
      {superclassExpression : CoreExpr} {descriptor : ClassBodyDescriptor}
      {enclosingObject : ObjRef} :
      p.classBodies declaration = some descriptor →
      PrologClassEnclosingObject p state.heap current declaration
        (some enclosingObject) →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.classBody declaration superclassExpression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor enclosingObject)⟩,
          .evaluate superclassExpression⟩
  | bodyCommit {state next : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ClassBodyDescriptor} {enclosingObject : ObjRef}
      {superclass classId metaclassId : ClassId} :
      PrologInheritanceError state.heap (.classObject superclass)
        descriptor.superclassMessage none →
      PrologValidTopSuperclass p enclosingObject descriptor.superclassSyntax
        superclass true →
      PrologAllocateClassPair p state
        (.expression (.namedClass descriptor.declaration))
        descriptor.instanceMixin descriptor.classMixin superclass
        enclosingObject (Program.bodyFactory descriptor)
        next classId metaclassId →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor enclosingObject)⟩,
          .object (.classObject superclass)⟩
        ⟨next, .push rest ⟨current, frames⟩,
          .object (.classObject classId)⟩
  | bodyInheritanceError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ClassBodyDescriptor} {enclosingObject : ObjRef}
      {value : ObjRef} {error : RuntimeError} :
      PrologInheritanceError state.heap value descriptor.superclassMessage
        (some error) →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor enclosingObject)⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
  | bodyTopError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ClassBodyDescriptor} {superclass : ClassId} :
      PrologInheritanceError state.heap (.classObject superclass)
        descriptor.superclassMessage none →
      PrologValidTopSuperclass p p.nilObject descriptor.superclassSyntax
        superclass false →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeClassBody descriptor p.nilObject)⟩,
          .object (.classObject superclass)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .runtimeError .topSuperclass⟩
  | mixinStart {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {declaration : ClassDeclId}
      {superclassExpression mixinExpression : CoreExpr}
      {descriptor : MixinApplicationDescriptor} :
      p.mixinApplications declaration = some descriptor →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.mixinApply declaration superclassExpression
            mixinExpression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSuperclass descriptor mixinExpression)⟩,
          .evaluate superclassExpression⟩
  | mixinSuperclassDone {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {mixinExpression : CoreExpr}
      {superclass : ClassId} :
      PrologInheritanceError state.heap (.classObject superclass)
        descriptor.superclassMessage none →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSuperclass descriptor mixinExpression)⟩,
          .object (.classObject superclass)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSource descriptor superclass)⟩,
          .evaluate mixinExpression⟩
  | mixinCommit {state next : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {superclass source : ClassId}
      {sourceDef : ClassDef} {sourceFactory : FactoryDef}
      {classId metaclassId : ClassId} :
      state.heap.classes source = some sourceDef →
      sourceDef.primaryFactory = some sourceFactory →
      sourceFactory.selector = descriptor.mixinMessage.selector →
      sourceFactory.selector = descriptor.factorySelector →
      PrologAllocateClassPair p state
        (.expression (.namedClass descriptor.declaration)) sourceDef.mixin
        descriptor.classMixin superclass sourceDef.enclosingObject
        (Program.applicationFactory descriptor) next classId metaclassId →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSource descriptor superclass)⟩,
          .object (.classObject source)⟩
        ⟨next, .push rest ⟨current, frames⟩,
          .object (.classObject classId)⟩
  | mixinSuperclassError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {mixinExpression : CoreExpr}
      {value : ObjRef} {error : RuntimeError} :
      PrologInheritanceError state.heap value descriptor.superclassMessage
        (some error) →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSuperclass descriptor mixinExpression)⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
  | mixinSourceError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : MixinApplicationDescriptor} {superclass : ClassId}
      {value : ObjRef} {error : RuntimeError} :
      PrologInheritanceError state.heap value descriptor.mixinMessage
        (some error) →
      PrologClassConstructionStep p
        ⟨state, .push rest ⟨current,
          .push frames (.mixinSource descriptor superclass)⟩, .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩

/-- The precise extra obligation in Lean's current class-construction
    relation.  A non-allocating clause preserves the allocation state; an
    allocating clause must establish global well-formedness of the result. -/
def PrologClassConstructionCommitSafe (p : Program)
    (before after : SequentialConfig) : Prop :=
  before.allocation = after.allocation ∨ p.WellFormed after.allocation.heap

theorem prologClassConstructionStep_sound {p : Program}
    {before after : SequentialConfig}
    (step : PrologClassConstructionStep p before after)
    (safe : PrologClassConstructionCommitSafe p before after) :
    p.ClassConstructionStep before after := by
  cases step with
  | bodyStart descriptor enclosing =>
      exact .bodyStart descriptor
        (prologClassEnclosingObject_iff.mp enclosing)
  | bodyCommit inheritance topValid allocated =>
      simp only [PrologClassConstructionCommitSafe] at safe
      rcases safe with same | allocationWellFormed
      · subst_vars
        have allocatedEq := prologAllocateClassPair_iff.mp allocated
        have impossible := congrArg (fun result => result.1.nextClass)
          allocatedEq
        simp [Program.allocateClassPair] at impossible
      · exact .bodyCommit (prologInheritanceError_iff.mp inheritance)
          (prologValidTopSuperclass_iff.mp topValid)
          (prologAllocateClassPair_iff.mp allocated).symm allocationWellFormed
  | bodyInheritanceError invalid =>
      exact .bodyInheritanceError (prologInheritanceError_iff.mp invalid)
  | bodyTopError inheritance topInvalid =>
      exact .bodyTopError (prologInheritanceError_iff.mp inheritance)
        (prologValidTopSuperclass_iff.mp topInvalid)
  | mixinStart descriptor => exact .mixinStart descriptor
  | mixinSuperclassDone valid =>
      exact .mixinSuperclassDone (prologInheritanceError_iff.mp valid)
  | mixinCommit source factory mixinSelector factorySelector allocated =>
      simp only [PrologClassConstructionCommitSafe] at safe
      rcases safe with same | allocationWellFormed
      · subst_vars
        have allocatedEq := prologAllocateClassPair_iff.mp allocated
        have impossible := congrArg (fun result => result.1.nextClass)
          allocatedEq
        simp [Program.allocateClassPair] at impossible
      · exact .mixinCommit source factory mixinSelector factorySelector
          (prologAllocateClassPair_iff.mp allocated).symm allocationWellFormed
  | mixinSuperclassError invalid =>
      exact .mixinSuperclassError (prologInheritanceError_iff.mp invalid)
  | mixinSourceError invalid =>
      exact .mixinSourceError (prologInheritanceError_iff.mp invalid)

theorem prologClassConstructionStep_complete {p : Program}
    {before after : SequentialConfig}
    (step : p.ClassConstructionStep before after) :
    PrologClassConstructionStep p before after ∧
      PrologClassConstructionCommitSafe p before after := by
  cases step with
  | bodyStart descriptor enclosing =>
      exact ⟨.bodyStart descriptor
        (prologClassEnclosingObject_iff.mpr enclosing), .inl rfl⟩
  | bodyCommit inheritance topValid allocated allocationWellFormed =>
      refine ⟨?_, .inr allocationWellFormed⟩
      exact .bodyCommit (prologInheritanceError_iff.mpr inheritance)
          (prologValidTopSuperclass_iff.mpr topValid)
          (prologAllocateClassPair_iff.mpr allocated.symm)
  | bodyInheritanceError invalid =>
      exact ⟨.bodyInheritanceError (prologInheritanceError_iff.mpr invalid),
        .inl rfl⟩
  | bodyTopError inheritance topInvalid =>
      exact ⟨.bodyTopError (prologInheritanceError_iff.mpr inheritance)
        (prologValidTopSuperclass_iff.mpr topInvalid), .inl rfl⟩
  | mixinStart descriptor => exact ⟨.mixinStart descriptor, .inl rfl⟩
  | mixinSuperclassDone valid =>
      exact ⟨.mixinSuperclassDone (prologInheritanceError_iff.mpr valid),
        .inl rfl⟩
  | mixinCommit source factory mixinSelector factorySelector allocated
      allocationWellFormed =>
      refine ⟨?_, .inr allocationWellFormed⟩
      exact .mixinCommit source factory mixinSelector factorySelector
        (prologAllocateClassPair_iff.mpr allocated.symm)
  | mixinSuperclassError invalid =>
      exact ⟨.mixinSuperclassError (prologInheritanceError_iff.mpr invalid),
        .inl rfl⟩
  | mixinSourceError invalid =>
      exact ⟨.mixinSourceError (prologInheritanceError_iff.mpr invalid),
        .inl rfl⟩

theorem prologClassConstructionStep_iff {p : Program}
    {before after : SequentialConfig} :
    (PrologClassConstructionStep p before after ∧
      PrologClassConstructionCommitSafe p before after) ↔
      p.ClassConstructionStep before after := by
  constructor
  · rintro ⟨derivation, safe⟩
    exact prologClassConstructionStep_sound derivation safe
  · exact prologClassConstructionStep_complete

/-! ## Object literals and receiver-local nested classes -/

inductive PrologObjectLiteralEnclosingObject (p : Program) (h : Heap)
    (activation : ActivationId) : Option ObjRef → Prop where
  | top {definition : ActivationDef} :
      h.activations activation = some definition →
      definition.provenance = .top →
      PrologObjectLiteralEnclosingObject p h activation (some p.nilObject)
  | nonTop {definition : ActivationDef} :
      h.activations activation = some definition →
      definition.provenance ≠ .top →
      PrologObjectLiteralEnclosingObject p h activation
        (some (.activationObject activation))
  | missing : h.activations activation = none →
      PrologObjectLiteralEnclosingObject p h activation none

theorem prologObjectLiteralEnclosingObject_iff {p : Program} {h : Heap}
    {activation : ActivationId} {result : Option ObjRef} :
    PrologObjectLiteralEnclosingObject p h activation result ↔
      p.objectLiteralEnclosingObject h activation = result := by
  constructor
  · intro derivation
    cases derivation with
    | top live provenance =>
        simp [Program.objectLiteralEnclosingObject, live, provenance]
    | @nonTop definition live provenance =>
        cases provenanceResult : definition.provenance with
        | top => exact (provenance provenanceResult).elim
        | method identity =>
            simp [Program.objectLiteralEnclosingObject, live, provenanceResult]
        | closure declaration =>
            simp [Program.objectLiteralEnclosingObject, live, provenanceResult]
        | initializer declaration =>
            simp [Program.objectLiteralEnclosingObject, live, provenanceResult]
    | missing absent =>
        simp [Program.objectLiteralEnclosingObject, absent]
  · intro equality
    cases live : h.activations activation with
    | none =>
        simp [Program.objectLiteralEnclosingObject, live] at equality
        subst result
        exact .missing live
    | some definition =>
        cases provenance : definition.provenance with
        | top =>
            simp [Program.objectLiteralEnclosingObject, live, provenance] at equality
            subst result
            exact .top live provenance
        | method identity =>
            simp [Program.objectLiteralEnclosingObject, live, provenance] at equality
            subst result
            exact .nonTop live (by simp [provenance])
        | closure declaration =>
            simp [Program.objectLiteralEnclosingObject, live, provenance] at equality
            subst result
            exact .nonTop live (by simp [provenance])
        | initializer declaration =>
            simp [Program.objectLiteralEnclosingObject, live, provenance] at equality
            subst result
            exact .nonTop live (by simp [provenance])

inductive PrologObjectLiteralFactory (descriptor : ObjectLiteralDescriptor)
    (mixin : MixinDef) : FactoryDef → Prop where
  | application : PrologObjectLiteralFactory descriptor mixin
      { activationDeclaration := descriptor.initializerDeclaration
        selector := mixin.initializerSelector
        parameters := []
        plan := .body descriptor.superclassMessage }

theorem prologObjectLiteralFactory_iff
    {descriptor : ObjectLiteralDescriptor} {mixin : MixinDef}
    {factory : FactoryDef} :
    PrologObjectLiteralFactory descriptor mixin factory ↔
      Program.objectLiteralFactory descriptor mixin = factory := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

inductive PrologObjectLiteralNewMessage (mixin : MixinDef) : Message → Prop where
  | application : PrologObjectLiteralNewMessage mixin
      ⟨mixin.initializerSelector, []⟩

theorem prologObjectLiteralNewMessage_iff {mixin : MixinDef}
    {message : Message} :
    PrologObjectLiteralNewMessage mixin message ↔
      Program.objectLiteralNewMessage mixin = message := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

inductive PrologReadNestedClass (h : Heap) (object : ObjectId)
    (declaration : NestedCacheId) : Option ClassId → Prop where
  | missingObject : h.objects object = none →
      PrologReadNestedClass h object declaration none
  | liveObject {definition : ObjectDef} {result : Option ClassId} :
      h.objects object = some definition →
      definition.nestedClasses declaration = result →
      PrologReadNestedClass h object declaration result

theorem prologReadNestedClass_iff {h : Heap} {object : ObjectId}
    {declaration : NestedCacheId} {result : Option ClassId} :
    PrologReadNestedClass h object declaration result ↔
      h.readNestedClass object declaration = result := by
  constructor
  · intro derivation
    cases derivation with
    | missingObject missing => simp [Heap.readNestedClass, missing]
    | liveObject live nested =>
        simp [Heap.readNestedClass, live, nested]
  · intro equality
    cases live : h.objects object with
    | none =>
        simp [Heap.readNestedClass, live] at equality
        subst result
        exact .missingObject live
    | some definition =>
        exact .liveObject live (by
          simpa [Heap.readNestedClass, live] using equality)

inductive PrologWriteNestedClass (h : Heap) (object : ObjectId)
    (declaration : NestedCacheId) (classId : ClassId) : Heap → Prop where
  | liveObject {definition : ObjectDef} :
      h.objects object = some definition →
      PrologWriteNestedClass h object declaration classId
        (h.installObject object
          { definition with nestedClasses :=
              definition.nestedClasses.install declaration classId })

theorem prologWriteNestedClass_iff {h next : Heap} {object : ObjectId}
    {declaration : NestedCacheId} {classId : ClassId} :
    PrologWriteNestedClass h object declaration classId next ↔
      h.writeNestedClass object declaration classId = some next := by
  constructor
  · intro derivation
    cases derivation with
    | liveObject live => simp [Heap.writeNestedClass, live]
  · intro equality
    cases live : h.objects object with
    | none => simp [Heap.writeNestedClass, live] at equality
    | some definition =>
        simp [Heap.writeNestedClass, live] at equality
        subst next
        exact .liveObject live

inductive PrologEvaluateNestedClassMiss (p : Program)
    (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (object : ObjectId)
    (declaration : NestedCacheId) : CoreExpr → SequentialConfig → Prop where
  | classBody {classDeclaration : ClassDeclId}
      {superclassExpression : CoreExpr} {descriptor : ClassBodyDescriptor} :
      p.classBodies classDeclaration = some descriptor →
      PrologEvaluateNestedClassMiss p state rest current frames object declaration
        (.classBody classDeclaration superclassExpression)
        ⟨state, .push rest ⟨current,
          .push (.push frames (.nestedClassStore object declaration))
            (.makeClassBody descriptor (.ordinaryObject object))⟩,
          .evaluate superclassExpression⟩
  | mixinApply {classDeclaration : ClassDeclId}
      {superclassExpression mixinExpression : CoreExpr} :
      PrologEvaluateNestedClassMiss p state rest current frames object declaration
        (.mixinApply classDeclaration superclassExpression mixinExpression)
        ⟨state, .push rest ⟨current,
          .push frames (.nestedClassStore object declaration)⟩,
          .evaluate (.mixinApply classDeclaration superclassExpression
            mixinExpression)⟩

theorem prologEvaluateNestedClassMiss_iff {p : Program}
    {state : AllocationState} {rest : ActivationStack}
    {current : ActivationId} {frames : EvalStack} {object : ObjectId}
    {declaration : NestedCacheId} {expression : CoreExpr}
    {after : SequentialConfig} :
    PrologEvaluateNestedClassMiss p state rest current frames object declaration
      expression after ↔
      p.evaluateNestedClassMiss state rest current frames object declaration
        expression = some after := by
  constructor
  · intro derivation
    cases derivation with
    | classBody descriptor =>
        simp [Program.evaluateNestedClassMiss, descriptor]
    | mixinApply => rfl
  · intro equality
    cases expression <;> simp [Program.evaluateNestedClassMiss] at equality
    case classBody classDeclaration superclassExpression =>
      cases descriptorResult : p.classBodies classDeclaration with
      | none => simp [descriptorResult] at equality
      | some descriptor =>
          simp [descriptorResult] at equality
          subst after
          exact .classBody descriptorResult
    case mixinApply classDeclaration superclassExpression mixinExpression =>
      subst after
      exact .mixinApply

/-- The four object-literal clauses as written in the LaTeX and Prolog.
    Commit has no global post-allocation proof premise. -/
inductive PrologObjectLiteralStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | superclass {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {declaration : ObjectLiteralDeclId} {superclassExpression : CoreExpr}
      {descriptor : ObjectLiteralDescriptor} {enclosingObject : ObjRef} :
      p.objectLiterals declaration = some descriptor →
      PrologObjectLiteralEnclosingObject p state.heap current
        (some enclosingObject) →
      PrologObjectLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.objectLiteral declaration superclassExpression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.makeObjectLiteral descriptor enclosingObject)⟩,
          .evaluate superclassExpression⟩
  | commit {state next : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ObjectLiteralDescriptor} {enclosingObject : ObjRef}
      {superclass : ClassId} {mixin : MixinDef} {classId metaclassId : ClassId} :
      PrologInheritanceError state.heap (.classObject superclass)
        descriptor.superclassMessage none →
      PrologValidTopSuperclass p enclosingObject descriptor.superclassSyntax
        superclass true →
      p.mixins descriptor.instanceMixin = some mixin →
      mixin.initializerDeclaration = descriptor.initializerDeclaration →
      mixin.initializerParameters = [] →
      PrologAllocateClassPair p state
        (.expression (.objectLiteral descriptor.declaration))
        descriptor.instanceMixin descriptor.classMixin superclass
        enclosingObject (Program.objectLiteralFactory descriptor mixin)
        next classId metaclassId →
      PrologObjectLiteralStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeObjectLiteral descriptor enclosingObject)⟩,
          .object (.classObject superclass)⟩
        ⟨next, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary (.classObject classId))
            (Program.objectLiteralNewMessage mixin)⟩
  | inheritanceError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ObjectLiteralDescriptor} {enclosingObject value : ObjRef}
      {error : RuntimeError} :
      PrologInheritanceError state.heap value descriptor.superclassMessage
        (some error) →
      PrologObjectLiteralStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeObjectLiteral descriptor enclosingObject)⟩,
          .object value⟩
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
  | topSuperclassError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {descriptor : ObjectLiteralDescriptor} {superclass : ClassId} :
      PrologInheritanceError state.heap (.classObject superclass)
        descriptor.superclassMessage none →
      PrologValidTopSuperclass p p.nilObject descriptor.superclassSyntax
        superclass false →
      PrologObjectLiteralStep p
        ⟨state, .push rest ⟨current,
          .push frames (.makeObjectLiteral descriptor p.nilObject)⟩,
          .object (.classObject superclass)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .runtimeError .topSuperclass⟩

def PrologObjectLiteralCommitSafe (p : Program)
    (before after : SequentialConfig) : Prop :=
  before.allocation = after.allocation ∨ p.WellFormed after.allocation.heap

theorem prologObjectLiteralStep_iff {p : Program}
    {before after : SequentialConfig} :
    (PrologObjectLiteralStep p before after ∧
      PrologObjectLiteralCommitSafe p before after) ↔
      p.ObjectLiteralStep before after := by
  constructor
  · rintro ⟨derivation, safe⟩
    cases derivation with
    | superclass descriptor enclosing =>
        exact .superclass descriptor
          (prologObjectLiteralEnclosingObject_iff.mp enclosing)
    | commit inheritance topValid mixin declaration nullary allocated =>
        simp only [PrologObjectLiteralCommitSafe] at safe
        rcases safe with same | allocationWellFormed
        · subst_vars
          have allocatedEq := prologAllocateClassPair_iff.mp allocated
          have impossible := congrArg (fun result => result.1.nextClass)
            allocatedEq
          simp [Program.allocateClassPair] at impossible
        · exact .commit (prologInheritanceError_iff.mp inheritance)
            (prologValidTopSuperclass_iff.mp topValid) mixin declaration nullary
            (prologAllocateClassPair_iff.mp allocated).symm allocationWellFormed
    | inheritanceError invalid =>
        exact .inheritanceError (prologInheritanceError_iff.mp invalid)
    | topSuperclassError inheritance topInvalid =>
        exact .topSuperclassError (prologInheritanceError_iff.mp inheritance)
          (prologValidTopSuperclass_iff.mp topInvalid)
  · intro derivation
    cases derivation with
    | superclass descriptor enclosing =>
        exact ⟨.superclass descriptor
          (prologObjectLiteralEnclosingObject_iff.mpr enclosing), .inl rfl⟩
    | commit inheritance topValid mixin declaration nullary allocated
        allocationWellFormed =>
        refine ⟨?_, .inr allocationWellFormed⟩
        exact .commit (prologInheritanceError_iff.mpr inheritance)
          (prologValidTopSuperclass_iff.mpr topValid) mixin declaration nullary
          (prologAllocateClassPair_iff.mpr allocated.symm)
    | inheritanceError invalid =>
        exact ⟨.inheritanceError (prologInheritanceError_iff.mpr invalid),
          .inl rfl⟩
    | topSuperclassError inheritance topInvalid =>
        exact ⟨.topSuperclassError
          (prologInheritanceError_iff.mpr inheritance)
          (prologValidTopSuperclass_iff.mpr topInvalid), .inl rfl⟩

inductive PrologNestedClassStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | hit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {activation : ActivationDef} {object : ObjectId}
      {declaration : ClassDeclId} {application : ClassId} {classExpression : CoreExpr}
      {classId : ClassId} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .ordinaryObject object →
      activation.currentClass = some application →
      PrologReadNestedClass state.heap object ⟨application, declaration⟩ (some classId) →
      PrologNestedClassStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.nestedClass declaration classExpression)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .object (.classObject classId)⟩
  | miss {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {activation : ActivationDef} {object : ObjectId}
      {declaration : ClassDeclId} {application : ClassId} {classExpression : CoreExpr}
      {after : SequentialConfig} :
      state.heap.activations current = some activation →
      activation.currentReceiver = .ordinaryObject object →
      activation.currentClass = some application →
      PrologReadNestedClass state.heap object ⟨application, declaration⟩ none →
      PrologEvaluateNestedClassMiss p state rest current frames object ⟨application, declaration⟩
        classExpression after →
      PrologNestedClassStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.nestedClass declaration classExpression)⟩ after
  | store {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {declaration : NestedCacheId} {classId : ClassId} {heap : Heap} :
      PrologWriteNestedClass state.heap object declaration classId heap →
      PrologNestedClassStep p
        ⟨state, .push rest ⟨current,
          .push frames (.nestedClassStore object declaration)⟩,
          .object (.classObject classId)⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .object (.classObject classId)⟩

theorem prologNestedClassStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologNestedClassStep p before after ↔ p.NestedClassStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | hit activation receiver selectedClass cached =>
        exact .hit activation receiver selectedClass (prologReadNestedClass_iff.mp cached)
    | miss activation receiver selectedClass absent next =>
        exact .miss activation receiver selectedClass (prologReadNestedClass_iff.mp absent)
          (prologEvaluateNestedClassMiss_iff.mp next)
    | store written =>
        exact .store (prologWriteNestedClass_iff.mp written)
  · intro derivation
    cases derivation with
    | hit activation receiver selectedClass cached =>
        exact .hit activation receiver selectedClass (prologReadNestedClass_iff.mpr cached)
    | miss activation receiver selectedClass absent next =>
        exact .miss activation receiver selectedClass (prologReadNestedClass_iff.mpr absent)
          (prologEvaluateNestedClassMiss_iff.mpr next)
    | store written =>
        exact .store (prologWriteNestedClass_iff.mpr written)

inductive PrologObjectAndNestedClassStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | objectLiteral {before after : SequentialConfig} :
      PrologObjectLiteralStep p before after →
      PrologObjectAndNestedClassStep p before after
  | nestedClass {before after : SequentialConfig} :
      PrologNestedClassStep p before after →
      PrologObjectAndNestedClassStep p before after

def PrologObjectAndNestedClassSafe (p : Program)
    (before after : SequentialConfig) : Prop :=
  PrologObjectLiteralStep p before after →
    PrologObjectLiteralCommitSafe p before after

theorem prologObjectAndNestedClassStep_iff {p : Program}
    {before after : SequentialConfig} :
    (PrologObjectAndNestedClassStep p before after ∧
      PrologObjectAndNestedClassSafe p before after) ↔
      p.ObjectAndNestedClassStep before after := by
  constructor
  · rintro ⟨derivation, safe⟩
    cases derivation with
    | objectLiteral object =>
        exact .objectLiteral (prologObjectLiteralStep_iff.mp ⟨object, safe object⟩)
    | nestedClass nested =>
        exact .nestedClass (prologNestedClassStep_iff.mp nested)
  · intro derivation
    cases derivation with
    | objectLiteral object =>
        rcases prologObjectLiteralStep_iff.mpr object with ⟨step, safe⟩
        exact ⟨.objectLiteral step, fun _ => safe⟩
    | nestedClass nested =>
        constructor
        · exact PrologObjectAndNestedClassStep.nestedClass
            (prologNestedClassStep_iff.mpr nested)
        · intro object
          cases nested <;> cases object

/-! ## Explicit sequential unions -/

inductive PrologSequentialStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | expression {before after : SequentialConfig} :
      PrologExpressionOrderStep p before after →
      PrologSequentialStep p before after
  | request {before after : SequentialConfig} :
      PrologRequestCompletionStep p before after →
      PrologSequentialStep p before after
  | invocation {before after : SequentialConfig} :
      PrologMethodInvocationStep p before after →
      PrologSequentialStep p before after
  | body {before after : SequentialConfig} :
      PrologBodyMachineStep p before after →
      PrologSequentialStep p before after
  | returns {before after : SequentialConfig} :
      PrologReturnMachineStep p before after →
      PrologSequentialStep p before after
  | closure {before after : SequentialConfig} :
      PrologClosureMachineStep p before after →
      PrologSequentialStep p before after
  | objectSlots {before after : SequentialConfig} :
      PrologObjectSlotStep p before after →
      PrologSequentialStep p before after
  | classes {before after : SequentialConfig} :
      PrologClassConstructionStep p before after →
      PrologSequentialStep p before after
  | messages {before after : SequentialConfig} :
      PrologMessageEvaluationStep p before after →
      PrologSequentialStep p before after

/-- The checked Horn union plus precisely the class-allocation certificate
    still stored in Lean's operational constructor. -/
inductive PrologSequentialStepAdmissible (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | expression {before after : SequentialConfig} :
      PrologExpressionOrderStep p before after →
      PrologSequentialStepAdmissible p before after
  | request {before after : SequentialConfig} :
      PrologRequestCompletionStep p before after →
      PrologSequentialStepAdmissible p before after
  | invocation {before after : SequentialConfig} :
      PrologMethodInvocationStep p before after →
      PrologSequentialStepAdmissible p before after
  | body {before after : SequentialConfig} :
      PrologBodyMachineStep p before after →
      PrologSequentialStepAdmissible p before after
  | returns {before after : SequentialConfig} :
      PrologReturnMachineStep p before after →
      PrologSequentialStepAdmissible p before after
  | closure {before after : SequentialConfig} :
      PrologClosureMachineStep p before after →
      PrologSequentialStepAdmissible p before after
  | objectSlots {before after : SequentialConfig} :
      PrologObjectSlotStep p before after →
      PrologSequentialStepAdmissible p before after
  | classes {before after : SequentialConfig} :
      PrologClassConstructionStep p before after →
      PrologClassConstructionCommitSafe p before after →
      PrologSequentialStepAdmissible p before after
  | messages {before after : SequentialConfig} :
      PrologMessageEvaluationStep p before after →
      PrologSequentialStepAdmissible p before after

theorem PrologSequentialStepAdmissible.raw {p : Program}
    {before after : SequentialConfig}
    (step : PrologSequentialStepAdmissible p before after) :
    PrologSequentialStep p before after := by
  cases step with
  | expression expression => exact .expression expression
  | request request => exact .request request
  | invocation invocation => exact .invocation invocation
  | body body => exact .body body
  | returns returns => exact .returns returns
  | closure closure => exact .closure closure
  | objectSlots slots => exact .objectSlots slots
  | classes classes safe => exact .classes classes
  | messages messages => exact .messages messages

theorem prologSequentialStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologSequentialStepAdmissible p before after ↔
      p.SequentialStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | expression expression =>
        exact .expression (prologExpressionOrderStep_iff.mp expression)
    | request request =>
        exact .request (prologRequestCompletionStep_iff.mp request)
    | invocation invocation =>
        exact .invocation (prologMethodInvocationStep_iff.mp invocation)
    | body body => exact .body (prologBodyMachineStep_iff.mp body)
    | returns returns => exact .returns (prologReturnMachineStep_iff.mp returns)
    | closure closure => exact .closure (prologClosureMachineStep_iff.mp closure)
    | objectSlots slots => exact .objectSlots (prologObjectSlotStep_iff.mp slots)
    | classes classes safe =>
        exact .classes (prologClassConstructionStep_iff.mp ⟨classes, safe⟩)
    | messages messages =>
        exact .messages (prologMessageEvaluationStep_iff.mp messages)
  · intro derivation
    cases derivation with
    | expression expression =>
        exact .expression (prologExpressionOrderStep_iff.mpr expression)
    | request request =>
        exact .request (prologRequestCompletionStep_iff.mpr request)
    | invocation invocation =>
        exact .invocation (prologMethodInvocationStep_iff.mpr invocation)
    | body body => exact .body (prologBodyMachineStep_iff.mpr body)
    | returns returns => exact .returns (prologReturnMachineStep_iff.mpr returns)
    | closure closure => exact .closure (prologClosureMachineStep_iff.mpr closure)
    | objectSlots slots => exact .objectSlots (prologObjectSlotStep_iff.mpr slots)
    | classes classes =>
        rcases prologClassConstructionStep_iff.mpr classes with ⟨step, safe⟩
        exact .classes step safe
    | messages messages =>
        exact .messages (prologMessageEvaluationStep_iff.mpr messages)

inductive PrologSequentialStepWithInitialization (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStep p before after →
      PrologSequentialStepWithInitialization p before after
  | initialization {before after : SequentialConfig} :
      PrologInstanceInitializationStep p before after →
      PrologSequentialStepWithInitialization p before after

inductive PrologSequentialStepWithInitializationAdmissible (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepAdmissible p before after →
      PrologSequentialStepWithInitializationAdmissible p before after
  | initialization {before after : SequentialConfig} :
      PrologInstanceInitializationStep p before after →
      PrologSequentialStepWithInitializationAdmissible p before after

theorem PrologSequentialStepWithInitializationAdmissible.raw {p : Program}
    {before after : SequentialConfig}
    (step : PrologSequentialStepWithInitializationAdmissible p before after) :
    PrologSequentialStepWithInitialization p before after := by
  cases step with
  | prior prior => exact .prior prior.raw
  | initialization initialization => exact .initialization initialization

theorem prologSequentialStepWithInitialization_iff {p : Program}
    {before after : SequentialConfig} :
    PrologSequentialStepWithInitializationAdmissible p before after ↔
      p.SequentialStepWithInitialization before after := by
  constructor
  · intro derivation
    cases derivation with
    | prior prior => exact .prior (prologSequentialStep_iff.mp prior)
    | initialization initialization =>
        exact .initialization
          (prologInstanceInitializationStep_iff.mp initialization)
  · intro derivation
    cases derivation with
    | prior prior => exact .prior (prologSequentialStep_iff.mpr prior)
    | initialization initialization =>
        exact .initialization
          (prologInstanceInitializationStep_iff.mpr initialization)

inductive PrologSequentialStepWithObjects (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithInitialization p before after →
      PrologSequentialStepWithObjects p before after
  | objects {before after : SequentialConfig} :
      PrologObjectAndNestedClassStep p before after →
      PrologSequentialStepWithObjects p before after

inductive PrologSequentialStepWithObjectsAdmissible (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithInitializationAdmissible p before after →
      PrologSequentialStepWithObjectsAdmissible p before after
  | objects {before after : SequentialConfig} :
      PrologObjectAndNestedClassStep p before after →
      PrologObjectAndNestedClassSafe p before after →
      PrologSequentialStepWithObjectsAdmissible p before after

theorem PrologSequentialStepWithObjectsAdmissible.raw {p : Program}
    {before after : SequentialConfig}
    (step : PrologSequentialStepWithObjectsAdmissible p before after) :
    PrologSequentialStepWithObjects p before after := by
  cases step with
  | prior prior => exact .prior prior.raw
  | objects objects safe => exact .objects objects

theorem prologSequentialStepWithObjects_iff {p : Program}
    {before after : SequentialConfig} :
    PrologSequentialStepWithObjectsAdmissible p before after ↔
      p.SequentialStepWithObjects before after := by
  constructor
  · intro derivation
    cases derivation with
    | prior prior =>
        exact .prior (prologSequentialStepWithInitialization_iff.mp prior)
    | objects objects safe =>
        exact .objects (prologObjectAndNestedClassStep_iff.mp ⟨objects, safe⟩)
  · intro derivation
    cases derivation with
    | prior prior =>
        exact .prior (prologSequentialStepWithInitialization_iff.mpr prior)
    | objects objects =>
        rcases prologObjectAndNestedClassStep_iff.mpr objects with ⟨step, safe⟩
        exact .objects step safe

inductive PrologErrorReification {p : Program} (reifier : ErrorReifier p)
    (state : AllocationState) (error : RuntimeError) :
    AllocationState → ObjRef → Prop where
  | application :
      PrologErrorReification reifier state error
        (reifier.reify state error).1 (reifier.reify state error).2

theorem prologErrorReification_iff {p : Program} {reifier : ErrorReifier p}
    {state next : AllocationState} {error : RuntimeError}
    {exception : ObjRef} :
    PrologErrorReification reifier state error next exception ↔
      reifier.reify state error = (next, exception) := by
  constructor
  · intro derivation
    cases derivation
    exact Prod.ext rfl rfl
  · intro equality
    have nextEqual := congrArg Prod.fst equality
    have exceptionEqual := congrArg Prod.snd equality
    simp only at nextEqual exceptionEqual
    subst next
    subst exception
    exact .application

inductive PrologExceptionBoundaryStep (p : Program) (reifier : ErrorReifier p) :
    SequentialConfig → SequentialConfig → Prop where
  | runtimeError {state next : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {error : RuntimeError}
      {exception : ObjRef} :
      PrologErrorReification reifier state error next exception →
      PrologExceptionBoundaryStep p reifier
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
        ⟨next, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary exception) signalMessage⟩
  | thrown {state next : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {error : RuntimeError}
      {exception : ObjRef} :
      PrologErrorReification reifier state error next exception →
      PrologExceptionBoundaryStep p reifier
        ⟨state, .push rest ⟨current, frames⟩, .throw error⟩
        ⟨next, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary exception) signalMessage⟩

theorem prologExceptionBoundaryStep_iff {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig} :
    PrologExceptionBoundaryStep p reifier before after ↔
      p.ExceptionBoundaryStep reifier before after := by
  constructor
  · intro derivation
    cases derivation with
    | runtimeError reification =>
        have result := prologErrorReification_iff.mp reification
        have nextEqual := congrArg Prod.fst result
        have exceptionEqual := congrArg Prod.snd result
        simp only at nextEqual exceptionEqual
        subst_vars
        exact .runtimeError
    | thrown reification =>
        have result := prologErrorReification_iff.mp reification
        have nextEqual := congrArg Prod.fst result
        have exceptionEqual := congrArg Prod.snd result
        simp only at nextEqual exceptionEqual
        subst_vars
        exact .thrown
  · intro derivation
    cases derivation with
    | runtimeError => exact .runtimeError .application
    | thrown => exact .thrown .application

inductive PrologSequentialStepWithExceptions (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithObjects p before after →
      PrologSequentialStepWithExceptions p reifier before after
  | exception {before after : SequentialConfig} :
      PrologExceptionBoundaryStep p reifier before after →
      PrologSequentialStepWithExceptions p reifier before after

inductive PrologSequentialStepWithExceptionsAdmissible (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithObjectsAdmissible p before after →
      PrologSequentialStepWithExceptionsAdmissible p reifier before after
  | exception {before after : SequentialConfig} :
      PrologExceptionBoundaryStep p reifier before after →
      PrologSequentialStepWithExceptionsAdmissible p reifier before after

theorem PrologSequentialStepWithExceptionsAdmissible.raw {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (step : PrologSequentialStepWithExceptionsAdmissible p reifier before after) :
    PrologSequentialStepWithExceptions p reifier before after := by
  cases step with
  | prior prior => exact .prior prior.raw
  | exception exception => exact .exception exception

theorem prologSequentialStepWithExceptions_iff {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig} :
    PrologSequentialStepWithExceptionsAdmissible p reifier before after ↔
      p.SequentialStepWithExceptions reifier before after := by
  constructor
  · intro derivation
    cases derivation with
    | prior prior => exact .prior (prologSequentialStepWithObjects_iff.mp prior)
    | exception exception =>
        exact .exception (prologExceptionBoundaryStep_iff.mp exception)
  · intro derivation
    cases derivation with
    | prior prior => exact .prior (prologSequentialStepWithObjects_iff.mpr prior)
    | exception exception =>
        exact .exception (prologExceptionBoundaryStep_iff.mpr exception)

/-! ## Compound literals -/

inductive PrologTuplePutClauses : Nat → List CoreExpr →
    List (Selector × List CoreExpr) → Prop where
  | nil {index : Nat} :
      PrologTuplePutClauses index [] [(tupleYourselfSelector, [])]
  | cons {index : Nat} {expression : CoreExpr} {remaining : List CoreExpr}
      {clauses : List (Selector × List CoreExpr)} :
      PrologTuplePutClauses (index + 1) remaining clauses →
      PrologTuplePutClauses index (expression :: remaining)
        ((tupleAtPutSelector, [naturalAtom index, expression]) :: clauses)

theorem prologTuplePutClauses_iff {index : Nat} {elements : List CoreExpr}
    {clauses : List (Selector × List CoreExpr)} :
    PrologTuplePutClauses index elements clauses ↔
      tuplePutClauses index elements = clauses := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons _ ih => simp [tuplePutClauses, ih]
  · intro equality
    induction elements generalizing index clauses with
    | nil =>
        simp [tuplePutClauses] at equality
        subst clauses
        exact .nil
    | cons expression remaining ih =>
        simp [tuplePutClauses] at equality
        subst clauses
        exact .cons (ih rfl)

inductive PrologTupleExpansion (p : Program) (site : SiteId)
    (descriptor : CascadeDescriptor) : List CoreExpr → CoreExpr → Prop where
  | empty {readOnlyTuple : ObjRef} :
      p.platform .readOnlyTuple = some readOnlyTuple →
      PrologTupleExpansion p site descriptor []
        (.ordinarySend (.value readOnlyTuple) tupleNewSelector [naturalAtom 0])
  | nonempty {first : CoreExpr} {remaining : List CoreExpr}
      {readOnlyTuple array : ObjRef}
      {clauses : List (Selector × List CoreExpr)} :
      p.platform .readOnlyTuple = some readOnlyTuple →
      p.platform .array = some array →
      PrologTuplePutClauses 1 (first :: remaining) clauses →
      PrologTupleExpansion p site descriptor (first :: remaining)
        (.ordinarySend (.value readOnlyTuple) tupleFromArraySelector
          [.cascade descriptor
            (.ordinarySend (.value array) tupleNewSelector
              [naturalAtom (first :: remaining).length]) clauses])

theorem prologTupleExpansion_iff {p : Program} {site : SiteId}
    {descriptor : CascadeDescriptor} {elements : List CoreExpr}
    {expansion : CoreExpr} :
    PrologTupleExpansion p site descriptor elements expansion ↔
      p.tupleExpansion site descriptor elements = some expansion := by
  constructor
  · intro derivation
    cases derivation with
    | empty tupleFound =>
        simp [Program.tupleExpansion, tupleFound]
    | nonempty tupleFound arrayFound clauses =>
        simp [Program.tupleExpansion, tupleFound, arrayFound,
          prologTuplePutClauses_iff.mp clauses]
  · intro equality
    cases elements with
    | nil =>
        cases tupleResult : p.platform .readOnlyTuple with
        | none => simp [Program.tupleExpansion, tupleResult] at equality
        | some readOnlyTuple =>
            simp [Program.tupleExpansion, tupleResult] at equality
            subst expansion
            exact .empty tupleResult
    | cons first remaining =>
        cases tupleResult : p.platform .readOnlyTuple with
        | none => simp [Program.tupleExpansion, tupleResult] at equality
        | some readOnlyTuple =>
            cases arrayResult : p.platform .array with
            | none =>
                simp [Program.tupleExpansion, tupleResult, arrayResult] at equality
            | some array =>
                simp [Program.tupleExpansion, tupleResult, arrayResult] at equality
                subst expansion
                exact .nonempty tupleResult arrayResult
                  (prologTuplePutClauses_iff.mpr rfl)

inductive PrologCascadeExpansion (descriptor : CascadeDescriptor)
    (receiver : CoreExpr) (clauses : List (Selector × List CoreExpr)) :
    CoreExpr → Prop where
  | application : PrologCascadeExpansion descriptor receiver clauses
      (.ordinarySend (.cascadeClosure descriptor clauses) (valueSelector 1)
        [receiver])

theorem prologCascadeExpansion_iff {descriptor : CascadeDescriptor}
    {receiver : CoreExpr} {clauses : List (Selector × List CoreExpr)}
    {expansion : CoreExpr} :
    PrologCascadeExpansion descriptor receiver clauses expansion ↔
      Program.cascadeExpansion descriptor receiver clauses = expansion := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

def patternKeywordAtoms (pairs : List (Selector × CorePattern)) :
    List CoreExpr :=
  pairs.map fun pair => .atom (.symbol pair.1.spelling)

inductive PrologPatternKeywordAtoms : List (Selector × CorePattern) →
    List CoreExpr → Prop where
  | nil : PrologPatternKeywordAtoms [] []
  | cons {selector : Selector} {pattern : CorePattern}
      {remaining : List (Selector × CorePattern)} {atoms : List CoreExpr} :
      PrologPatternKeywordAtoms remaining atoms →
      PrologPatternKeywordAtoms ((selector, pattern) :: remaining)
        (.atom (.symbol selector.spelling) :: atoms)

theorem prologPatternKeywordAtoms_iff
    {pairs : List (Selector × CorePattern)} {atoms : List CoreExpr} :
    PrologPatternKeywordAtoms pairs atoms ↔ patternKeywordAtoms pairs = atoms := by
  constructor
  · intro derivation
    induction derivation with
    | nil => rfl
    | @cons selector pattern remaining atoms _ ih =>
        change .atom (.symbol selector.spelling) ::
          patternKeywordAtoms remaining =
            .atom (.symbol selector.spelling) :: atoms
        simp [ih]
  · intro equality
    induction pairs generalizing atoms with
    | nil =>
        simp [patternKeywordAtoms] at equality
        subst atoms
        exact .nil
    | cons pair remaining ih =>
        rcases pair with ⟨selector, pattern⟩
        simp [patternKeywordAtoms] at equality
        subst atoms
        exact .cons (ih rfl)

mutual
  inductive PrologPatternExpansion (p : Program)
      (annotation : Option ScopeDecl) (immediate : Option ClassDeclId) :
      CorePattern → CoreExpr → Prop where
    | wildcard : PrologPatternExpansion p annotation immediate .wildcard
        (.ordinarySend
          (.implicitSend patternBindingSelector [] annotation immediate)
          patternWildcardSelector [])
    | literal {expression : CoreExpr} :
        PrologPatternExpansion p annotation immediate (.literal expression)
          (.ordinarySend
            (.implicitSend patternBindingSelector [] annotation immediate)
            patternLiteralSelector [expression])
    | variable {site : SiteId} {expression : CoreExpr} :
        p.patternVariable site = some expression →
        PrologPatternExpansion p annotation immediate (.variable site) expression
    | nested {pattern : CorePattern} :
        PrologPatternExpansion p annotation immediate (.nested pattern)
          (.pattern pattern annotation immediate)
    | keyword {keywordTupleSite : SiteId}
        {keywordTupleCascade : CascadeDescriptor}
        {componentTupleSite : SiteId}
        {componentTupleCascade : CascadeDescriptor}
        {pairs : List (Selector × CorePattern)}
        {components keywords : List CoreExpr} :
        PrologPatternComponentExpansions p annotation immediate pairs components →
        PrologPatternKeywordAtoms pairs keywords →
        PrologPatternExpansion p annotation immediate
          (.keyword keywordTupleSite keywordTupleCascade componentTupleSite
            componentTupleCascade pairs)
          (.ordinarySend
            (.implicitSend patternBindingSelector [] annotation immediate)
            patternKeywordsSelector
            [.tuple keywordTupleSite keywordTupleCascade keywords,
             .tuple componentTupleSite componentTupleCascade components])

  inductive PrologPatternComponentExpansions (p : Program)
      (annotation : Option ScopeDecl) (immediate : Option ClassDeclId) :
      List (Selector × CorePattern) → List CoreExpr → Prop where
    | nil : PrologPatternComponentExpansions p annotation immediate [] []
    | cons {selector : Selector} {pattern : CorePattern}
        {remaining : List (Selector × CorePattern)}
        {first : CoreExpr} {rest : List CoreExpr} :
        PrologPatternExpansion p annotation immediate pattern first →
        PrologPatternComponentExpansions p annotation immediate remaining rest →
        PrologPatternComponentExpansions p annotation immediate
          ((selector, pattern) :: remaining) (first :: rest)
end

mutual
  theorem prologPatternExpansion_sound {p : Program}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {pattern : CorePattern} {expansion : CoreExpr}
      (derivation : PrologPatternExpansion p annotation immediate pattern expansion) :
      p.patternExpansion annotation immediate pattern = some expansion := by
    cases derivation with
    | wildcard => rfl
    | literal => rfl
    | «variable» found => exact found
    | nested => rfl
    | @keyword keywordTupleSite keywordTupleCascade componentTupleSite
        componentTupleCascade pairs components keywords componentsDerivation
        keywordsDerivation =>
        have keywordsEqual :
            pairs.map (fun pair => CoreExpr.atom (.symbol pair.1.spelling)) =
              keywords := by
          simpa [patternKeywordAtoms] using
            (prologPatternKeywordAtoms_iff.mp keywordsDerivation)
        simp [Program.patternExpansion,
          prologPatternComponents_sound componentsDerivation,
          keywordsEqual]

  theorem prologPatternComponents_sound {p : Program}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {pairs : List (Selector × CorePattern)} {components : List CoreExpr}
      (derivation :
        PrologPatternComponentExpansions p annotation immediate pairs components) :
      p.patternComponentExpansions annotation immediate pairs = some components := by
    cases derivation with
    | nil => rfl
    | cons first rest =>
        simp [Program.patternComponentExpansions,
          prologPatternExpansion_sound first,
          prologPatternComponents_sound rest]
end

mutual
  theorem prologPatternExpansion_complete {p : Program}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {pattern : CorePattern} {expansion : CoreExpr}
      (equality :
        p.patternExpansion annotation immediate pattern = some expansion) :
      PrologPatternExpansion p annotation immediate pattern expansion := by
    cases pattern with
    | wildcard =>
        simp [Program.patternExpansion] at equality
        subst expansion
        exact .wildcard
    | literal expression =>
        simp [Program.patternExpansion] at equality
        subst expansion
        exact .literal
    | «variable» site => exact .variable equality
    | nested pattern =>
        simp [Program.patternExpansion] at equality
        subst expansion
        exact .nested
    | keyword keywordTupleSite keywordTupleCascade componentTupleSite
        componentTupleCascade pairs =>
        cases componentsResult :
            p.patternComponentExpansions annotation immediate pairs with
        | none =>
            simp [Program.patternExpansion, componentsResult] at equality
        | some components =>
            simp [Program.patternExpansion, componentsResult] at equality
            subst expansion
            exact .keyword
              (prologPatternComponents_complete componentsResult)
              (prologPatternKeywordAtoms_iff.mpr rfl)

  theorem prologPatternComponents_complete {p : Program}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {pairs : List (Selector × CorePattern)} {components : List CoreExpr}
      (equality :
        p.patternComponentExpansions annotation immediate pairs =
          some components) :
      PrologPatternComponentExpansions p annotation immediate pairs components := by
    cases pairs with
    | nil =>
        simp [Program.patternComponentExpansions] at equality
        subst components
        exact .nil
    | cons pair remaining =>
        rcases pair with ⟨selector, pattern⟩
        cases firstResult : p.patternExpansion annotation immediate pattern with
        | none =>
            simp [Program.patternComponentExpansions, firstResult] at equality
        | some first =>
            cases restResult :
                p.patternComponentExpansions annotation immediate remaining with
            | none =>
                simp [Program.patternComponentExpansions, firstResult,
                  restResult] at equality
            | some rest =>
                simp [Program.patternComponentExpansions, firstResult,
                  restResult] at equality
                subst components
                exact .cons
                  (prologPatternExpansion_complete firstResult)
                  (prologPatternComponents_complete restResult)
end

theorem prologPatternExpansion_iff {p : Program}
    {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
    {pattern : CorePattern} {expansion : CoreExpr} :
    PrologPatternExpansion p annotation immediate pattern expansion ↔
      p.patternExpansion annotation immediate pattern = some expansion :=
  ⟨prologPatternExpansion_sound, prologPatternExpansion_complete⟩

theorem prologPatternComponentExpansions_iff {p : Program}
    {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
    {pairs : List (Selector × CorePattern)} {components : List CoreExpr} :
    PrologPatternComponentExpansions p annotation immediate pairs components ↔
      p.patternComponentExpansions annotation immediate pairs = some components :=
  ⟨prologPatternComponents_sound, prologPatternComponents_complete⟩

inductive PrologCompoundLiteralStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | tuple {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {site : SiteId}
      {descriptor : CascadeDescriptor} {elements : List CoreExpr}
      {expansion : CoreExpr} :
      PrologTupleExpansion p site descriptor elements expansion →
      PrologCompoundLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.tuple site descriptor elements)⟩
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expansion⟩
  | cascade {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack}
      {receiver : CoreExpr} {clauses : List (Selector × List CoreExpr)}
      {descriptor : CascadeDescriptor} {expansion : CoreExpr} :
      PrologCascadeExpansion descriptor receiver clauses expansion →
      PrologCompoundLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.cascade descriptor receiver clauses)⟩
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expansion⟩
  | pattern {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {value : CorePattern}
      {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {expansion : CoreExpr} :
      PrologPatternExpansion p annotation immediate value expansion →
      PrologCompoundLiteralStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.pattern value annotation immediate)⟩
        ⟨state, .push rest ⟨current, frames⟩, .evaluate expansion⟩

theorem prologCompoundLiteralStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologCompoundLiteralStep p before after ↔
      p.CompoundLiteralStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | tuple expanded => exact .tuple (prologTupleExpansion_iff.mp expanded)
    | cascade expanded =>
        have equality := prologCascadeExpansion_iff.mp expanded
        subst_vars
        exact .cascade
    | pattern expanded =>
        exact .pattern (prologPatternExpansion_iff.mp expanded)
  · intro derivation
    cases derivation with
    | tuple expanded => exact .tuple (prologTupleExpansion_iff.mpr expanded)
    | cascade => exact .cascade .application
    | pattern expanded =>
        exact .pattern (prologPatternExpansion_iff.mpr expanded)

inductive PrologSequentialStepWithLiterals (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithExceptions p reifier before after →
      PrologSequentialStepWithLiterals p reifier before after
  | compoundLiteral {before after : SequentialConfig} :
      PrologCompoundLiteralStep p before after →
      PrologSequentialStepWithLiterals p reifier before after

inductive PrologSequentialStepWithLiteralsAdmissible (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithExceptionsAdmissible p reifier before after →
      PrologSequentialStepWithLiteralsAdmissible p reifier before after
  | compoundLiteral {before after : SequentialConfig} :
      PrologCompoundLiteralStep p before after →
      PrologSequentialStepWithLiteralsAdmissible p reifier before after

theorem PrologSequentialStepWithLiteralsAdmissible.raw {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (step : PrologSequentialStepWithLiteralsAdmissible p reifier before after) :
    PrologSequentialStepWithLiterals p reifier before after := by
  cases step with
  | prior prior => exact .prior prior.raw
  | compoundLiteral literal => exact .compoundLiteral literal

theorem prologSequentialStepWithLiterals_iff {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig} :
    PrologSequentialStepWithLiteralsAdmissible p reifier before after ↔
      p.SequentialStepWithLiterals reifier before after := by
  constructor
  · intro derivation
    cases derivation with
    | prior prior =>
        exact .prior (prologSequentialStepWithExceptions_iff.mp prior)
    | compoundLiteral literal =>
        exact .compoundLiteral (prologCompoundLiteralStep_iff.mp literal)
  · intro derivation
    cases derivation with
    | prior prior =>
        exact .prior (prologSequentialStepWithExceptions_iff.mpr prior)
    | compoundLiteral literal =>
        exact .compoundLiteral (prologCompoundLiteralStep_iff.mpr literal)

/-! ## Top-level termination and the completed sequential relation -/

inductive PrologStopTopLevelActivation (state : AllocationState)
    (id : ActivationId) (activation : ActivationDef) : AllocationState → Prop where
  | application : PrologStopTopLevelActivation state id activation
      (Program.stopTopLevelActivation state id activation)

theorem prologStopTopLevelActivation_iff {state next : AllocationState}
    {id : ActivationId} {activation : ActivationDef} :
    PrologStopTopLevelActivation state id activation next ↔
      Program.stopTopLevelActivation state id activation = next := by
  constructor
  · intro derivation
    cases derivation
    rfl
  · intro equality
    rw [← equality]
    exact .application

inductive PrologTopLevelHaltStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | halt {state next : AllocationState} {current : ActivationId}
      {activation : ActivationDef} {value : ObjRef} :
      state.heap.activations current = some activation →
      activation.provenance = .top →
      PrologStopTopLevelActivation state current activation next →
      PrologTopLevelHaltStep p
        ⟨state, .push .empty ⟨current, .empty⟩, .object value⟩
        ⟨next, .empty, .halt value⟩

theorem prologTopLevelHaltStep_iff {p : Program}
    {before after : SequentialConfig} :
    PrologTopLevelHaltStep p before after ↔ p.TopLevelHaltStep before after := by
  constructor
  · intro derivation
    cases derivation with
    | halt live top stopped =>
        have equality := prologStopTopLevelActivation_iff.mp stopped
        subst_vars
        exact .halt live top
  · intro derivation
    cases derivation with
    | halt live top => exact .halt live top .application

inductive PrologSequentialStepWithTopLevel (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithLiterals p reifier before after →
      PrologSequentialStepWithTopLevel p reifier before after
  | topHalt {before after : SequentialConfig} :
      PrologTopLevelHaltStep p before after →
      PrologSequentialStepWithTopLevel p reifier before after

inductive PrologSequentialStepWithTopLevelAdmissible (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      PrologSequentialStepWithLiteralsAdmissible p reifier before after →
      PrologSequentialStepWithTopLevelAdmissible p reifier before after
  | topHalt {before after : SequentialConfig} :
      PrologTopLevelHaltStep p before after →
      PrologSequentialStepWithTopLevelAdmissible p reifier before after

theorem PrologSequentialStepWithTopLevelAdmissible.raw {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (step : PrologSequentialStepWithTopLevelAdmissible p reifier before after) :
    PrologSequentialStepWithTopLevel p reifier before after := by
  cases step with
  | prior prior => exact .prior prior.raw
  | topHalt halt => exact .topHalt halt

theorem prologSequentialStepWithTopLevel_iff {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig} :
    PrologSequentialStepWithTopLevelAdmissible p reifier before after ↔
      p.SequentialStepWithTopLevel reifier before after := by
  constructor
  · intro derivation
    cases derivation with
    | prior prior => exact .prior (prologSequentialStepWithLiterals_iff.mp prior)
    | topHalt halt => exact .topHalt (prologTopLevelHaltStep_iff.mp halt)
  · intro derivation
    cases derivation with
    | prior prior => exact .prior (prologSequentialStepWithLiterals_iff.mpr prior)
    | topHalt halt => exact .topHalt (prologTopLevelHaltStep_iff.mpr halt)

end PrologBridge
end Newspeak
