import Newspeak.LexicalBinding
import Newspeak.PrologLookupCorrespondence

/-! # Correspondence for static scope chains and lexical binding -/

namespace Newspeak
namespace PrologBridge

inductive PrologScopeChain (p : Program) (site : SiteId) :
    List ScopeDecl → Prop where
  | value : PrologScopeChain p site (p.scopeChain site)

theorem prologScopeChain_iff {p : Program} {site : SiteId}
    {scopes : List ScopeDecl} :
    PrologScopeChain p site scopes ↔ p.scopeChain site = scopes := by
  constructor
  · intro derivation; cases derivation; rfl
  · intro equality; rw [← equality]; exact .value

inductive PrologDeclares (p : Program) (declaration : ScopeDecl)
    (selector : Selector) : Bool → Prop where
  | value : PrologDeclares p declaration selector
      (p.declares declaration selector)

theorem prologDeclares_iff {p : Program} {declaration : ScopeDecl}
    {selector : Selector} {result : Bool} :
    PrologDeclares p declaration selector result ↔
      p.declares declaration selector = result := by
  constructor
  · intro derivation; cases derivation; rfl
  · intro equality; rw [← equality]; exact .value

inductive PrologBindIn (p : Program) (selector : Selector) :
    List ScopeDecl → Option ScopeDecl → Prop where
  | empty : PrologBindIn p selector [] none
  | hit {declaration : ScopeDecl} {rest : List ScopeDecl} :
      PrologDeclares p declaration selector true →
      PrologBindIn p selector (declaration :: rest) (some declaration)
  | skip {declaration : ScopeDecl} {rest : List ScopeDecl}
      {result : Option ScopeDecl} :
      PrologDeclares p declaration selector false →
      PrologBindIn p selector rest result →
      PrologBindIn p selector (declaration :: rest) result

theorem prologBindIn_computed (p : Program) (selector : Selector)
    (scopes : List ScopeDecl) :
    PrologBindIn p selector scopes (p.bindIn selector scopes) := by
  induction scopes with
  | nil => exact .empty
  | cons declaration rest ih =>
      cases declared : p.declares declaration selector with
      | false =>
          simpa [Program.bindIn, declared] using
            PrologBindIn.skip (prologDeclares_iff.mpr declared) ih
      | true =>
          simpa [Program.bindIn, declared] using
            (PrologBindIn.hit (rest := rest)
              (prologDeclares_iff.mpr declared))

theorem prologBindIn_iff {p : Program} {selector : Selector}
    {scopes : List ScopeDecl} {result : Option ScopeDecl} :
    PrologBindIn p selector scopes result ↔
      p.bindIn selector scopes = result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | hit declared =>
        simp [Program.bindIn, prologDeclares_iff.mp declared]
    | skip declared _ ih =>
        simp [Program.bindIn, prologDeclares_iff.mp declared, ih]
  · intro equality
    rw [← equality]
    exact prologBindIn_computed p selector scopes

inductive PrologLexicalBinding (p : Program) (site : SiteId)
    (selector : Selector) : Option ScopeDecl → Prop where
  | bind {scopes : List ScopeDecl} {result : Option ScopeDecl} :
      PrologScopeChain p site scopes →
      PrologBindIn p selector scopes result →
      PrologLexicalBinding p site selector result

theorem prologLexicalBinding_iff {p : Program} {site : SiteId}
    {selector : Selector} {result : Option ScopeDecl} :
    PrologLexicalBinding p site selector result ↔
      p.bind site selector = result := by
  constructor
  · intro derivation
    cases derivation with
    | bind chain binding =>
        unfold Program.bind
        rw [prologScopeChain_iff.mp chain]
        exact prologBindIn_iff.mp binding
  · intro equality
    exact .bind .value (prologBindIn_iff.mpr equality)

inductive PrologScanOnClassChain (p : Program) (selector : Selector) :
    List ClassDeclId → Option ClassDeclId → Prop where
  | empty : PrologScanOnClassChain p selector [] none
  | hit {declaration : ClassDeclId} {rest : List ClassDeclId} :
      PrologDeclares p (.classDecl declaration) selector true →
      PrologScanOnClassChain p selector (declaration :: rest)
        (some declaration)
  | skip {declaration : ClassDeclId} {rest : List ClassDeclId}
      {result : Option ClassDeclId} :
      PrologDeclares p (.classDecl declaration) selector false →
      PrologScanOnClassChain p selector rest result →
      PrologScanOnClassChain p selector (declaration :: rest) result

theorem prologScanOnClassChain_computed (p : Program) (selector : Selector)
    (chain : List ClassDeclId) :
    PrologScanOnClassChain p selector chain
      (p.scanOnClassChain selector chain) := by
  induction chain with
  | nil => exact .empty
  | cons declaration rest ih =>
      cases declared : p.declares (.classDecl declaration) selector with
      | false =>
          simpa [Program.scanOnClassChain, declared] using
            PrologScanOnClassChain.skip
              (prologDeclares_iff.mpr declared) ih
      | true =>
          simpa [Program.scanOnClassChain, declared] using
            (PrologScanOnClassChain.hit (rest := rest)
              (prologDeclares_iff.mpr declared))

theorem prologScanOnClassChain_iff {p : Program} {selector : Selector}
    {chain : List ClassDeclId} {result : Option ClassDeclId} :
    PrologScanOnClassChain p selector chain result ↔
      p.scanOnClassChain selector chain = result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | hit declared =>
        simp [Program.scanOnClassChain, prologDeclares_iff.mp declared]
    | skip declared _ ih =>
        simp [Program.scanOnClassChain, prologDeclares_iff.mp declared, ih]
  · intro equality
    rw [← equality]
    exact prologScanOnClassChain_computed p selector chain

inductive PrologClassScan (p : Program) (start : ClassDeclId)
    (selector : Selector) : Option ClassDeclId → Prop where
  | scan {chain : List ClassDeclId} {result : Option ClassDeclId} :
      PrologLexicalClassChain p start chain →
      PrologScanOnClassChain p selector chain result →
      PrologClassScan p start selector result

theorem prologClassScan_iff {p : Program} {start : ClassDeclId}
    {selector : Selector} {result : Option ClassDeclId} :
    PrologClassScan p start selector result ↔
      p.ClassScan start selector result := by
  constructor
  · intro derivation
    cases derivation with
    | scan lexical scanned =>
        exact ⟨_, prologLexicalClassChain_iff.mp lexical,
          prologScanOnClassChain_iff.mp scanned⟩
  · rintro ⟨chain, lexical, scanned⟩
    exact .scan (prologLexicalClassChain_iff.mpr lexical)
      (prologScanOnClassChain_iff.mpr scanned)

end PrologBridge
end Newspeak
