import Newspeak.LookupProofs

namespace Newspeak
namespace Program

/-- The U-Top/U-Here/U-Super rules from section 4. -/
inductive UnrestrictedLookupRules (p : Program) (h : Heap) (selector : Selector) :
    ClassId → Option LookupResult → Prop where
  | top : UnrestrictedLookupRules p h selector p.top none
  | here {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      UnrestrictedLookupRules p h selector c (some ⟨method, c⟩)
  | super {c parent : ClassId} {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      UnrestrictedLookupRules p h selector parent result →
      UnrestrictedLookupRules p h selector c result

/-- The Pub rules.  The two recursive constructors make the disjunction in
    Pub-Super explicit: absence and a private declaration are both
    transparent, while a protected declaration is a barrier. -/
inductive PublicLookupRules (p : Program) (h : Heap) (selector : Selector) :
    ClassId → Option LookupResult → Prop where
  | top : PublicLookupRules p h selector p.top none
  | hit {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .publicAccess →
      PublicLookupRules p h selector c (some ⟨method, c⟩)
  | protectedBarrier {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .protectedAccess →
      PublicLookupRules p h selector c none
  | superAbsent {c parent : ClassId} {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      PublicLookupRules p h selector parent result →
      PublicLookupRules p h selector c result
  | superPrivate {c parent : ClassId} {method : MethodDef}
      {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .privateAccess →
      p.superclass? h c = some parent →
      PublicLookupRules p h selector parent result →
      PublicLookupRules p h selector c result

/-- The Prot rules.  Public and protected declarations hit; private
    declarations remain transparent. -/
inductive ProtectedLookupRules (p : Program) (h : Heap) (selector : Selector) :
    ClassId → Option LookupResult → Prop where
  | top : ProtectedLookupRules p h selector p.top none
  | hitPublic {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .publicAccess →
      ProtectedLookupRules p h selector c (some ⟨method, c⟩)
  | hitProtected {c : ClassId} {method : MethodDef} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .protectedAccess →
      ProtectedLookupRules p h selector c (some ⟨method, c⟩)
  | superAbsent {c parent : ClassId} {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = none →
      p.superclass? h c = some parent →
      ProtectedLookupRules p h selector parent result →
      ProtectedLookupRules p h selector c result
  | superPrivate {c parent : ClassId} {method : MethodDef}
      {result : Option LookupResult} :
      c ≠ p.top →
      p.direct h c selector = some method →
      method.access = .privateAccess →
      p.superclass? h c = some parent →
      ProtectedLookupRules p h selector parent result →
      ProtectedLookupRules p h selector c result

theorem unrestrictedRules_eval {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {chain : List ClassId} {result : Option LookupResult}
    (rules : p.UnrestrictedLookupRules h selector start result)
    (hc : p.ClassChain h start chain) :
    p.lookupOnChain h .unrestricted selector chain = result := by
  induction rules generalizing chain with
  | top =>
      have hchain : chain = [p.top] := ClassChain.unique hc .top
      subst chain
      simp [lookupOnChain]
  | @here c method hne hd =>
      cases hc with
      | top => exact (hne rfl).elim
      | step => simp [lookupOnChain, hne, lookupAtNonTop, hd]
  | @super c parent result hne hd hparent _ ih =>
      cases hc with
      | top => exact (hne rfl).elim
      | @step _ parent' tail _ hparent' htail =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          simp [lookupOnChain, hne, lookupAtNonTop, hd, ih htail]

theorem unrestrictedRules_of_chain {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {chain : List ClassId} {result : Option LookupResult}
    (hc : p.ClassChain h start chain)
    (heval : p.lookupOnChain h .unrestricted selector chain = result) :
    p.UnrestrictedLookupRules h selector start result := by
  induction hc generalizing result with
  | top =>
      simp [lookupOnChain] at heval
      subst result
      exact .top
  | @step c parent tail hne hparent htail ih =>
      cases hd : p.direct h c selector with
      | none =>
          have htailEval : p.lookupOnChain h .unrestricted selector tail = result := by
            simpa [lookupOnChain, hne, lookupAtNonTop, hd] using heval
          exact .super hne hd hparent (ih htailEval)
      | some method =>
          have hit : p.UnrestrictedLookupRules h selector c
              (some ⟨method, c⟩) := .here hne hd
          rw [← heval]
          simpa [lookupOnChain, hne, lookupAtNonTop, hd] using hit

theorem unrestrictedRules_iff_lookup {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {result : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain) :
    p.UnrestrictedLookupRules h selector start result ↔
      p.Lookup h .unrestricted selector start result := by
  constructor
  · intro rules
    rcases hasChain with ⟨chain, hc⟩
    exact ⟨chain, hc, unrestrictedRules_eval rules hc⟩
  · rintro ⟨chain, hc, heval⟩
    exact unrestrictedRules_of_chain hc heval

theorem publicRules_eval {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {chain : List ClassId} {result : Option LookupResult}
    (rules : p.PublicLookupRules h selector start result)
    (hc : p.ClassChain h start chain) :
    p.lookupOnChain h .publicOnly selector chain = result := by
  induction rules generalizing chain with
  | top =>
      have hchain : chain = [p.top] := ClassChain.unique hc .top
      subst chain
      simp [lookupOnChain]
  | @hit c method hne hd ha =>
      cases hc with
      | top => exact (hne rfl).elim
      | step => simp [lookupOnChain, hne, lookupAtNonTop, hd, ha]
  | @protectedBarrier c method hne hd ha =>
      cases hc with
      | top => exact (hne rfl).elim
      | step => simp [lookupOnChain, hne, lookupAtNonTop, hd, ha]
  | @superAbsent c parent result hne hd hparent _ ih =>
      cases hc with
      | top => exact (hne rfl).elim
      | @step _ parent' tail _ hparent' htail =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          simp [lookupOnChain, hne, lookupAtNonTop, hd, ih htail]
  | @superPrivate c parent method result hne hd ha hparent _ ih =>
      cases hc with
      | top => exact (hne rfl).elim
      | @step _ parent' tail _ hparent' htail =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          simp [lookupOnChain, hne, lookupAtNonTop, hd, ha, ih htail]

theorem publicRules_of_chain {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {chain : List ClassId} {result : Option LookupResult}
    (hc : p.ClassChain h start chain)
    (heval : p.lookupOnChain h .publicOnly selector chain = result) :
    p.PublicLookupRules h selector start result := by
  induction hc generalizing result with
  | top =>
      simp [lookupOnChain] at heval
      subst result
      exact .top
  | @step c parent tail hne hparent htail ih =>
      cases hd : p.direct h c selector with
      | none =>
          have htailEval : p.lookupOnChain h .publicOnly selector tail = result := by
            simpa [lookupOnChain, hne, lookupAtNonTop, hd] using heval
          exact .superAbsent hne hd hparent (ih htailEval)
      | some method =>
          cases ha : method.access with
          | publicAccess =>
              have hit : p.PublicLookupRules h selector c
                  (some ⟨method, c⟩) := .hit hne hd ha
              rw [← heval]
              simpa [lookupOnChain, hne, lookupAtNonTop, hd, ha] using hit
          | protectedAccess =>
              have barrier : p.PublicLookupRules h selector c none :=
                .protectedBarrier hne hd ha
              rw [← heval]
              simpa [lookupOnChain, hne, lookupAtNonTop, hd, ha] using barrier
          | privateAccess =>
              have htailEval : p.lookupOnChain h .publicOnly selector tail = result := by
                simpa [lookupOnChain, hne, lookupAtNonTop, hd, ha] using heval
              exact .superPrivate hne hd ha hparent (ih htailEval)

theorem publicRules_iff_lookup {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {result : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain) :
    p.PublicLookupRules h selector start result ↔
      p.Lookup h .publicOnly selector start result := by
  constructor
  · intro rules
    rcases hasChain with ⟨chain, hc⟩
    exact ⟨chain, hc, publicRules_eval rules hc⟩
  · rintro ⟨chain, hc, heval⟩
    exact publicRules_of_chain hc heval

theorem protectedRules_eval {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {chain : List ClassId} {result : Option LookupResult}
    (rules : p.ProtectedLookupRules h selector start result)
    (hc : p.ClassChain h start chain) :
    p.lookupOnChain h .protectedAccess selector chain = result := by
  induction rules generalizing chain with
  | top =>
      have hchain : chain = [p.top] := ClassChain.unique hc .top
      subst chain
      simp [lookupOnChain]
  | @hitPublic c method hne hd ha =>
      cases hc with
      | top => exact (hne rfl).elim
      | step => simp [lookupOnChain, hne, lookupAtNonTop, hd, ha]
  | @hitProtected c method hne hd ha =>
      cases hc with
      | top => exact (hne rfl).elim
      | step => simp [lookupOnChain, hne, lookupAtNonTop, hd, ha]
  | @superAbsent c parent result hne hd hparent _ ih =>
      cases hc with
      | top => exact (hne rfl).elim
      | @step _ parent' tail _ hparent' htail =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          simp [lookupOnChain, hne, lookupAtNonTop, hd, ih htail]
  | @superPrivate c parent method result hne hd ha hparent _ ih =>
      cases hc with
      | top => exact (hne rfl).elim
      | @step _ parent' tail _ hparent' htail =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          simp [lookupOnChain, hne, lookupAtNonTop, hd, ha, ih htail]

theorem protectedRules_of_chain {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {chain : List ClassId} {result : Option LookupResult}
    (hc : p.ClassChain h start chain)
    (heval : p.lookupOnChain h .protectedAccess selector chain = result) :
    p.ProtectedLookupRules h selector start result := by
  induction hc generalizing result with
  | top =>
      simp [lookupOnChain] at heval
      subst result
      exact .top
  | @step c parent tail hne hparent htail ih =>
      cases hd : p.direct h c selector with
      | none =>
          have htailEval : p.lookupOnChain h .protectedAccess selector tail = result := by
            simpa [lookupOnChain, hne, lookupAtNonTop, hd] using heval
          exact .superAbsent hne hd hparent (ih htailEval)
      | some method =>
          cases ha : method.access with
          | publicAccess =>
              have hit : p.ProtectedLookupRules h selector c
                  (some ⟨method, c⟩) := .hitPublic hne hd ha
              rw [← heval]
              simpa [lookupOnChain, hne, lookupAtNonTop, hd, ha] using hit
          | protectedAccess =>
              have hit : p.ProtectedLookupRules h selector c
                  (some ⟨method, c⟩) := .hitProtected hne hd ha
              rw [← heval]
              simpa [lookupOnChain, hne, lookupAtNonTop, hd, ha] using hit
          | privateAccess =>
              have htailEval : p.lookupOnChain h .protectedAccess selector tail = result := by
                simpa [lookupOnChain, hne, lookupAtNonTop, hd, ha] using heval
              exact .superPrivate hne hd ha hparent (ih htailEval)

theorem protectedRules_iff_lookup {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {result : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain) :
    p.ProtectedLookupRules h selector start result ↔
      p.Lookup h .protectedAccess selector start result := by
  constructor
  · intro rules
    rcases hasChain with ⟨chain, hc⟩
    exact ⟨chain, hc, protectedRules_eval rules hc⟩
  · rintro ⟨chain, hc, heval⟩
    exact protectedRules_of_chain hc heval

theorem unrestrictedRules_deterministic {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {r₁ r₂ : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain)
    (h₁ : p.UnrestrictedLookupRules h selector start r₁)
    (h₂ : p.UnrestrictedLookupRules h selector start r₂) : r₁ = r₂ :=
  lookup_deterministic
    ((unrestrictedRules_iff_lookup hasChain).mp h₁)
    ((unrestrictedRules_iff_lookup hasChain).mp h₂)

theorem publicRules_deterministic {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {r₁ r₂ : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain)
    (h₁ : p.PublicLookupRules h selector start r₁)
    (h₂ : p.PublicLookupRules h selector start r₂) : r₁ = r₂ :=
  lookup_deterministic
    ((publicRules_iff_lookup hasChain).mp h₁)
    ((publicRules_iff_lookup hasChain).mp h₂)

theorem protectedRules_deterministic {p : Program} {h : Heap} {selector : Selector}
    {start : ClassId} {r₁ r₂ : Option LookupResult}
    (hasChain : ∃ chain, p.ClassChain h start chain)
    (h₁ : p.ProtectedLookupRules h selector start r₁)
    (h₂ : p.ProtectedLookupRules h selector start r₂) : r₁ = r₂ :=
  lookup_deterministic
    ((protectedRules_iff_lookup hasChain).mp h₁)
    ((protectedRules_iff_lookup hasChain).mp h₂)

end Program
end Newspeak
