import Newspeak.Lookup

namespace Newspeak
namespace Program

theorem lookup_deterministic {p : Program} {h : Heap} {mode : LookupMode}
    {s : Selector} {start : ClassId} {r₁ r₂ : Option LookupResult}
    (h₁ : p.Lookup h mode s start r₁) (h₂ : p.Lookup h mode s start r₂) :
    r₁ = r₂ := by
  rcases h₁ with ⟨chain₁, hc₁, hr₁⟩
  rcases h₂ with ⟨chain₂, hc₂, hr₂⟩
  have hchain : chain₁ = chain₂ := ClassChain.unique hc₁ hc₂
  subst chain₂
  rw [← hr₁, ← hr₂]

theorem unrestricted_lookup_deterministic {p : Program} {h : Heap} {s : Selector}
    {start : ClassId} {r₁ r₂ : Option LookupResult}
    (h₁ : p.Lookup h .unrestricted s start r₁)
    (h₂ : p.Lookup h .unrestricted s start r₂) : r₁ = r₂ :=
  lookup_deterministic h₁ h₂

theorem public_lookup_deterministic {p : Program} {h : Heap} {s : Selector}
    {start : ClassId} {r₁ r₂ : Option LookupResult}
    (h₁ : p.Lookup h .publicOnly s start r₁)
    (h₂ : p.Lookup h .publicOnly s start r₂) : r₁ = r₂ :=
  lookup_deterministic h₁ h₂

theorem protected_lookup_deterministic {p : Program} {h : Heap} {s : Selector}
    {start : ClassId} {r₁ r₂ : Option LookupResult}
    (h₁ : p.Lookup h .protectedAccess s start r₁)
    (h₂ : p.Lookup h .protectedAccess s start r₂) : r₁ = r₂ :=
  lookup_deterministic h₁ h₂

theorem lookupOnChain_public_result_is_public
    (p : Program) (h : Heap) (selector : Selector)
    {chain : List ClassId} {result : LookupResult}
    (found : p.lookupOnChain h .publicOnly selector chain = some result) :
    result.method.access = .publicAccess := by
  induction chain with
  | nil => simp [lookupOnChain] at found
  | cons classId ancestors inductionHypothesis =>
      by_cases atTop : classId = p.top
      · simp [lookupOnChain, atTop] at found
      · simp only [lookupOnChain, atTop, ↓reduceIte] at found
        cases directResult : p.direct h classId selector with
        | none =>
            simp [lookupAtNonTop, directResult] at found
            exact inductionHypothesis found
        | some method =>
            cases accessResult : method.access with
            | publicAccess =>
                simp [lookupAtNonTop, directResult, accessResult] at found
                rw [← found]
                exact accessResult
            | protectedAccess =>
                simp [lookupAtNonTop, directResult, accessResult] at found
            | privateAccess =>
                simp [lookupAtNonTop, directResult, accessResult] at found
                exact inductionHypothesis found

theorem lookupOnChain_protected_result_not_private
    (p : Program) (h : Heap) (selector : Selector)
    {chain : List ClassId} {result : LookupResult}
    (found : p.lookupOnChain h .protectedAccess selector chain = some result) :
    result.method.access ≠ .privateAccess := by
  induction chain with
  | nil => simp [lookupOnChain] at found
  | cons classId ancestors inductionHypothesis =>
      by_cases atTop : classId = p.top
      · simp [lookupOnChain, atTop] at found
      · simp only [lookupOnChain, atTop, ↓reduceIte] at found
        cases directResult : p.direct h classId selector with
        | none =>
            simp [lookupAtNonTop, directResult] at found
            exact inductionHypothesis found
        | some method =>
            cases accessResult : method.access with
            | publicAccess =>
                simp [lookupAtNonTop, directResult, accessResult] at found
                rw [← found]
                simp [accessResult]
            | protectedAccess =>
                simp [lookupAtNonTop, directResult, accessResult] at found
                rw [← found]
                simp [accessResult]
            | privateAccess =>
                simp [lookupAtNonTop, directResult, accessResult] at found
                exact inductionHypothesis found

theorem publicLookup_result_is_public
    {p : Program} {h : Heap} {selector : Selector} {start : ClassId}
    {result : LookupResult}
    (lookup : p.Lookup h .publicOnly selector start (some result)) :
    result.method.access = .publicAccess := by
  rcases lookup with ⟨chain, _classChain, found⟩
  exact p.lookupOnChain_public_result_is_public h selector found

theorem protectedLookup_result_not_private
    {p : Program} {h : Heap} {selector : Selector} {start : ClassId}
    {result : LookupResult}
    (lookup : p.Lookup h .protectedAccess selector start (some result)) :
    result.method.access ≠ .privateAccess := by
  rcases lookup with ⟨chain, _classChain, found⟩
  exact p.lookupOnChain_protected_result_not_private h selector found

end Program
end Newspeak
