import Newspeak.PEGCertificate

namespace Newspeak

theorem PEGRecognizes.result_monotone
    {grammar : PEGGrammar} {source : SourceText} {expression : PEGExpr}
    {start : Nat} {result : PEGResult}
    (recognizes : PEGRecognizes grammar source expression start result) :
    match result with
    | .success finish _ => start ≤ finish
    | .failure _ => True := by
  induction recognizes with
  | empty => exact Nat.le_refl _
  | characterSuccess => omega
  | characterFailure => trivial
  | characterSetSuccess => omega
  | characterSetFailureAbsent => trivial
  | characterSetFailureRejected => trivial
  | anySuccess => omega
  | anyFailure => trivial
  | nonterminalDefined _ _ _ result _ _ ih =>
      cases result <;> simp_all
  | nonterminalUndefined => trivial
  | sequenceFirstFailure => trivial
  | sequenceSecondFailure => trivial
  | sequenceSuccess _ _ _ _ _ _ _ _ _ firstIH secondIH =>
      exact Nat.le_trans firstIH secondIH
  | choiceLeftSuccess _ _ _ _ _ _ ih => exact ih
  | choiceRight _ _ _ _ result _ _ _ rightIH =>
      cases result <;> simp_all
  | starStop => exact Nat.le_refl _
  | starStep _ _ _ _ _ _ _ _ _ _ remainingIH =>
      exact Nat.le_trans (Nat.le_of_lt ‹_›) remainingIH
  | notAheadSuccess => exact Nat.le_refl _
  | notAheadFailure => trivial
  | andAheadSuccess => exact Nat.le_refl _
  | andAheadFailure => trivial
  | captureSuccess _ _ _ _ _ _ ih => exact ih
  | captureFailure => trivial

theorem PEGRecognizes.success_monotone
    {grammar : PEGGrammar} {source : SourceText} {expression : PEGExpr}
    {start finish : Nat} {forest : List ConcreteTree}
    (recognizes : PEGRecognizes grammar source expression start
      (.success finish forest)) :
    start ≤ finish :=
  recognizes.result_monotone

theorem PEGReferencesNonterminal.mem_referencedNames
    {expression : PEGExpr} {name : Nonterminal}
    (references : PEGReferencesNonterminal expression name) :
    name ∈ pegReferencedNames expression := by
  induction references <;> simp_all [pegReferencedNames]

theorem PEGRecognizes.noAdvance_upper
    {grammar : PEGGrammar} {oracle : Nonterminal → Bool}
    (closed : ∀ {name body}, grammar.rules name = some body →
      pegNullableUpper oracle body = true → oracle name = true)
    {source : SourceText} {expression : PEGExpr} {start finish : Nat}
    {forest : List ConcreteTree}
    (recognizes : PEGRecognizes grammar source expression start
      (.success finish forest))
    (noAdvance : start = finish) :
    pegNullableUpper oracle expression = true := by
  have general : ∀ {expression start result},
      PEGRecognizes grammar source expression start result →
      match result with
      | .success finish _ => start = finish →
          pegNullableUpper oracle expression = true
      | .failure _ => True := by
    intro current currentStart result currentRecognizes
    induction currentRecognizes with
    | empty => simp [pegNullableUpper]
    | characterSuccess => simp [pegNullableUpper]
    | characterFailure => trivial
    | characterSetSuccess => simp [pegNullableUpper]
    | characterSetFailureAbsent => trivial
    | characterSetFailureRejected => trivial
    | anySuccess => simp [pegNullableUpper]
    | anyFailure => trivial
    | nonterminalDefined _ name body result defined recognizes ih =>
        cases result <;> simp_all [pegNullableUpper]
    | nonterminalUndefined => trivial
    | sequenceFirstFailure => trivial
    | sequenceSecondFailure => trivial
    | sequenceSuccess offset first second middle final firstForest secondForest
          firstSucceeds secondSucceeds firstIH secondIH =>
        simp only [pegNullableUpper, Bool.and_eq_true]
        intro same
        have firstLe := firstSucceeds.success_monotone
        have secondLe := secondSucceeds.success_monotone
        have firstSame : offset = middle := by omega
        have secondSame : middle = final := by omega
        exact ⟨firstIH firstSame, secondIH secondSame⟩
    | choiceLeftSuccess _ _ _ _ _ _ ih =>
        simp only [pegNullableUpper, Bool.or_eq_true]
        intro same
        exact Or.inl (ih same)
    | choiceRight _ _ _ _ result _ _ _ rightIH =>
        cases result <;> simp_all [pegNullableUpper]
    | starStop => simp [pegNullableUpper]
    | starStep => simp [pegNullableUpper]
    | notAheadSuccess => simp [pegNullableUpper]
    | notAheadFailure => trivial
    | andAheadSuccess => simp [pegNullableUpper]
    | andAheadFailure => trivial
    | captureSuccess _ _ _ _ _ _ ih =>
        simpa [pegNullableUpper] using ih
    | captureFailure => trivial
  exact general recognizes noAdvance

theorem PEGNullable.upper
    {grammar : PEGGrammar} {oracle : Nonterminal → Bool}
    (closed : ∀ {name body}, grammar.rules name = some body →
      pegNullableUpper oracle body = true → oracle name = true)
    {expression : PEGExpr}
    (nullable : PEGNullable grammar expression) :
    pegNullableUpper oracle expression = true := by
  rcases nullable with ⟨forest, recognizes⟩
  exact recognizes.noAdvance_upper closed rfl

theorem PEGLeadingNonterminal.mem_leadingUpper
    {grammar : PEGGrammar} {oracle : Nonterminal → Bool}
    (closed : ∀ {name body}, grammar.rules name = some body →
      pegNullableUpper oracle body = true → oracle name = true)
    {expression : PEGExpr} {name : Nonterminal}
    (leading : PEGLeadingNonterminal grammar expression name) :
    name ∈ pegLeadingUpper oracle expression := by
  induction leading <;>
    simp_all [pegLeadingUpper, PEGNullable.upper closed]

theorem pegRepetitionsAdvance_subexpression
    {oracle : Nonterminal → Bool} {expression repeated : PEGExpr}
    (advances : pegRepetitionsAdvance oracle expression = true)
    (occurs : PEGSubexpression (.star repeated) expression) :
    pegNullableUpper oracle repeated = false := by
  induction occurs <;> simp_all [pegRepetitionsAdvance]

structure PEGGrammarCertificate (grammar : PEGGrammar) where
  nullable : Nonterminal → Bool
  rank : Nonterminal → Nat
  startDefined : grammar.rules grammar.start ≠ none
  referencesDefined :
    ∀ {source body target}, grammar.rules source = some body →
      target ∈ pegReferencedNames body → grammar.rules target ≠ none
  nullableClosed :
    ∀ {name body}, grammar.rules name = some body →
      pegNullableUpper nullable body = true → nullable name = true
  repetitionsAdvance :
    ∀ {source body}, grammar.rules source = some body →
      pegRepetitionsAdvance nullable body = true
  rankDecreases :
    ∀ {source body target}, grammar.rules source = some body →
      target ∈ pegLeadingUpper nullable body → rank target < rank source

def pegGrammarCertificateValidRaw_sound
    {grammar : PEGGrammar}
    (valid : pegGrammarCertificateValidRaw grammar = true) :
    PEGGrammarCertificate grammar := by
  let nullableStore := computedNullableOracle grammar
  let nullable := fun name => (nullableStore name).getD false
  let ranks := computedLeadingRanks grammar nullable
  change ((grammar.rules grammar.start).isSome &&
    grammar.rules.domain.all (fun name =>
      match grammar.rules name with
      | none => false
      | some body =>
          (pegReferencedNames body).all (fun target =>
            (grammar.rules target).isSome) &&
          (!pegNullableUpper nullable body || nullable name) &&
          pegRepetitionsAdvance nullable body &&
          (pegLeadingUpper nullable body).all (fun target =>
            (ranks target).getD 0 < (ranks name).getD 0))) = true at valid
  have validity := Bool.and_eq_true_iff.mp valid
  refine
    { nullable := nullable
      rank := fun name => (ranks name).getD 0
      startDefined := Option.isSome_iff_ne_none.mp validity.1
      referencesDefined := ?_
      nullableClosed := ?_
      repetitionsAdvance := ?_
      rankDecreases := ?_ }
  · intro source body target defined referenced
    have sourceMember := FiniteStore.mem_domain_of_lookup_eq_some defined
    have checked := (List.all_eq_true.mp validity.2) source sourceMember
    rw [defined] at checked
    simp only [Bool.and_eq_true] at checked
    have targetChecked := (List.all_eq_true.mp checked.1.1.1) target referenced
    exact Option.isSome_iff_ne_none.mp targetChecked
  · intro name body defined bodyNullable
    have nameMember := FiniteStore.mem_domain_of_lookup_eq_some defined
    have checked := (List.all_eq_true.mp validity.2) name nameMember
    rw [defined] at checked
    simp only [Bool.and_eq_true] at checked
    have closure := checked.1.1.2
    simp [bodyNullable] at closure
    exact closure
  · intro source body defined
    have sourceMember := FiniteStore.mem_domain_of_lookup_eq_some defined
    have checked := (List.all_eq_true.mp validity.2) source sourceMember
    rw [defined] at checked
    simp only [Bool.and_eq_true] at checked
    exact checked.1.2
  · intro source body target defined leading
    have sourceMember := FiniteStore.mem_domain_of_lookup_eq_some defined
    have checked := (List.all_eq_true.mp validity.2) source sourceMember
    rw [defined] at checked
    simp only [Bool.and_eq_true] at checked
    exact of_decide_eq_true ((List.all_eq_true.mp checked.2) target leading)

@[simp] theorem pegReferencedNames_erase (expression : PEGExpr) :
    pegReferencedNames (erasePEGCharacterPredicates expression) =
      pegReferencedNames expression := by
  induction expression <;> simp [erasePEGCharacterPredicates,
    pegReferencedNames, *]

@[simp] theorem pegNullableUpper_erase (oracle : Nonterminal → Bool)
    (expression : PEGExpr) :
    pegNullableUpper oracle (erasePEGCharacterPredicates expression) =
      pegNullableUpper oracle expression := by
  induction expression <;> simp [erasePEGCharacterPredicates,
    pegNullableUpper, *]

@[simp] theorem pegLeadingUpper_erase (oracle : Nonterminal → Bool)
    (expression : PEGExpr) :
    pegLeadingUpper oracle (erasePEGCharacterPredicates expression) =
      pegLeadingUpper oracle expression := by
  induction expression <;> simp [erasePEGCharacterPredicates,
    pegLeadingUpper, pegNullableUpper_erase, *]

@[simp] theorem pegRepetitionsAdvance_erase (oracle : Nonterminal → Bool)
    (expression : PEGExpr) :
    pegRepetitionsAdvance oracle (erasePEGCharacterPredicates expression) =
      pegRepetitionsAdvance oracle expression := by
  induction expression <;> simp [erasePEGCharacterPredicates,
    pegRepetitionsAdvance, pegNullableUpper_erase, *]

def PEGGrammarCertificate.ofErased
    {grammar : PEGGrammar}
    (certificate : PEGGrammarCertificate
      (erasePEGGrammarCharacterPredicates grammar)) :
    PEGGrammarCertificate grammar :=
  { nullable := certificate.nullable
    rank := certificate.rank
    startDefined := by
      intro absent
      apply certificate.startDefined
      simp [erasePEGGrammarCharacterPredicates, absent]
    referencesDefined := by
      intro source body target defined referenced absent
      have erasedDefined :
          (erasePEGGrammarCharacterPredicates grammar).rules source =
            some (erasePEGCharacterPredicates body) := by
        simp [erasePEGGrammarCharacterPredicates, defined]
      have erasedTarget := certificate.referencesDefined erasedDefined
        (by simpa using referenced)
      exact erasedTarget (by
        simp [erasePEGGrammarCharacterPredicates, absent])
    nullableClosed := by
      intro name body defined nullable
      apply certificate.nullableClosed (body := erasePEGCharacterPredicates body)
      · simp [erasePEGGrammarCharacterPredicates, defined]
      · simpa using nullable
    repetitionsAdvance := by
      intro source body defined
      have checked := certificate.repetitionsAdvance
        (source := source) (body := erasePEGCharacterPredicates body) (by
          simp [erasePEGGrammarCharacterPredicates, defined])
      simpa using checked
    rankDecreases := by
      intro source body target defined leading
      apply certificate.rankDecreases
        (body := erasePEGCharacterPredicates body)
      · simp [erasePEGGrammarCharacterPredicates, defined]
      · simpa using leading }

def pegGrammarCertificateValid_sound
    {grammar : PEGGrammar}
    (valid : pegGrammarCertificateValid grammar = true) :
    PEGGrammarCertificate grammar :=
  PEGGrammarCertificate.ofErased
    (pegGrammarCertificateValidRaw_sound valid)

theorem PEGGrammarCertificate.leads_rank_decreases
    {grammar : PEGGrammar} (certificate : PEGGrammarCertificate grammar)
    {source target : Nonterminal}
    (leads : PEGLeads grammar source target) :
    certificate.rank target < certificate.rank source := by
  rcases leads with ⟨body, defined, leading⟩
  exact certificate.rankDecreases defined
    (leading.mem_leadingUpper certificate.nullableClosed)

theorem PEGGrammarCertificate.leadsPlus_rank_decreases
    {grammar : PEGGrammar} (certificate : PEGGrammarCertificate grammar)
    {source target : Nonterminal}
    (leads : PEGLeadsPlus grammar source target) :
    certificate.rank target < certificate.rank source := by
  induction leads with
  | single direct => exact certificate.leads_rank_decreases direct
  | step direct remaining ih =>
      exact Nat.lt_trans ih (certificate.leads_rank_decreases direct)

theorem PEGGrammarCertificate.sound
    {grammar : PEGGrammar} (certificate : PEGGrammarCertificate grammar) :
    PEGGrammarWellFormed grammar where
  startDefined := certificate.startDefined
  referencesDefined := by
    intro source body target defined references
    exact certificate.referencesDefined defined references.mem_referencedNames
  noLeftRecursion := by
    intro name recursive
    exact (Nat.lt_irrefl _)
      (certificate.leadsPlus_rank_decreases recursive)
  repetitionAdvances := by
    intro source body repeated defined occurs nullable
    have upperFalse := pegRepetitionsAdvance_subexpression
      (certificate.repetitionsAdvance defined) occurs
    have upperTrue := nullable.upper certificate.nullableClosed
    simp_all

theorem pegGrammarCertificateValid_wellFormed
    {grammar : PEGGrammar}
    (valid : pegGrammarCertificateValid grammar = true) :
    PEGGrammarWellFormed grammar :=
  (pegGrammarCertificateValid_sound valid).sound

theorem newspeakGrammarCanonical_wellFormed :
    PEGGrammarWellFormed (newspeakGrammar certificateCharacterClasses) :=
  pegGrammarCertificateValid_wellFormed
    newspeakGrammarCanonical_certificate_valid

theorem newspeakGrammar_wellFormed
    (classes : NewspeakCharacterClasses) :
    PEGGrammarWellFormed (newspeakGrammar classes) :=
  pegGrammarCertificateValid_wellFormed
    (newspeakGrammar_certificate_valid classes)

end Newspeak
