import Newspeak.PEGWellFormed
import Newspeak.NewspeakGrammar

namespace Newspeak

def pegReferencedNames : PEGExpr → List Nonterminal
  | .empty | .character _ | .characterSet _ | .any => []
  | .nonterminal name => [name]
  | .sequence first second | .orderedChoice first second =>
      pegReferencedNames first ++ pegReferencedNames second
  | .star body | .notAhead body | .andAhead body | .capture _ body =>
      pegReferencedNames body

def pegNullableUpper (oracle : Nonterminal → Bool) : PEGExpr → Bool
  | .empty => true
  | .character _ | .characterSet _ | .any => false
  | .nonterminal name => oracle name
  | .sequence first second =>
      pegNullableUpper oracle first && pegNullableUpper oracle second
  | .orderedChoice first second =>
      pegNullableUpper oracle first || pegNullableUpper oracle second
  | .star _ | .notAhead _ | .andAhead _ => true
  | .capture _ body => pegNullableUpper oracle body

def pegLeadingUpper (oracle : Nonterminal → Bool) : PEGExpr → List Nonterminal
  | .empty | .character _ | .characterSet _ | .any => []
  | .nonterminal name => [name]
  | .sequence first second =>
      pegLeadingUpper oracle first ++
        (if pegNullableUpper oracle first then pegLeadingUpper oracle second else [])
  | .orderedChoice first second =>
      pegLeadingUpper oracle first ++ pegLeadingUpper oracle second
  | .star body | .notAhead body | .andAhead body | .capture _ body =>
      pegLeadingUpper oracle body

def pegRepetitionsAdvance (oracle : Nonterminal → Bool) : PEGExpr → Bool
  | .empty | .character _ | .characterSet _ | .any | .nonterminal _ => true
  | .sequence first second | .orderedChoice first second =>
      pegRepetitionsAdvance oracle first && pegRepetitionsAdvance oracle second
  | .star body =>
      !pegNullableUpper oracle body && pegRepetitionsAdvance oracle body
  | .notAhead body | .andAhead body | .capture _ body =>
      pegRepetitionsAdvance oracle body

def nullableStep (grammar : PEGGrammar)
    (oracle : FiniteStore Nonterminal Bool) : FiniteStore Nonterminal Bool :=
  grammar.rules.domain.foldl (fun next name =>
    match grammar.rules name with
    | none => next
    | some body => next.install name (pegNullableUpper
        (fun target => (oracle target).getD false) body))
    (FiniteStore.empty Nonterminal Bool)

def nullableIterations (grammar : PEGGrammar) : Nat →
    FiniteStore Nonterminal Bool → FiniteStore Nonterminal Bool
  | 0, oracle => oracle
  | fuel + 1, oracle => nullableIterations grammar fuel
      (nullableStep grammar oracle)

def computedNullableOracle (grammar : PEGGrammar) :
    FiniteStore Nonterminal Bool :=
  nullableIterations grammar (grammar.rules.domain.length + 1)
    (FiniteStore.constantOn grammar.rules.domain false)

def maximumNat (values : List Nat) : Nat := values.foldl Nat.max 0

def rankStep (grammar : PEGGrammar) (oracle : Nonterminal → Bool)
    (ranks : FiniteStore Nonterminal Nat) : FiniteStore Nonterminal Nat :=
  grammar.rules.domain.foldl (fun next name =>
    match grammar.rules name with
    | none => next
    | some body =>
        let successors := pegLeadingUpper oracle body
        next.install name (maximumNat
          (successors.map fun target => (ranks target).getD 0) + 1))
    (FiniteStore.empty Nonterminal Nat)

def rankIterations (grammar : PEGGrammar) (oracle : Nonterminal → Bool) :
    Nat → FiniteStore Nonterminal Nat → FiniteStore Nonterminal Nat
  | 0, ranks => ranks
  | fuel + 1, ranks => rankIterations grammar oracle fuel
      (rankStep grammar oracle ranks)

def computedLeadingRanks (grammar : PEGGrammar)
    (oracle : Nonterminal → Bool) : FiniteStore Nonterminal Nat :=
  rankIterations grammar oracle (grammar.rules.domain.length + 1)
    (FiniteStore.constantOn grammar.rules.domain 0)

def erasePEGCharacterPredicates : PEGExpr → PEGExpr
  | .empty => .empty
  | .character value => .character value
  | .characterSet _ => .characterSet fun _ => false
  | .any => .any
  | .nonterminal name => .nonterminal name
  | .sequence first second =>
      .sequence (erasePEGCharacterPredicates first)
        (erasePEGCharacterPredicates second)
  | .orderedChoice first second =>
      .orderedChoice (erasePEGCharacterPredicates first)
        (erasePEGCharacterPredicates second)
  | .star body => .star (erasePEGCharacterPredicates body)
  | .notAhead body => .notAhead (erasePEGCharacterPredicates body)
  | .andAhead body => .andAhead (erasePEGCharacterPredicates body)
  | .capture name body => .capture name (erasePEGCharacterPredicates body)

def erasePEGGrammarCharacterPredicates (grammar : PEGGrammar) : PEGGrammar :=
  { grammar with
    rules := grammar.rules.mapValues fun _ body =>
      erasePEGCharacterPredicates body }

theorem FiniteStore.mapValues_install_sameType
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (transform : Key → Value → Value)
    (key : Key) (value : Value) :
    (store.install key value).mapValues transform =
      (store.mapValues transform).install key (transform key value) := by
  apply FiniteStore.extensional_eq
  · intro candidate
    by_cases same : candidate = key
    · subst candidate
      simp
    · simp [FiniteStore.mapValues_apply, FiniteStore.install_away, same]
  · rfl

theorem mapValues_finiteStoreFromEntries
    {Key Value : Type} [DecidableEq Key]
    (entries : List (Key × Value)) (transform : Key → Value → Value) :
    (finiteStoreFromEntries entries).mapValues transform =
      finiteStoreFromEntries
        (entries.map fun entry => (entry.1, transform entry.1 entry.2)) := by
  unfold finiteStoreFromEntries
  have general : ∀ (remaining : List (Key × Value))
      (store : FiniteStore Key Value),
      (remaining.foldl (fun current entry =>
          current.install entry.1 entry.2) store).mapValues transform =
        remaining.foldl (fun current entry =>
          current.install entry.1 (transform entry.1 entry.2))
          (store.mapValues transform) := by
    intro remaining
    induction remaining with
    | nil => intro store; rfl
    | cons entry remaining ih =>
        intro store
        simp only [List.foldl_cons]
        rw [ih]
        congr 1
        exact FiniteStore.mapValues_install_sameType store transform
          entry.1 entry.2
  rw [List.foldl_map]
  have emptyMapped :
      (FiniteStore.empty Key Value).mapValues transform =
        FiniteStore.empty Key Value := by
    apply FiniteStore.extensional_eq
    · intro key
      rfl
    · rfl
  rw [← emptyMapped]
  exact general entries (FiniteStore.empty Key Value)

def pegGrammarCertificateValidRaw (grammar : PEGGrammar) : Bool :=
  let nullableStore := computedNullableOracle grammar
  let nullable := fun name => (nullableStore name).getD false
  let ranks := computedLeadingRanks grammar nullable
  (grammar.rules grammar.start).isSome &&
  grammar.rules.domain.all (fun name =>
    match grammar.rules name with
    | none => false
    | some body =>
        (pegReferencedNames body).all (fun target =>
          (grammar.rules target).isSome) &&
        (!pegNullableUpper nullable body || nullable name) &&
        pegRepetitionsAdvance nullable body &&
        (pegLeadingUpper nullable body).all (fun target =>
          (ranks target).getD 0 < (ranks name).getD 0))

def pegGrammarCertificateValid (grammar : PEGGrammar) : Bool :=
  pegGrammarCertificateValidRaw (erasePEGGrammarCharacterPredicates grammar)

/-- A closed representative for grammar-admissibility checking. Character-set
    predicates cannot recognize the empty input and are otherwise opaque to
    every certificate component. -/
def certificateCharacterClasses : NewspeakCharacterClasses where
  whiteSpace := fun _ => false
  asciiLetter := fun _ => false
  asciiUpper := fun _ => false
  decimalDigit := fun _ => false
  specialCharacter := fun _ => false

def erasedNewspeakGrammarEntries (classes : NewspeakCharacterClasses) :
    List (Nonterminal × PEGExpr) :=
  (newspeakGrammarEntries classes).map fun entry =>
    (entry.1, erasePEGCharacterPredicates entry.2)

set_option maxRecDepth 100000 in
theorem erasedNewspeakGrammarEntries_independent
    (classes : NewspeakCharacterClasses) :
    erasedNewspeakGrammarEntries classes =
      erasedNewspeakGrammarEntries certificateCharacterClasses := by
  rfl

theorem erase_newspeakGrammar_independent
    (classes : NewspeakCharacterClasses) :
    erasePEGGrammarCharacterPredicates (newspeakGrammar classes) =
      erasePEGGrammarCharacterPredicates
        (newspeakGrammar certificateCharacterClasses) := by
  unfold erasePEGGrammarCharacterPredicates newspeakGrammar
  simp only [mapValues_finiteStoreFromEntries]
  rw [show (newspeakGrammarEntries classes).map
      (fun entry => (entry.1, erasePEGCharacterPredicates entry.2)) =
      erasedNewspeakGrammarEntries classes by rfl]
  rw [show (newspeakGrammarEntries certificateCharacterClasses).map
      (fun entry => (entry.1, erasePEGCharacterPredicates entry.2)) =
      erasedNewspeakGrammarEntries certificateCharacterClasses by rfl]
  rw [erasedNewspeakGrammarEntries_independent]

theorem newspeakGrammarCanonical_certificate_valid :
    pegGrammarCertificateValid
      (newspeakGrammar certificateCharacterClasses) = true := by
  native_decide

theorem newspeakGrammar_certificate_valid
    (classes : NewspeakCharacterClasses) :
    pegGrammarCertificateValid (newspeakGrammar classes) = true := by
  unfold pegGrammarCertificateValid
  rw [erase_newspeakGrammar_independent]
  exact newspeakGrammarCanonical_certificate_valid

end Newspeak
