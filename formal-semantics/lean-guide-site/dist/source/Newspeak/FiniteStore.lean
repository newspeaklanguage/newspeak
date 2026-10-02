namespace Newspeak

/-- Relational lifting through a partial computation.  Two failures agree;
    two successes agree when their payloads do; success never agrees with
    failure.  Reflection uses this when fresh finite-store insertions differ
    only in unobservable domain order. -/
inductive OptionalResultsRelated {Value : Type} (related : Value → Value → Prop) :
    Option Value → Option Value → Prop where
  | bothFailed : OptionalResultsRelated related none none
  | bothSucceeded {left right} :
      related left right → OptionalResultsRelated related (some left) (some right)

theorem OptionalResultsRelated.symmetric {Value : Type}
    {related : Value → Value → Prop}
    (relatedSymmetric : ∀ {left right}, related left right → related right left)
    {left right : Option Value}
    (results : OptionalResultsRelated related left right) :
    OptionalResultsRelated related right left := by
  cases results with
  | bothFailed => exact .bothFailed
  | bothSucceeded relatedValues =>
      exact .bothSucceeded (relatedSymmetric relatedValues)

theorem OptionalResultsRelated.reflexive {Value : Type}
    {related : Value → Value → Prop}
    (relatedReflexive : ∀ value, related value value)
    (result : Option Value) : OptionalResultsRelated related result result := by
  cases result with
  | none => exact .bothFailed
  | some value => exact .bothSucceeded (relatedReflexive value)

theorem OptionalResultsRelated.transitive {Value : Type}
    {related : Value → Value → Prop}
    (relatedTransitive : ∀ {first second third},
      related first second → related second third → related first third)
    {first second third : Option Value}
    (left : OptionalResultsRelated related first second)
    (right : OptionalResultsRelated related second third) :
    OptionalResultsRelated related first third := by
  cases left with
  | bothFailed => cases right; exact .bothFailed
  | bothSucceeded leftRelated =>
      cases right with
      | bothSucceeded rightRelated =>
          exact .bothSucceeded (relatedTransitive leftRelated rightRelated)

theorem OptionalResultsRelated.bind
    {Value Result : Type}
    {inputRelated : Value → Value → Prop}
    {outputRelated : Result → Result → Prop}
    {left right : Option Value}
    (inputs : OptionalResultsRelated inputRelated left right)
    (leftNext rightNext : Value → Option Result)
    (nextRelated : ∀ {leftValue rightValue},
      inputRelated leftValue rightValue →
        OptionalResultsRelated outputRelated (leftNext leftValue)
          (rightNext rightValue)) :
    OptionalResultsRelated outputRelated (left.bind leftNext)
      (right.bind rightNext) := by
  cases inputs with
  | bothFailed => exact .bothFailed
  | bothSucceeded relatedValues => exact nextRelated relatedValues

/-- An extensional partial map paired with an exact, duplicate-free executable
    domain.  The representation keeps existing lookup proofs independent of a
    particular balanced-tree library while making heap enumeration total. -/
structure FiniteStore (Key Value : Type) [DecidableEq Key] where
  lookup : Key → Option Value
  domain : List Key
  domainNodup : domain.Nodup
  lookupDefinedIffMem : ∀ key, lookup key ≠ none ↔ key ∈ domain

namespace FiniteStore

/-- Duplicate elimination driven by propositional key equality, with its
    invariants proved below rather than delegated to a `BEq` law. -/
def deduplicated {Element : Type} [DecidableEq Element] :
    List Element → List Element
  | [] => []
  | element :: remaining =>
      let tail := deduplicated remaining
      if element ∈ tail then tail else element :: tail

@[simp] theorem mem_deduplicated {Element : Type} [DecidableEq Element]
    (element : Element) (elements : List Element) :
    element ∈ deduplicated elements ↔ element ∈ elements := by
  induction elements generalizing element with
  | nil => simp [deduplicated]
  | cons first remaining ih =>
      simp only [deduplicated]
      by_cases present : first ∈ deduplicated remaining
      · simp only [present, ↓reduceIte]
        constructor
        · intro member
          exact List.mem_cons_of_mem first ((ih element).mp member)
        · intro member
          rcases List.mem_cons.mp member with equal | inRemaining
          · subst element
            exact present
          · exact (ih element).mpr inRemaining
      · simp only [present, ↓reduceIte]
        simp [ih]

theorem deduplicated_nodup {Element : Type} [DecidableEq Element]
    (elements : List Element) : (deduplicated elements).Nodup := by
  induction elements with
  | nil => simp [deduplicated]
  | cons first remaining ih =>
      simp only [deduplicated]
      by_cases present : first ∈ deduplicated remaining
      · simp only [present, ↓reduceIte]
        exact ih
      · simp only [present, ↓reduceIte]
        apply List.Pairwise.cons
        · intro candidate member equal
          subst candidate
          exact present member
        · exact ih

instance {Key Value : Type} [DecidableEq Key] :
    CoeFun (FiniteStore Key Value) (fun _ => Key → Option Value) where
  coe := FiniteStore.lookup

def empty (Key Value : Type) [DecidableEq Key] : FiniteStore Key Value :=
  { lookup := fun _ => none
    domain := []
    domainNodup := List.nodup_nil
    lookupDefinedIffMem := by simp }

@[simp] theorem empty_apply (Key Value : Type) [DecidableEq Key] (key : Key) :
    (empty Key Value) key = none := by
  rfl

/-- A finite store with one fixed value at exactly the listed keys. -/
def constantOn {Key Value : Type} [DecidableEq Key]
    (keys : List Key) (value : Value) : FiniteStore Key Value :=
  { lookup := fun key => if key ∈ keys then some value else none
    domain := deduplicated keys
    domainNodup := deduplicated_nodup keys
    lookupDefinedIffMem := by
      intro key
      simp [mem_deduplicated] }

@[simp] theorem constantOn_apply {Key Value : Type} [DecidableEq Key]
    (keys : List Key) (value : Value) (key : Key) :
    constantOn keys value key = if key ∈ keys then some value else none := by
  rfl

@[simp] theorem constantOn_domain {Key Value : Type} [DecidableEq Key]
    (keys : List Key) (value : Value) :
    (constantOn keys value).domain = deduplicated keys := by
  rfl

def install {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key : Key) (value : Value) :
    FiniteStore Key Value :=
  { lookup := fun candidate =>
      if candidate = key then some value else store candidate
    domain := if key ∈ store.domain then store.domain else key :: store.domain
    domainNodup := by
      by_cases present : key ∈ store.domain
      · simpa [present] using store.domainNodup
      · simp [present, store.domainNodup]
    lookupDefinedIffMem := by
      intro candidate
      by_cases atKey : candidate = key
      · subst candidate
        by_cases present : key ∈ store.domain <;> simp [present]
      · by_cases present : key ∈ store.domain
        · simp [atKey, present, store.lookupDefinedIffMem candidate]
        · simp [atKey, present, store.lookupDefinedIffMem candidate] }

@[simp] theorem install_at {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key : Key) (value : Value) :
    (store.install key value) key = some value := by
  simp [install]

@[simp] theorem install_away {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {key candidate : Key} (value : Value)
    (away : candidate ≠ key) :
    (store.install key value) candidate = store candidate := by
  simp [install, away]

/-- Remove exactly one key.  Unlike installing a new key, erasure preserves
    the relative order of every surviving domain entry. -/
def erase {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key : Key) : FiniteStore Key Value :=
  { lookup := fun candidate =>
      if candidate = key then none else store candidate
    domain := store.domain.filter fun candidate => decide (candidate ≠ key)
    domainNodup := store.domainNodup.filter _
    lookupDefinedIffMem := by
      intro candidate
      by_cases atKey : candidate = key
      · subst candidate
        simp
      · simp [atKey, store.lookupDefinedIffMem candidate] }

@[simp] theorem erase_at {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key : Key) :
    (store.erase key) key = none := by
  simp [erase]

@[simp] theorem erase_away {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {key candidate : Key}
    (away : candidate ≠ key) :
    (store.erase key) candidate = store candidate := by
  simp [erase, away]

@[simp] theorem mem_erase_domain_iff {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key candidate : Key) :
    candidate ∈ (store.erase key).domain ↔
      candidate ∈ store.domain ∧ candidate ≠ key := by
  simp [erase]

@[simp] theorem mem_install_domain_iff {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key candidate : Key) (value : Value) :
    candidate ∈ (store.install key value).domain ↔
      candidate = key ∨ candidate ∈ store.domain := by
  by_cases atKey : candidate = key
  · subst candidate
    by_cases present : key ∈ store.domain <;> simp [install, present]
  · by_cases present : key ∈ store.domain <;>
      simp [install, atKey, present]

@[simp] theorem mem_domain_iff {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key : Key) :
    key ∈ store.domain ↔ store key ≠ none :=
  (store.lookupDefinedIffMem key).symm

theorem mem_domain_of_lookup_eq_some {Key Value : Type} [DecidableEq Key]
    {store : FiniteStore Key Value} {key : Key} {value : Value}
    (lookup : store key = some value) : key ∈ store.domain := by
  rw [store.mem_domain_iff]
  simp [lookup]

theorem exists_value_of_mem_domain {Key Value : Type} [DecidableEq Key]
    {store : FiniteStore Key Value} {key : Key}
    (member : key ∈ store.domain) : ∃ value, store key = some value := by
  have defined : store key ≠ none := (store.mem_domain_iff key).mp member
  cases result : store key with
  | none => contradiction
  | some value => exact ⟨value, rfl⟩

/-- Pointwise value transformation preserving the exact key domain. -/
def mapValues {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (transform : Key → Value → Value) :
    FiniteStore Key Value :=
  { lookup := fun key => (store key).map (transform key)
    domain := store.domain
    domainNodup := store.domainNodup
    lookupDefinedIffMem := by
      intro key
      cases result : store key with
      | none =>
          have absent : key ∉ store.domain := by
            intro member
            have defined := (store.lookupDefinedIffMem key).mpr member
            exact defined (by simpa using result)
          simp [absent]
      | some value =>
          have member : key ∈ store.domain :=
            store.mem_domain_of_lookup_eq_some result
          simp [member] }

@[simp] theorem mapValues_apply {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (transform : Key → Value → Value)
    (key : Key) :
    (store.mapValues transform) key = (store key).map (transform key) := by
  rfl

/-- Restrict a store to keys accepted by an executable predicate. -/
def retainKeys {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (keep : Key → Bool) :
    FiniteStore Key Value :=
  { lookup := fun key => if keep key then store key else none
    domain := store.domain.filter keep
    domainNodup := store.domainNodup.filter keep
    lookupDefinedIffMem := by
      intro key
      cases retained : keep key with
      | false => simp [retained]
      | true =>
        simp only [retained, ite_true, List.mem_filter]
        rw [store.lookupDefinedIffMem key]
        simp }

@[simp] theorem retainKeys_apply {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (keep : Key → Bool) (key : Key) :
    store.retainKeys keep key = if keep key then store key else none := by
  rfl

@[simp] theorem mem_retainKeys_domain_iff
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (keep : Key → Bool) (key : Key) :
    key ∈ (store.retainKeys keep).domain ↔
      key ∈ store.domain ∧ keep key = true := by
  change key ∈ store.domain.filter keep ↔ _
  simp

theorem retainKeys_lookup_eq_some_iff
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (keep : Key → Bool)
    (key : Key) (value : Value) :
    store.retainKeys keep key = some value ↔
      store key = some value ∧ keep key = true := by
  cases retained : keep key <;> simp [retainKeys, retained]

theorem extensional_eq {Key Value : Type} [DecidableEq Key]
    {left right : FiniteStore Key Value}
    (lookupEqual : ∀ key, left key = right key)
    (domainEqual : left.domain = right.domain) : left = right := by
  cases left with
  | mk leftLookup leftDomain leftNodup leftDefined =>
      cases right with
      | mk rightLookup rightDomain rightNodup rightDefined =>
          simp only [FiniteStore.mk.injEq]
          exact ⟨funext lookupEqual, domainEqual⟩

theorem retainKeys_eq_self {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (keep : Key → Bool)
    (allKept : ∀ key, key ∈ store.domain → keep key = true) :
    store.retainKeys keep = store := by
  apply extensional_eq
  · intro key
    by_cases member : key ∈ store.domain
    · simp [retainKeys, allKept key member]
    · have absent : store key = none := by
        cases result : store key with
        | none => rfl
        | some value =>
            exfalso
            exact member (store.mem_domain_of_lookup_eq_some result)
      rw [retainKeys_apply, absent]
      cases keep key <;> rfl
  · change store.domain.filter keep = store.domain
    exact List.filter_eq_self.mpr allKept

/-- Equality of finite maps as maps, deliberately ignoring executable domain
    order.  Independent fresh insertions can choose different list orders
    while denoting exactly the same store. -/
def LookupEquivalent {Key Value : Type} [DecidableEq Key]
    (left right : FiniteStore Key Value) : Prop :=
  ∀ key, left key = right key

theorem LookupEquivalent.refl {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) : store.LookupEquivalent store := by
  intro key
  rfl

theorem LookupEquivalent.symm {Key Value : Type} [DecidableEq Key]
    {left right : FiniteStore Key Value}
    (equivalent : left.LookupEquivalent right) :
    right.LookupEquivalent left := by
  intro key
  exact (equivalent key).symm

theorem LookupEquivalent.trans {Key Value : Type} [DecidableEq Key]
    {first second third : FiniteStore Key Value}
    (left : first.LookupEquivalent second)
    (right : second.LookupEquivalent third) :
    first.LookupEquivalent third := by
  intro key
  exact (left key).trans (right key)

theorem LookupEquivalent.install {Key Value : Type} [DecidableEq Key]
    {left right : FiniteStore Key Value} (equivalent : left.LookupEquivalent right)
    (key : Key) (value : Value) :
    (left.install key value).LookupEquivalent (right.install key value) := by
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    simp
  · simp [same, equivalent candidate]

theorem LookupEquivalent.erase {Key Value : Type} [DecidableEq Key]
    {left right : FiniteStore Key Value} (equivalent : left.LookupEquivalent right)
    (key : Key) : (left.erase key).LookupEquivalent (right.erase key) := by
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    simp
  · simp [same, equivalent candidate]

/-- Boolean equality of finite-store supports, independent of executable
    domain order and of the stores' value types. -/
def sameDomain {Key LeftValue RightValue : Type} [DecidableEq Key]
    (left : FiniteStore Key LeftValue) (right : FiniteStore Key RightValue) :
    Bool :=
  left.domain.all (fun key => (right key).isSome) &&
    right.domain.all (fun key => (left key).isSome)

/-- Universal checks over an exact finite-store domain are extensional in
    both the store and the checked predicate. -/
theorem LookupEquivalent.all_domain_eq {Key Value : Type} [DecidableEq Key]
    {left right : FiniteStore Key Value}
    (equivalent : left.LookupEquivalent right)
    {leftPredicate rightPredicate : Key → Bool}
    (predicateEquivalent : ∀ key,
      leftPredicate key = rightPredicate key) :
    left.domain.all leftPredicate = right.domain.all rightPredicate := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro leftAll
    apply List.all_eq_true.mpr
    intro key rightMember
    have rightDefined : right key ≠ none :=
      (right.lookupDefinedIffMem key).mpr rightMember
    have leftDefined : left key ≠ none := by
      rw [equivalent key]
      exact rightDefined
    have leftMember : key ∈ left.domain :=
      (left.lookupDefinedIffMem key).mp leftDefined
    rw [← predicateEquivalent key]
    exact (List.all_eq_true.mp leftAll) key leftMember
  · intro rightAll
    apply List.all_eq_true.mpr
    intro key leftMember
    have leftDefined : left key ≠ none :=
      (left.lookupDefinedIffMem key).mpr leftMember
    have rightDefined : right key ≠ none := by
      rw [← equivalent key]
      exact leftDefined
    have rightMember : key ∈ right.domain :=
      (right.lookupDefinedIffMem key).mp rightDefined
    rw [predicateEquivalent key]
    exact (List.all_eq_true.mp rightAll) key rightMember

theorem sameDomain_eq_of_lookupEquivalent
    {Key LeftValue RightValue : Type} [DecidableEq Key]
    {left₁ left₂ : FiniteStore Key LeftValue}
    {right₁ right₂ : FiniteStore Key RightValue}
    (leftEquivalent : left₁.LookupEquivalent left₂)
    (rightEquivalent : right₁.LookupEquivalent right₂) :
    sameDomain left₁ right₁ = sameDomain left₂ right₂ := by
  have forward := leftEquivalent.all_domain_eq
    (leftPredicate := fun key => (right₁ key).isSome)
    (rightPredicate := fun key => (right₂ key).isSome)
    (fun key => congrArg Option.isSome (rightEquivalent key))
  have backward := rightEquivalent.all_domain_eq
    (leftPredicate := fun key => (left₁ key).isSome)
    (rightPredicate := fun key => (left₂ key).isSome)
    (fun key => congrArg Option.isSome (leftEquivalent key))
  simp [sameDomain, forward, backward]

theorem install_distinct_commute_lookup
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {first second : Key}
    (different : first ≠ second) (firstValue secondValue : Value) :
    LookupEquivalent
      ((store.install first firstValue).install second secondValue)
      ((store.install second secondValue).install first firstValue) := by
  intro key
  by_cases atFirst : key = first
  · subst key
    simp [different]
  · by_cases atSecond : key = second
    · subst key
      simp [different.symm]
    · simp [atFirst, atSecond]

theorem install_distinct_commute_of_mem
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {first second : Key}
    (different : first ≠ second)
    (firstPresent : first ∈ store.domain)
    (secondPresent : second ∈ store.domain)
    (firstValue secondValue : Value) :
    (store.install first firstValue).install second secondValue =
      (store.install second secondValue).install first firstValue := by
  apply extensional_eq
  · exact store.install_distinct_commute_lookup different firstValue secondValue
  · simp [install, firstPresent, secondPresent]

theorem install_distinct_commute_of_left_mem
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {first second : Key}
    (different : first ≠ second) (firstPresent : first ∈ store.domain)
    (firstValue secondValue : Value) :
    (store.install first firstValue).install second secondValue =
      (store.install second secondValue).install first firstValue := by
  apply extensional_eq
  · exact store.install_distinct_commute_lookup different firstValue secondValue
  · by_cases secondPresent : second ∈ store.domain <;>
      simp [install, firstPresent, secondPresent, different]

theorem install_same_key_overwrites
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (key : Key) (firstValue secondValue : Value) :
    (store.install key firstValue).install key secondValue =
      store.install key secondValue := by
  apply extensional_eq
  · intro candidate
    by_cases atKey : candidate = key
    · subst candidate
      simp
    · simp [atKey]
  · by_cases present : key ∈ store.domain <;> simp [install, present]

theorem erase_distinct_commute
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {first second : Key}
    (different : first ≠ second) :
    (store.erase first).erase second = (store.erase second).erase first := by
  apply extensional_eq
  · intro key
    by_cases atFirst : key = first <;>
      by_cases atSecond : key = second <;>
      simp [atFirst, atSecond, erase, different.symm]
  · simp only [erase, List.filter_filter]
    congr 1
    funext key
    exact Bool.and_comm _ _

theorem install_erase_distinct_commute_of_mem
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {installed erased : Key}
    (different : installed ≠ erased)
    (installedPresent : installed ∈ store.domain) (value : Value) :
    (store.install installed value).erase erased =
      (store.erase erased).install installed value := by
  apply extensional_eq
  · intro key
    by_cases atInstalled : key = installed
    · subst key
      simp [different]
    · by_cases atErased : key = erased
      · subst key
        simp [atInstalled]
      · simp [atInstalled, atErased]
  · simp [install, erase, installedPresent, different]

theorem install_erase_distinct_commute_lookup
    {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) {installed erased : Key}
    (different : installed ≠ erased) (value : Value) :
    LookupEquivalent
      ((store.install installed value).erase erased)
      ((store.erase erased).install installed value) := by
  intro key
  by_cases atInstalled : key = installed
  · subst key
    simp [different]
  · by_cases atErased : key = erased
    · subst key
      simp [atInstalled]
    · simp [atInstalled, atErased]

/-- Values of all defined entries, in domain order. -/
def values {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) : List Value :=
  store.domain.filterMap fun key => store key

@[simp] theorem mem_values_iff {Key Value : Type} [DecidableEq Key]
    (store : FiniteStore Key Value) (value : Value) :
    value ∈ store.values ↔ ∃ key, store key = some value := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨key, _inDomain, lookup⟩
    exact ⟨key, lookup⟩
  · rintro ⟨key, lookup⟩
    apply List.mem_filterMap.mpr
    exact ⟨key, store.mem_domain_of_lookup_eq_some lookup, lookup⟩

end FiniteStore
end Newspeak
