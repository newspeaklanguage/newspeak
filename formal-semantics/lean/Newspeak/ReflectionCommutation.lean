import Newspeak.ReflectionSourceImage
import Newspeak.ReflectionRuntimePreparation

namespace Newspeak

/-!
# Transaction commutation algebra

This module isolates the list-permutation argument used by reflection M6 from
the representation of any particular reflective state.  Concrete command
families need prove only the adjacent-pair equation below.  The final theorem
then supplies order independence for every permutation of a pairwise
independent transaction.
-/

/-- Sequentially apply a partial command transformer.  The distinct name is
    intentional: this is the family-independent algebra, not any of the
    concrete source, heap, activation, or debugger phase functions. -/
def applyOptionalCommandSequence {State Command : Type}
    (applyOne : State → Command → Option State) :
    State → List Command → Option State
  | state, [] => some state
  | state, command :: remaining => do
      let updated ← applyOne state command
      applyOptionalCommandSequence applyOne updated remaining

/-- Two commands commute when swapping them preserves both failure and the
    exact successful state, from every input state. -/
def OptionalCommandsCommute {State Command : Type}
    (applyOne : State → Command → Option State)
    (first second : Command) : Prop :=
  ∀ state,
    (do
      let afterFirst ← applyOne state first
      applyOne afterFirst second) =
    (do
      let afterSecond ← applyOne state second
      applyOne afterSecond first)

theorem OptionalCommandsCommute.of_left_failure
    {State Command : Type} {applyOne : State → Command → Option State}
    {first second : Command} (fails : ∀ state, applyOne state first = none) :
    OptionalCommandsCommute applyOne first second := by
  intro state
  simp [fails]

theorem OptionalCommandsCommute.of_right_failure
    {State Command : Type} {applyOne : State → Command → Option State}
    {first second : Command} (fails : ∀ state, applyOne state second = none) :
    OptionalCommandsCommute applyOne first second := by
  intro state
  simp [fails]

theorem OptionalCommandsCommute.of_success_and_applicability
    {State Command : Type} {applyOne : State → Command → Option State}
    {first second : Command}
    (firstApplicableAfterSecond : ∀ {before after},
      applyOne before second = some after →
      (applyOne before first).isSome = (applyOne after first).isSome)
    (secondApplicableAfterFirst : ∀ {before after},
      applyOne before first = some after →
      (applyOne before second).isSome = (applyOne after second).isSome)
    (successCommutes : ∀ state,
      (applyOne state first).isSome = true →
      (applyOne state second).isSome = true →
      (do
        let afterFirst ← applyOne state first
        applyOne afterFirst second) =
      (do
        let afterSecond ← applyOne state second
        applyOne afterSecond first)) :
    OptionalCommandsCommute applyOne first second := by
  intro state
  cases firstResult : applyOne state first with
  | none =>
      cases secondResult : applyOne state second with
      | none => simp [firstResult, secondResult]
      | some afterSecond =>
          have applicability := firstApplicableAfterSecond secondResult
          rw [firstResult] at applicability
          cases afterResult : applyOne afterSecond first with
          | none => simp [firstResult, secondResult, afterResult]
          | some final => simp [afterResult] at applicability
  | some afterFirst =>
      cases secondResult : applyOne state second with
      | none =>
          have applicability := secondApplicableAfterFirst firstResult
          rw [secondResult] at applicability
          cases afterResult : applyOne afterFirst second with
          | none => simp [firstResult, secondResult, afterResult]
          | some final => simp [afterResult] at applicability
      | some afterSecond =>
          simpa [firstResult, secondResult] using
            successCommutes state (by simp [firstResult])
              (by simp [secondResult])

def OptionalCommandsCommuteUnder {State Command : Type}
    (invariant : State → Prop) (applyOne : State → Command → Option State)
    (first second : Command) : Prop :=
  ∀ state, invariant state →
    (do
      let afterFirst ← applyOne state first
      applyOne afterFirst second) =
    (do
      let afterSecond ← applyOne state second
      applyOne afterSecond first)

def OptionalCommandPreserves {State Command : Type}
    (invariant : State → Prop) (applyOne : State → Command → Option State)
    (command : Command) : Prop :=
  ∀ before after, invariant before → applyOne before command = some after →
    invariant after

theorem applyOptionalCommandSequence_preserves
    {State Command : Type} {invariant : State → Prop}
    {applyOne : State → Command → Option State}
    (preserves : ∀ command,
      OptionalCommandPreserves invariant applyOne command)
    {before after : State} (commands : List Command)
    (valid : invariant before)
    (result : applyOptionalCommandSequence applyOne before commands = some after) :
    invariant after := by
  induction commands generalizing before after with
  | nil =>
      simp [applyOptionalCommandSequence] at result
      subst after
      exact valid
  | cons command remaining inductionHypothesis =>
      simp only [applyOptionalCommandSequence] at result
      cases commandResult : applyOne before command with
      | none => simp [commandResult] at result
      | some updated =>
          simp [commandResult] at result
          exact inductionHypothesis
            (preserves command before updated valid commandResult) result

/-- Extensionality of a partial command with respect to an observational
    state relation. -/
def OptionalCommandRespects {State Command : Type}
    (related : State → State → Prop)
    (applyOne : State → Command → Option State) (command : Command) : Prop :=
  ∀ {left right}, related left right →
    OptionalResultsRelated related (applyOne left command)
      (applyOne right command)

/-- Commutation modulo an observational relation.  This is needed for fresh
    finite-store insertions, whose lookup behavior agrees while their private
    executable-domain order may differ. -/
def OptionalCommandsCommuteModulo {State Command : Type}
    (related : State → State → Prop)
    (applyOne : State → Command → Option State)
    (first second : Command) : Prop :=
  ∀ state,
    OptionalResultsRelated related
      (do
        let afterFirst ← applyOne state first
        applyOne afterFirst second)
      (do
        let afterSecond ← applyOne state second
        applyOne afterSecond first)

theorem OptionalCommandsCommute.to_modulo
    {State Command : Type} {related : State → State → Prop}
    (relatedReflexive : ∀ state, related state state)
    {applyOne : State → Command → Option State} {first second : Command}
    (commute : OptionalCommandsCommute applyOne first second) :
    OptionalCommandsCommuteModulo related applyOne first second := by
  intro state
  rw [commute state]
  cases result : (do
    let afterSecond ← applyOne state second
    applyOne afterSecond first) with
  | none => exact .bothFailed
  | some final => exact .bothSucceeded (relatedReflexive final)

theorem OptionalCommandsCommuteModulo.of_success_and_applicability
    {State Command : Type} {related : State → State → Prop}
    {applyOne : State → Command → Option State} {first second : Command}
    (firstApplicableAfterSecond : ∀ {before after},
      applyOne before second = some after →
      (applyOne before first).isSome = (applyOne after first).isSome)
    (secondApplicableAfterFirst : ∀ {before after},
      applyOne before first = some after →
      (applyOne before second).isSome = (applyOne after second).isSome)
    (successCommutes : ∀ state,
      (applyOne state first).isSome = true →
      (applyOne state second).isSome = true →
      OptionalResultsRelated related
        (do
          let afterFirst ← applyOne state first
          applyOne afterFirst second)
        (do
          let afterSecond ← applyOne state second
          applyOne afterSecond first)) :
    OptionalCommandsCommuteModulo related applyOne first second := by
  intro state
  cases firstResult : applyOne state first with
  | none =>
      cases secondResult : applyOne state second with
      | none => simpa [firstResult, secondResult] using
          (OptionalResultsRelated.bothFailed :
            OptionalResultsRelated related none none)
      | some afterSecond =>
          have applicability := firstApplicableAfterSecond secondResult
          rw [firstResult] at applicability
          cases afterResult : applyOne afterSecond first with
          | none => simpa [firstResult, secondResult, afterResult] using
              (OptionalResultsRelated.bothFailed :
                OptionalResultsRelated related none none)
          | some final => simp [afterResult] at applicability
  | some afterFirst =>
      cases secondResult : applyOne state second with
      | none =>
          have applicability := secondApplicableAfterFirst firstResult
          rw [secondResult] at applicability
          cases afterResult : applyOne afterFirst second with
          | none => simpa [firstResult, secondResult, afterResult] using
              (OptionalResultsRelated.bothFailed :
                OptionalResultsRelated related none none)
          | some final => simp [afterResult] at applicability
      | some afterSecond =>
          simpa [firstResult, secondResult] using
            successCommutes state (by simp [firstResult])
              (by simp [secondResult])

/-- State-specific commutation for concrete source edits.  Applicability is a
    property of the identified source image, whereas the generic permutation
    theorem above uses the stronger all-states equation. -/
def SourceCodeCommandsCommuteAt (source : IdentifiedSourceImage)
    (first second : ReflectionCommand) : Prop :=
  (do
    let afterFirst ← source.patchSourceCodeCommand first
    afterFirst.patchSourceCodeCommand second) =
  (do
    let afterSecond ← source.patchSourceCodeCommand second
    afterSecond.patchSourceCodeCommand first)

def ClassGraphCommandsCommuteAt (heap : Heap)
    (first second : ReflectionCommand) : Prop :=
  (do
    let afterFirst ← applyClassGraphCommand heap first
    applyClassGraphCommand afterFirst second) =
  (do
    let afterSecond ← applyClassGraphCommand heap second
    applyClassGraphCommand afterSecond first)

def ObjectClassCommandsCommuteAt (heap : Heap)
    (first second : ReflectionCommand) : Prop :=
  (do
    let afterFirst ← applyObjectClassCommand heap first
    applyObjectClassCommand afterFirst second) =
  (do
    let afterSecond ← applyObjectClassCommand heap second
    applyObjectClassCommand afterSecond first)

def ObjectSlotCommandsCommuteAt (program : Program) (heap : Heap)
    (first second : ReflectionCommand) : Prop :=
  (do
    let afterFirst ← applyReflectiveObjectSlotCommand program heap first
    applyReflectiveObjectSlotCommand program afterFirst second) =
  (do
    let afterSecond ← applyReflectiveObjectSlotCommand program heap second
    applyReflectiveObjectSlotCommand program afterSecond first)

noncomputable def ActivationCommandsCommuteAt (heap : Heap)
    (first second : ReflectionCommand) : Prop :=
  (do
    let afterFirst ← applyActivationCommand heap first
    applyActivationCommand afterFirst second) =
  (do
    let afterSecond ← applyActivationCommand heap second
    applyActivationCommand afterSecond first)

def DebuggerCommandsCommuteAt (materialize : StackTemplateMaterializer)
    (program : Program) (requester : ActorId) (world : ActorWorld)
    (first second : ReflectionCommand) : Prop :=
  (do
    let afterFirst ←
      applyDebuggerCommand materialize program requester world first
    applyDebuggerCommand materialize program requester afterFirst second) =
  (do
    let afterSecond ←
      applyDebuggerCommand materialize program requester world second
    applyDebuggerCommand materialize program requester afterSecond first)

def ActorStoreDomainsCoherent (world : ActorWorld) : Prop :=
  world.runStates.domain = world.actorAllocations.domain

theorem ActorStoreDomainsCoherent.allocation_member_of_runState
    {world : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    {actor : ActorId} {state : ActorRunState}
    (present : world.runStates actor = some state) :
    actor ∈ world.actorAllocations.domain := by
  rw [← coherent]
  exact world.runStates.mem_domain_of_lookup_eq_some present

theorem ActorStoreDomainsCoherent.runState_member_of_allocation
    {world : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    {actor : ActorId} {allocation : AllocationState}
    (present : world.actorAllocations actor = some allocation) :
    actor ∈ world.runStates.domain := by
  rw [coherent]
  exact world.actorAllocations.mem_domain_of_lookup_eq_some present

theorem ActorStoreDomainsCoherent.replaceActorAllocationCoherently
    {world : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    {actor : ActorId} {oldAllocation newAllocation : AllocationState}
    (present : world.actorAllocations actor = some oldAllocation) :
    ActorStoreDomainsCoherent
      (world.replaceActorAllocationCoherently actor newAllocation) := by
  have allocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some present
  have runMember := coherent.runState_member_of_allocation present
  rcases world.runStates.exists_value_of_mem_domain runMember with
    ⟨state, stateResult⟩
  cases state <;>
    simp [ActorStoreDomainsCoherent,
      ActorWorld.replaceActorAllocationCoherently, stateResult,
      FiniteStore.install, allocationMember, runMember] <;>
    exact coherent

theorem ActorStoreDomainsCoherent.updateHeapAt
    {world after : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    (location : HeapLocation) (update : Heap → Option Heap)
    (result : world.updateHeapAt location update = some after) :
    ActorStoreDomainsCoherent after := by
  cases location with
  | shared =>
      unfold ActorWorld.updateHeapAt at result
      cases heapResult : update world.valueHeap with
      | none => simp [heapResult] at result
      | some heap =>
          simp [heapResult] at result
          subst after
          exact coherent
  | actor actor =>
      unfold ActorWorld.updateHeapAt at result
      cases allocationResult : world.actorAllocations actor with
      | none => simp [allocationResult] at result
      | some allocation =>
          cases heapResult : update allocation.heap with
          | none => simp [allocationResult, heapResult] at result
          | some heap =>
              simp [allocationResult, heapResult] at result
              subst after
              exact coherent.replaceActorAllocationCoherently allocationResult

theorem ActorStoreDomainsCoherent.updateHeapAtAfterLocation
    {world after : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    (location : Option HeapLocation) (update : Heap → Option Heap)
    (result : (location.bind fun found => world.updateHeapAt found update) =
      some after) : ActorStoreDomainsCoherent after := by
  cases location with
  | none => simp at result
  | some found =>
      simp at result
      exact coherent.updateHeapAt found update result

theorem ActorWorld.firstActorHeapSatisfying_of_actorAllocations_eq
    {left right : ActorWorld}
    (equal : left.actorAllocations = right.actorAllocations)
    (accept : Heap → Bool) (actors : List ActorId) :
    left.firstActorHeapSatisfying accept actors =
      right.firstActorHeapSatisfying accept actors := by
  induction actors with
  | nil => rfl
  | cons actor remaining inductionHypothesis =>
      simp [ActorWorld.firstActorHeapSatisfying, equal,
        inductionHypothesis]

theorem ActorWorld.firstActorHeapSatisfying_replaceActorAllocationCoherently
    (world : ActorWorld) (accept : Heap → Bool) (actors : List ActorId)
    (actor : ActorId) {oldAllocation : AllocationState}
    (newAllocation : AllocationState)
    (present : world.actorAllocations actor = some oldAllocation)
    (acceptEqual : accept newAllocation.heap = accept oldAllocation.heap) :
    ActorWorld.firstActorHeapSatisfying
        (world.replaceActorAllocationCoherently actor newAllocation)
        accept actors =
      world.firstActorHeapSatisfying accept actors := by
  induction actors with
  | nil => rfl
  | cons candidate remaining inductionHypothesis =>
      by_cases atActor : candidate = actor
      · subst candidate
        simp only [ActorWorld.firstActorHeapSatisfying]
        rw [ActorWorld.replaceActorAllocationCoherently_table, present]
        simp [acceptEqual, inductionHypothesis]
      · have lookupAway :
            (world.replaceActorAllocationCoherently actor newAllocation).actorAllocations
                candidate =
              world.actorAllocations candidate := by
            simp [ActorWorld.replaceActorAllocationCoherently, atActor]
        simp [ActorWorld.firstActorHeapSatisfying, lookupAway,
          inductionHypothesis]

theorem ActorWorld.locateHeapSatisfying_updateHeapAt
    {world after : ActorWorld} (accept : Heap → Bool)
    (location : HeapLocation) (update : Heap → Option Heap)
    (preserves : ∀ before updated, update before = some updated →
      accept updated = accept before)
    (result : world.updateHeapAt location update = some after) :
    after.locateHeapSatisfying accept = world.locateHeapSatisfying accept := by
  cases location with
  | shared =>
      unfold ActorWorld.updateHeapAt at result
      cases heapResult : update world.valueHeap with
      | none => simp [heapResult] at result
      | some heap =>
          simp [heapResult] at result
          subst after
          unfold ActorWorld.locateHeapSatisfying
          rw [preserves world.valueHeap heap heapResult]
          have firstActorEqual :=
            ActorWorld.firstActorHeapSatisfying_of_actorAllocations_eq
              (left := { world with valueHeap := heap }) (right := world) rfl
              accept world.actorAllocations.domain
          rw [firstActorEqual]
  | actor actor =>
      unfold ActorWorld.updateHeapAt at result
      cases allocationResult : world.actorAllocations actor with
      | none => simp [allocationResult] at result
      | some allocation =>
          cases heapResult : update allocation.heap with
          | none => simp [allocationResult, heapResult] at result
          | some heap =>
              simp [allocationResult, heapResult] at result
              subst after
              have actorMember :=
                world.actorAllocations.mem_domain_of_lookup_eq_some
                  allocationResult
              let updatedAllocation : AllocationState :=
                { allocation with heap := heap }
              have domainEqual :
                  (world.replaceActorAllocationCoherently actor
                      updatedAllocation).actorAllocations.domain =
                    world.actorAllocations.domain := by
                simp [ActorWorld.replaceActorAllocationCoherently,
                  FiniteStore.install, actorMember]
              unfold ActorWorld.locateHeapSatisfying
              rw [domainEqual]
              rw [world.firstActorHeapSatisfying_replaceActorAllocationCoherently
                accept world.actorAllocations.domain actor updatedAllocation
                allocationResult (preserves allocation.heap heap heapResult)]
              simp [ActorWorld.replaceActorAllocationCoherently]
              rfl

theorem ActorWorld.replaceActorAllocationCoherently_same_overwrites
    (world : ActorWorld) (actor : ActorId)
    (first second : AllocationState) :
    ActorWorld.replaceActorAllocationCoherently
        (world.replaceActorAllocationCoherently actor first) actor second =
      world.replaceActorAllocationCoherently actor second := by
  cases stateResult : world.runStates actor with
  | none =>
      simp [ActorWorld.replaceActorAllocationCoherently, stateResult,
        FiniteStore.install_same_key_overwrites]
  | some state =>
      cases state <;>
        simp [ActorWorld.replaceActorAllocationCoherently, stateResult,
          FiniteStore.install_same_key_overwrites]

@[simp] theorem ActorWorld.replaceActorAllocationCoherently_table_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (allocation : AllocationState) :
    (world.replaceActorAllocationCoherently actor allocation).actorAllocations
        other = world.actorAllocations other := by
  simp [ActorWorld.replaceActorAllocationCoherently, different]

theorem ActorWorld.replaceActorAllocationCoherently_distinct_commutes
    (world : ActorWorld) {firstActor secondActor : ActorId}
    (different : firstActor ≠ secondActor)
    (firstAllocation secondAllocation : AllocationState)
    (firstPresent : world.actorAllocations firstActor = some firstAllocation)
    (secondPresent : world.actorAllocations secondActor =
      some secondAllocation)
    (firstReplacement secondReplacement : AllocationState) :
    ActorWorld.replaceActorAllocationCoherently
        (world.replaceActorAllocationCoherently firstActor firstReplacement)
        secondActor secondReplacement =
      ActorWorld.replaceActorAllocationCoherently
        (world.replaceActorAllocationCoherently secondActor secondReplacement)
        firstActor firstReplacement := by
  have firstAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some firstPresent
  have secondAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some secondPresent
  have allocationStoresCommute :=
    world.actorAllocations.install_distinct_commute_of_mem different
      firstAllocationMember secondAllocationMember firstReplacement
      secondReplacement
  cases firstStateResult : world.runStates firstActor with
  | none =>
      cases secondStateResult : world.runStates secondActor with
      | none =>
          simp [ActorWorld.replaceActorAllocationCoherently,
            firstStateResult, secondStateResult, different, different.symm,
            allocationStoresCommute]
      | some secondState =>
          cases secondState <;>
            simp [ActorWorld.replaceActorAllocationCoherently,
              firstStateResult, secondStateResult, different, different.symm,
              allocationStoresCommute]
  | some firstState =>
      cases secondStateResult : world.runStates secondActor with
      | none =>
          cases firstState <;>
            simp [ActorWorld.replaceActorAllocationCoherently,
              firstStateResult, secondStateResult, different, different.symm,
              allocationStoresCommute]
      | some secondState =>
          have firstRunMember :=
            world.runStates.mem_domain_of_lookup_eq_some firstStateResult
          have secondRunMember :=
            world.runStates.mem_domain_of_lookup_eq_some secondStateResult
          have runStoresCommute (firstReplacementState secondReplacementState :
              ActorRunState) :=
            world.runStates.install_distinct_commute_of_mem different
              firstRunMember secondRunMember firstReplacementState
              secondReplacementState
          cases firstState <;> cases secondState <;>
            simp [ActorWorld.replaceActorAllocationCoherently,
              firstStateResult, secondStateResult, different, different.symm,
              allocationStoresCommute, runStoresCommute]

theorem ActorWorld.updateHeapAt_same_location_commutes
    (world : ActorWorld) (location : HeapLocation)
    (first second : Heap → Option Heap)
    (commute : ∀ heap,
      (do let afterFirst ← first heap; second afterFirst) =
      (do let afterSecond ← second heap; first afterSecond)) :
    (do
      let afterFirst ← world.updateHeapAt location first
      afterFirst.updateHeapAt location second) =
    (do
      let afterSecond ← world.updateHeapAt location second
      afterSecond.updateHeapAt location first) := by
  cases location with
  | shared =>
      have diamond := commute world.valueHeap
      cases firstResult : first world.valueHeap with
      | none =>
          cases secondResult : second world.valueHeap with
          | none => simp [ActorWorld.updateHeapAt, firstResult, secondResult]
          | some afterSecond =>
              cases firstAfterSecondResult : first afterSecond <;>
                simp [ActorWorld.updateHeapAt, firstResult, secondResult,
                  firstAfterSecondResult] at diamond ⊢
      | some afterFirst =>
          cases secondAfterFirstResult : second afterFirst with
          | none =>
              cases secondResult : second world.valueHeap with
              | none =>
                  simp [ActorWorld.updateHeapAt, firstResult,
                    secondAfterFirstResult, secondResult]
              | some afterSecond =>
                  cases firstAfterSecondResult : first afterSecond <;>
                    simp [ActorWorld.updateHeapAt, firstResult,
                      secondAfterFirstResult, secondResult,
                      firstAfterSecondResult] at diamond ⊢
          | some finalFirst =>
              cases secondResult : second world.valueHeap with
              | none =>
                  simp [firstResult, secondAfterFirstResult, secondResult] at diamond
              | some afterSecond =>
                  cases firstAfterSecondResult : first afterSecond with
                  | none =>
                      simp [firstResult, secondAfterFirstResult, secondResult,
                        firstAfterSecondResult] at diamond
                  | some finalSecond =>
                      simp [firstResult, secondAfterFirstResult, secondResult,
                        firstAfterSecondResult] at diamond
                      subst finalSecond
                      simp [ActorWorld.updateHeapAt, firstResult,
                        secondAfterFirstResult, secondResult,
                        firstAfterSecondResult]
  | actor actor =>
      cases allocationResult : world.actorAllocations actor with
      | none => simp [ActorWorld.updateHeapAt, allocationResult]
      | some allocation =>
          have diamond := commute allocation.heap
          cases firstResult : first allocation.heap with
          | none =>
              cases secondResult : second allocation.heap with
              | none =>
                  simp [ActorWorld.updateHeapAt, allocationResult, firstResult,
                    secondResult]
              | some afterSecond =>
                  cases firstAfterSecondResult : first afterSecond <;>
                    simp [ActorWorld.updateHeapAt, allocationResult,
                      firstResult, secondResult, firstAfterSecondResult,
                      ActorWorld.replaceActorAllocationCoherently_table]
                      at diamond ⊢
          | some afterFirst =>
              cases secondAfterFirstResult : second afterFirst with
              | none =>
                  cases secondResult : second allocation.heap with
                  | none =>
                      simp [ActorWorld.updateHeapAt, allocationResult,
                        firstResult, secondAfterFirstResult, secondResult,
                        ActorWorld.replaceActorAllocationCoherently_table]
                  | some afterSecond =>
                      cases firstAfterSecondResult : first afterSecond <;>
                        simp [ActorWorld.updateHeapAt, allocationResult,
                          firstResult, secondAfterFirstResult, secondResult,
                          firstAfterSecondResult,
                          ActorWorld.replaceActorAllocationCoherently_table]
                          at diamond ⊢
              | some finalFirst =>
                  cases secondResult : second allocation.heap with
                  | none =>
                      simp [firstResult, secondAfterFirstResult, secondResult]
                        at diamond
                  | some afterSecond =>
                      cases firstAfterSecondResult : first afterSecond with
                      | none =>
                          simp [firstResult, secondAfterFirstResult,
                            secondResult, firstAfterSecondResult] at diamond
                      | some finalSecond =>
                          simp [firstResult, secondAfterFirstResult,
                            secondResult, firstAfterSecondResult] at diamond
                          subst finalSecond
                          simp [ActorWorld.updateHeapAt, allocationResult,
                            firstResult, secondAfterFirstResult, secondResult,
                            firstAfterSecondResult,
                            ActorWorld.replaceActorAllocationCoherently_table,
                            ActorWorld.replaceActorAllocationCoherently_same_overwrites]

theorem ActorWorld.updateHeapAt_distinct_locations_commute
    (world : ActorWorld) {firstLocation secondLocation : HeapLocation}
    (different : firstLocation ≠ secondLocation)
    (first second : Heap → Option Heap) :
    (do
      let afterFirst ← world.updateHeapAt firstLocation first
      afterFirst.updateHeapAt secondLocation second) =
    (do
      let afterSecond ← world.updateHeapAt secondLocation second
      afterSecond.updateHeapAt firstLocation first) := by
  cases firstLocation <;> cases secondLocation
  case shared.shared => exact False.elim (different rfl)
  case shared.actor secondActor =>
    cases allocationResult : world.actorAllocations secondActor with
    | none =>
        cases firstResult : first world.valueHeap <;>
          simp [ActorWorld.updateHeapAt, allocationResult, firstResult]
    | some allocation =>
        cases firstResult : first world.valueHeap <;>
          cases secondResult : second allocation.heap <;>
          simp [ActorWorld.updateHeapAt, allocationResult, firstResult,
            secondResult, ActorWorld.replaceActorAllocationCoherently]
  case actor.shared firstActor =>
    cases allocationResult : world.actorAllocations firstActor with
    | none =>
        cases secondResult : second world.valueHeap <;>
          simp [ActorWorld.updateHeapAt, allocationResult, secondResult]
    | some allocation =>
        cases firstResult : first allocation.heap <;>
          cases secondResult : second world.valueHeap <;>
          simp [ActorWorld.updateHeapAt, allocationResult, firstResult,
            secondResult, ActorWorld.replaceActorAllocationCoherently]
  case actor.actor firstActor secondActor =>
    have actorsDifferent : firstActor ≠ secondActor := by
      intro equal
      subst secondActor
      exact different rfl
    cases firstAllocationResult : world.actorAllocations firstActor with
    | none =>
        cases secondAllocationResult : world.actorAllocations secondActor with
        | none =>
            simp [ActorWorld.updateHeapAt, firstAllocationResult,
              secondAllocationResult]
        | some secondAllocation =>
            cases secondResult : second secondAllocation.heap <;>
              simp [ActorWorld.updateHeapAt, firstAllocationResult,
                secondAllocationResult, secondResult, actorsDifferent,
                actorsDifferent.symm,
                ActorWorld.replaceActorAllocationCoherently_table_away]
    | some firstAllocation =>
        cases secondAllocationResult : world.actorAllocations secondActor with
        | none =>
            cases firstResult : first firstAllocation.heap <;>
              simp [ActorWorld.updateHeapAt, firstAllocationResult,
                secondAllocationResult, firstResult,
                actorsDifferent, actorsDifferent.symm,
                ActorWorld.replaceActorAllocationCoherently_table_away]
        | some secondAllocation =>
            cases firstResult : first firstAllocation.heap with
            | none =>
                cases secondResult : second secondAllocation.heap <;>
                  simp [ActorWorld.updateHeapAt, firstAllocationResult,
                    secondAllocationResult, firstResult, secondResult,
                    actorsDifferent, actorsDifferent.symm,
                    ActorWorld.replaceActorAllocationCoherently]
            | some firstHeap =>
                cases secondResult : second secondAllocation.heap with
                | none =>
                    simp [ActorWorld.updateHeapAt, firstAllocationResult,
                      secondAllocationResult, firstResult, secondResult,
                      actorsDifferent, actorsDifferent.symm,
                      ActorWorld.replaceActorAllocationCoherently]
                | some secondHeap =>
                    simp [ActorWorld.updateHeapAt, firstAllocationResult,
                      secondAllocationResult, firstResult, secondResult,
                      actorsDifferent, actorsDifferent.symm,
                      ActorWorld.replaceActorAllocationCoherently_table_away]
                    exact
                      world.replaceActorAllocationCoherently_distinct_commutes
                        actorsDifferent firstAllocation secondAllocation
                        firstAllocationResult secondAllocationResult
                        { firstAllocation with heap := firstHeap }
                        { secondAllocation with heap := secondHeap }

def applyLocatedHeapUpdate (world : ActorWorld) (accept : Heap → Bool)
    (update : Heap → Option Heap) : Option ActorWorld := do
  let location ← world.locateHeapSatisfying accept
  world.updateHeapAt location update

theorem applyLocatedHeapUpdates_commute
    (world : ActorWorld) (firstAccept secondAccept : Heap → Bool)
    (firstUpdate secondUpdate : Heap → Option Heap)
    (firstPreservesSecond : ∀ before after,
      firstUpdate before = some after →
      secondAccept after = secondAccept before)
    (secondPreservesFirst : ∀ before after,
      secondUpdate before = some after →
      firstAccept after = firstAccept before)
    (sameHeapCommutes : ∀ heap,
      (do let afterFirst ← firstUpdate heap; secondUpdate afterFirst) =
      (do let afterSecond ← secondUpdate heap; firstUpdate afterSecond)) :
    (do
      let afterFirst ← applyLocatedHeapUpdate world firstAccept firstUpdate
      applyLocatedHeapUpdate afterFirst secondAccept secondUpdate) =
    (do
      let afterSecond ← applyLocatedHeapUpdate world secondAccept secondUpdate
      applyLocatedHeapUpdate afterSecond firstAccept firstUpdate) := by
  cases firstLocationResult : world.locateHeapSatisfying firstAccept with
  | none =>
      cases secondLocationResult : world.locateHeapSatisfying secondAccept with
      | none =>
          simp [applyLocatedHeapUpdate, firstLocationResult,
            secondLocationResult]
      | some secondLocation =>
          cases secondWorldResult :
              world.updateHeapAt secondLocation secondUpdate with
          | none =>
              simp [applyLocatedHeapUpdate, firstLocationResult,
                secondLocationResult, secondWorldResult]
          | some afterSecond =>
              have preserved := ActorWorld.locateHeapSatisfying_updateHeapAt
                firstAccept secondLocation secondUpdate secondPreservesFirst
                secondWorldResult
              rw [firstLocationResult] at preserved
              simp [applyLocatedHeapUpdate, firstLocationResult,
                secondLocationResult, secondWorldResult, preserved]
  | some firstLocation =>
      cases secondLocationResult : world.locateHeapSatisfying secondAccept with
      | none =>
          cases firstWorldResult :
              world.updateHeapAt firstLocation firstUpdate with
          | none =>
              simp [applyLocatedHeapUpdate, firstLocationResult,
                secondLocationResult, firstWorldResult]
          | some afterFirst =>
              have preserved := ActorWorld.locateHeapSatisfying_updateHeapAt
                secondAccept firstLocation firstUpdate firstPreservesSecond
                firstWorldResult
              rw [secondLocationResult] at preserved
              simp [applyLocatedHeapUpdate, firstLocationResult,
                secondLocationResult, firstWorldResult, preserved]
      | some secondLocation =>
          have leftReduction :
              (do
                let afterFirst ←
                  applyLocatedHeapUpdate world firstAccept firstUpdate
                applyLocatedHeapUpdate afterFirst secondAccept secondUpdate) =
              (do
                let afterFirst ←
                  world.updateHeapAt firstLocation firstUpdate
                afterFirst.updateHeapAt secondLocation secondUpdate) := by
            cases firstWorldResult :
                world.updateHeapAt firstLocation firstUpdate with
            | none =>
                simp [applyLocatedHeapUpdate, firstLocationResult,
                  firstWorldResult]
            | some afterFirst =>
                have preserved :=
                  ActorWorld.locateHeapSatisfying_updateHeapAt secondAccept
                    firstLocation firstUpdate firstPreservesSecond
                    firstWorldResult
                rw [secondLocationResult] at preserved
                simp [applyLocatedHeapUpdate, firstLocationResult,
                  firstWorldResult, preserved]
          have rightReduction :
              (do
                let afterSecond ←
                  applyLocatedHeapUpdate world secondAccept secondUpdate
                applyLocatedHeapUpdate afterSecond firstAccept firstUpdate) =
              (do
                let afterSecond ←
                  world.updateHeapAt secondLocation secondUpdate
                afterSecond.updateHeapAt firstLocation firstUpdate) := by
            cases secondWorldResult :
                world.updateHeapAt secondLocation secondUpdate with
            | none =>
                simp [applyLocatedHeapUpdate, secondLocationResult,
                  secondWorldResult]
            | some afterSecond =>
                have preserved :=
                  ActorWorld.locateHeapSatisfying_updateHeapAt firstAccept
                    secondLocation secondUpdate secondPreservesFirst
                    secondWorldResult
                rw [firstLocationResult] at preserved
                simp [applyLocatedHeapUpdate, secondLocationResult,
                  secondWorldResult, preserved]
          rw [leftReduction, rightReduction]
          by_cases sameLocation : firstLocation = secondLocation
          · subst secondLocation
            exact world.updateHeapAt_same_location_commutes firstLocation
              firstUpdate secondUpdate sameHeapCommutes
          · exact world.updateHeapAt_distinct_locations_commute sameLocation
              firstUpdate secondUpdate

theorem applyCohortClassGraphCommand_preserves_actorStoreDomains
    (command : ReflectionCommand) :
    OptionalCommandPreserves ActorStoreDomainsCoherent
      applyCohortClassGraphCommand command := by
  intro before after coherent result
  cases command <;> simp only [applyCohortClassGraphCommand,
    classGraphCommandClass?] at result
  all_goals try contradiction
  case changeSuperclass mirror classId superclass =>
    exact coherent.updateHeapAtAfterLocation _ _ result
  case changeClassEnclosingObject mirror classId enclosingObject =>
    exact coherent.updateHeapAtAfterLocation _ _ result

theorem applyCohortObjectClassCommand_preserves_actorStoreDomains
    (command : ReflectionCommand) :
    OptionalCommandPreserves ActorStoreDomainsCoherent
      applyCohortObjectClassCommand command := by
  intro before after coherent result
  cases command <;> simp only [applyCohortObjectClassCommand,
    objectClassCommandObject?] at result
  all_goals try contradiction
  case changeObjectClass mirror object classId =>
    exact coherent.updateHeapAtAfterLocation _ _ result

theorem applyCohortObjectSlotCommand_preserves_actorStoreDomains
    (program : Program) (command : ReflectionCommand) :
    OptionalCommandPreserves ActorStoreDomainsCoherent
      (applyCohortObjectSlotCommand program) command := by
  intro before after coherent result
  cases command <;> simp only [applyCohortObjectSlotCommand,
    objectSlotCommandObject?] at result
  all_goals try contradiction
  case objectSlotWrite mirror object slot value =>
    exact coherent.updateHeapAtAfterLocation _ _ result

theorem applyCohortActivationCommand_preserves_actorStoreDomains
    (command : ReflectionCommand) :
    OptionalCommandPreserves ActorStoreDomainsCoherent
      applyCohortActivationCommand command := by
  intro before after coherent result
  cases command <;> simp only [applyCohortActivationCommand,
    activationCommandActivation?] at result
  all_goals try contradiction
  case activationParameterWrite mirror activation parameter value =>
    exact coherent.updateHeapAtAfterLocation _ _ result
  case activationLocalWrite mirror activation slot value =>
    exact coherent.updateHeapAtAfterLocation _ _ result
  case changeActivationCurrentClass mirror activation classId =>
    exact coherent.updateHeapAtAfterLocation _ _ result
  case changeActivationContinuation mirror activation continuation =>
    exact coherent.updateHeapAtAfterLocation _ _ result
  case makeActivationUncontinuable mirror activation =>
    exact coherent.updateHeapAtAfterLocation _ _ result

theorem ActorStoreDomainsCoherent.transformActorHeaps
    {world after : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    (transform : Heap → Option Heap) (actors : List ActorId)
    (result : world.transformActorHeaps transform actors = some after) :
    ActorStoreDomainsCoherent after := by
  induction actors generalizing world after with
  | nil =>
      simp [ActorWorld.transformActorHeaps] at result
      subst after
      exact coherent
  | cons actor remaining inductionHypothesis =>
      simp only [ActorWorld.transformActorHeaps] at result
      cases allocationResult : world.actorAllocations actor with
      | none => simp [allocationResult] at result
      | some allocation =>
          cases heapResult : transform allocation.heap with
          | none => simp [allocationResult, heapResult] at result
          | some heap =>
              simp [allocationResult, heapResult] at result
              exact inductionHypothesis
                (coherent.replaceActorAllocationCoherently allocationResult)
                result

theorem ActorStoreDomainsCoherent.transformEveryHeap
    {world after : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    (transform : Heap → Option Heap)
    (result : world.transformEveryHeap transform = some after) :
    ActorStoreDomainsCoherent after := by
  unfold ActorWorld.transformEveryHeap at result
  cases sharedResult : transform world.valueHeap with
  | none => simp [sharedResult] at result
  | some shared =>
      simp [sharedResult] at result
      have updatedCoherent : ActorStoreDomainsCoherent
          { world with valueHeap := shared } := coherent
      exact updatedCoherent.transformActorHeaps transform
        world.actorAllocations.domain result

theorem ActorStoreDomainsCoherent.pauseRunningActor
    {world : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    {actor : ActorId} {state : ActorRunState}
    (present : world.runStates actor = some state)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) :
    ActorStoreDomainsCoherent
      (world.pauseRunningActor actor config reply event reason) := by
  have runMember := world.runStates.mem_domain_of_lookup_eq_some present
  simp [ActorStoreDomainsCoherent, ActorWorld.pauseRunningActor,
    FiniteStore.install, runMember]
  exact coherent

theorem ActorStoreDomainsCoherent.advanceRunningTurn
    {world : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    {actor : ActorId} {state : ActorRunState}
    (present : world.runStates actor = some state)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    ActorStoreDomainsCoherent
      (world.advanceRunningTurn actor config reply event) := by
  have runMember := world.runStates.mem_domain_of_lookup_eq_some present
  have allocationMember := coherent.allocation_member_of_runState present
  simp [ActorStoreDomainsCoherent, ActorWorld.advanceRunningTurn,
    FiniteStore.install, runMember, allocationMember]
  exact coherent

theorem ActorStoreDomainsCoherent.replacePausedActorConfiguration
    {world : ActorWorld} (coherent : ActorStoreDomainsCoherent world)
    {actor : ActorId} {state : ActorRunState}
    (present : world.runStates actor = some state)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) :
    ActorStoreDomainsCoherent
      (world.replacePausedActorConfiguration actor config reply event reason) := by
  have runMember := world.runStates.mem_domain_of_lookup_eq_some present
  have allocationMember := coherent.allocation_member_of_runState present
  simp [ActorStoreDomainsCoherent,
    ActorWorld.replacePausedActorConfiguration, FiniteStore.install,
    runMember, allocationMember]
  exact coherent

theorem applyDebuggerCommand_preserves_actorStoreDomains
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (command : ReflectionCommand) :
    OptionalCommandPreserves ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      command := by
  intro before after coherent result
  cases command <;> simp only [applyDebuggerCommand] at result
  all_goals try contradiction
  case pauseActor mirror actor reason =>
    cases stateResult : before.runStates actor with
    | none => simp [stateResult] at result
    | some state =>
        cases state with
        | idle => simp [stateResult] at result
        | pausedTurn => simp [stateResult] at result
        | runningTurn config reply event =>
            by_cases self : requester = actor
            · simp [stateResult, self] at result
            · cases stackResult : config.stack with
              | empty => simp [stateResult, self, stackResult] at result
              | push rest frame =>
                  simp [stateResult, self, stackResult] at result
                  subst after
                  exact coherent.pauseRunningActor stateResult config reply event
                    reason
  case replaceCurrentActorStack mirror actor template =>
    by_cases self : requester = actor
    · cases stateResult : before.runStates actor with
      | none => simp [self, stateResult] at result
      | some state =>
          cases state with
          | idle => simp [self, stateResult] at result
          | pausedTurn => simp [self, stateResult] at result
          | runningTurn config reply event =>
              cases materializedResult : materialize program config.allocation
                  config.stack template with
              | none => simp [self, stateResult, materializedResult] at result
              | some materialized =>
                  rcases materialized with ⟨allocation, stack, control⟩
                  simp [self, stateResult, materializedResult] at result
                  subst after
                  exact coherent.advanceRunningTurn stateResult _ reply event
    · simp [self] at result
  case replacePausedActorStack mirror actor token template =>
    cases stateResult : before.runStates actor with
    | none => simp [stateResult] at result
    | some state =>
        cases state with
        | idle => simp [stateResult] at result
        | runningTurn => simp [stateResult] at result
        | pausedTurn config reply event currentToken reason =>
            by_cases current : token = currentToken
            · cases materializedResult : materialize program config.allocation
                  config.stack template with
              | none => simp [stateResult, current, materializedResult] at result
              | some materialized =>
                  rcases materialized with ⟨allocation, stack, control⟩
                  simp [stateResult, current, materializedResult] at result
                  subst after
                  exact coherent.replacePausedActorConfiguration stateResult _
                    reply event reason
            · simp [stateResult, current] at result

  case resumePausedActorAtFullSpeed mirror actor token =>
    cases stateResult : before.runStates actor with
    | none => simp [stateResult] at result
    | some state =>
        cases state with
        | idle => simp [stateResult] at result
        | runningTurn => simp [stateResult] at result
        | pausedTurn config reply event currentToken reason =>
            by_cases current : token = currentToken
            · simp [stateResult, current] at result
              subst after
              exact coherent.advanceRunningTurn stateResult config reply event
            · simp [stateResult, current] at result
  case replaceAndResumePausedActorStack mirror actor token template =>
    cases stateResult : before.runStates actor with
    | none => simp [stateResult] at result
    | some state =>
        cases state with
        | idle => simp [stateResult] at result
        | runningTurn => simp [stateResult] at result
        | pausedTurn config reply event currentToken reason =>
            by_cases current : token = currentToken
            · cases materializedResult : materialize program config.allocation
                  config.stack template with
              | none => simp [stateResult, current, materializedResult] at result
              | some materialized =>
                  rcases materialized with ⟨allocation, stack, control⟩
                  simp [stateResult, current, materializedResult] at result
                  subst after
                  exact coherent.advanceRunningTurn stateResult _ reply event
            · simp [stateResult, current] at result

def DebuggerTransactionIndependent
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (transaction : List ReflectionCommand) : Prop :=
  (debuggerCommands transaction).Pairwise
    (OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command))

theorem applyDebuggerCommandSequence_eq_optional
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld)
    (commands : List ReflectionCommand) :
    applyDebuggerCommandSequence materialize program requester world commands =
      applyOptionalCommandSequence
        (fun current command =>
          applyDebuggerCommand materialize program requester current command)
        world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyDebuggerCommandSequence, applyOptionalCommandSequence]
      cases result :
          applyDebuggerCommand materialize program requester world command with
      | none => rfl
      | some updated => exact inductionHypothesis updated

theorem OptionalCommandsCommute.symmetric {State Command : Type}
    {applyOne : State → Command → Option State} {first second : Command}
    (commute : OptionalCommandsCommute applyOne first second) :
    OptionalCommandsCommute applyOne second first := by
  intro state
  exact (commute state).symm

theorem OptionalCommandsCommuteUnder.symmetric {State Command : Type}
    {invariant : State → Prop} {applyOne : State → Command → Option State}
    {first second : Command}
    (commute : OptionalCommandsCommuteUnder invariant applyOne first second) :
    OptionalCommandsCommuteUnder invariant applyOne second first := by
  intro state valid
  exact (commute state valid).symm

theorem OptionalCommandsCommuteModulo.symmetric {State Command : Type}
    {related : State → State → Prop}
    (relatedSymmetric : ∀ {left right}, related left right → related right left)
    {applyOne : State → Command → Option State} {first second : Command}
    (commute : OptionalCommandsCommuteModulo related applyOne first second) :
    OptionalCommandsCommuteModulo related applyOne second first := by
  intro state
  exact (commute state).symmetric relatedSymmetric

theorem compatibleCommands_cannot_share_location
    {first second : ReflectionCommand} {location : ReflectionWriteLocation}
    (compatible : ReflectionCommandsCompatible first second)
    (firstWrites : location ∈ first.writes)
    (secondWrites : location ∈ second.writes) : False :=
  compatible location firstWrites location secondWrites (.same location)

theorem compatibleActorStackCommands_have_distinct_actors
    {first second : ReflectionCommand} {firstActor secondActor : ActorId}
    (compatible : ReflectionCommandsCompatible first second)
    (firstWrites : .actorStack firstActor ∈ first.writes)
    (secondWrites : .actorStack secondActor ∈ second.writes) :
    firstActor ≠ secondActor := by
  intro equal
  subst secondActor
  exact compatibleCommands_cannot_share_location compatible firstWrites
    secondWrites

theorem debuggerActor?_writes_actorStack
    {command : ReflectionCommand} {actor : ActorId}
    (target : command.debuggerActor? = some actor) :
    .actorStack actor ∈ command.writes := by
  cases command <;> simp [ReflectionCommand.debuggerActor?] at target ⊢
  all_goals cases target
  all_goals simp [ReflectionCommand.writes]

theorem mintsPauseToken_writes_supply
    {command : ReflectionCommand}
    (mints : command.mintsPauseToken = true) :
    .pauseTokenSupply ∈ command.writes := by
  cases command <;> simp [ReflectionCommand.mintsPauseToken] at mints ⊢
  all_goals simp [ReflectionCommand.writes]

theorem replacesStack_writes_activationGraph
    {command : ReflectionCommand}
    (replaces : command.replacesStack = true) :
    .activationGraph ∈ command.writes := by
  cases command <;> simp [ReflectionCommand.replacesStack] at replaces ⊢
  all_goals simp [ReflectionCommand.writes]

theorem compatibleDebuggerCommands_have_distinct_actors
    {first second : ReflectionCommand} {firstActor secondActor : ActorId}
    (compatible : ReflectionCommandsCompatible first second)
    (firstTarget : first.debuggerActor? = some firstActor)
    (secondTarget : second.debuggerActor? = some secondActor) :
    firstActor ≠ secondActor :=
  compatibleActorStackCommands_have_distinct_actors compatible
    (debuggerActor?_writes_actorStack firstTarget)
    (debuggerActor?_writes_actorStack secondTarget)

theorem compatibleCommands_not_both_mint_pause_tokens
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second)
    (firstMints : first.mintsPauseToken = true) :
    second.mintsPauseToken = false := by
  cases result : second.mintsPauseToken with
  | false => rfl
  | true =>
      exact False.elim (compatibleCommands_cannot_share_location compatible
        (mintsPauseToken_writes_supply firstMints)
        (mintsPauseToken_writes_supply result))

theorem compatibleCommands_not_both_replace_stacks
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second)
    (firstReplaces : first.replacesStack = true) :
    second.replacesStack = false := by
  cases result : second.replacesStack with
  | false => rfl
  | true =>
      exact False.elim (compatibleCommands_cannot_share_location compatible
        (replacesStack_writes_activationGraph firstReplaces)
        (replacesStack_writes_activationGraph result))

theorem compatibleDebuggerCommands_classified
    {first second : ReflectionCommand}
    (firstKind : first.kind = .debugger)
    (secondKind : second.kind = .debugger)
    (compatible : ReflectionCommandsCompatible first second) :
    ∃ firstActor secondActor,
      first.debuggerActor? = some firstActor ∧
      second.debuggerActor? = some secondActor ∧
      firstActor ≠ secondActor ∧
      (first.mintsPauseToken = true → second.mintsPauseToken = false) ∧
      (second.mintsPauseToken = true → first.mintsPauseToken = false) ∧
      (first.replacesStack = true → second.replacesStack = false) ∧
      (second.replacesStack = true → first.replacesStack = false) := by
  have firstSome : first.debuggerActor?.isSome = true :=
    (ReflectionCommand.debuggerActor?_isSome_iff first).mpr firstKind
  have secondSome : second.debuggerActor?.isSome = true :=
    (ReflectionCommand.debuggerActor?_isSome_iff second).mpr secondKind
  cases firstTarget : first.debuggerActor? with
  | none => simp [firstTarget] at firstSome
  | some firstActor =>
      cases secondTarget : second.debuggerActor? with
      | none => simp [secondTarget] at secondSome
      | some secondActor =>
          refine ⟨firstActor, secondActor, rfl, rfl,
            compatibleDebuggerCommands_have_distinct_actors compatible
              firstTarget secondTarget, ?_, ?_, ?_, ?_⟩
          · exact compatibleCommands_not_both_mint_pause_tokens compatible
          · exact compatibleCommands_not_both_mint_pause_tokens
              compatible.symmetric
          · exact compatibleCommands_not_both_replace_stacks compatible
          · exact compatibleCommands_not_both_replace_stacks
              compatible.symmetric

theorem continuationTransferCommands_incompatible
    {firstMirror secondMirror : MirrorId} {firstActor secondActor : ActorId}
    {firstActivation secondActivation : ActivationId}
    {firstValue secondValue : ObjRef} :
    ¬ReflectionCommandsCompatible
      (.continueAtActivation firstMirror firstActor firstActivation firstValue)
      (.continueAtActivation secondMirror secondActor secondActivation
        secondValue) := by
  intro compatible
  exact compatibleCommands_cannot_share_location compatible
    (location := .activationGraph) (by simp [ReflectionCommand.writes])
    (by simp [ReflectionCommand.writes])

theorem activationRetirementAndContinuationTransfer_incompatible
    {retireMirror continueMirror : MirrorId} {actor : ActorId}
    {retired continued : ActivationId} {value : ObjRef} :
    ¬ReflectionCommandsCompatible
      (.makeActivationUncontinuable retireMirror retired)
      (.continueAtActivation continueMirror actor continued value) := by
  intro compatible
  exact compatibleCommands_cannot_share_location compatible
    (location := .activationGraph) (by simp [ReflectionCommand.writes])
    (by simp [ReflectionCommand.writes])

theorem activationRetirementAndActivationCommand_incompatible
    {retireMirror : MirrorId} {retired : ActivationId}
    {command : ReflectionCommand} (activationKind : command.kind = .activation) :
    ¬ReflectionCommandsCompatible
      (.makeActivationUncontinuable retireMirror retired) command := by
  rcases (ReflectionCommand.kind_eq_activation_iff command).mp activationKind with
    ⟨mirror, activation, parameter, value, rfl⟩ |
    ⟨mirror, activation, slot, value, rfl⟩ |
    ⟨mirror, activation, classId, rfl⟩ |
    ⟨mirror, activation, continuation, rfl⟩ |
    ⟨mirror, activation, rfl⟩
  · intro compatible
    exact compatible (.activationGraph) (by simp [ReflectionCommand.writes])
      (.activationField activation (.parameter parameter))
      (by simp [ReflectionCommand.writes]) (.graphField activation _)
  · intro compatible
    exact compatible (.activationGraph) (by simp [ReflectionCommand.writes])
      (.activationField activation (.local slot))
      (by simp [ReflectionCommand.writes]) (.graphField activation _)
  · intro compatible
    exact compatible (.activationGraph) (by simp [ReflectionCommand.writes])
      (.activationField activation .currentClass)
      (by simp [ReflectionCommand.writes]) (.graphField activation _)
  · intro compatible
    exact compatible (.activationGraph) (by simp [ReflectionCommand.writes])
      (.activationField activation .continuation)
      (by simp [ReflectionCommand.writes]) (.graphField activation _)
  · intro compatible
    exact compatibleCommands_cannot_share_location compatible
      (location := .activationGraph) (by simp [ReflectionCommand.writes])
      (by simp [ReflectionCommand.writes])

theorem pairwiseNonconflicting_continuationCommands_length_le_one
    {transaction : List ReflectionCommand}
    (nonconflicting :
      transaction.Pairwise ReflectionCommandsCompatible) :
    (continuationCommands transaction).length ≤ 1 := by
  have filteredPairwise :
      (continuationCommands transaction).Pairwise
        ReflectionCommandsCompatible :=
    nonconflicting.filter _
  cases filtered : continuationCommands transaction with
  | nil => simp
  | cons first remaining =>
      cases remaining with
      | nil => simp
      | cons second tail =>
          rw [filtered] at filteredPairwise
          have compatible : ReflectionCommandsCompatible first second :=
            (List.pairwise_cons.mp filteredPairwise).1 second (by simp)
          have firstMember : first ∈ continuationCommands transaction := by
            rw [filtered]
            simp
          have secondMember : second ∈ continuationCommands transaction := by
            rw [filtered]
            simp
          have firstKind : first.kind = .continuation := by
            have selected := (List.mem_filter.mp
              (show first ∈ transaction.filter
                (fun command => decide (command.kind = .continuation)) by
                  simpa [continuationCommands] using firstMember)).2
            cases first <;> simp [ReflectionCommand.kind] at selected ⊢
          have secondKind : second.kind = .continuation := by
            have selected := (List.mem_filter.mp
              (show second ∈ transaction.filter
                (fun command => decide (command.kind = .continuation)) by
                  simpa [continuationCommands] using secondMember)).2
            cases second <;> simp [ReflectionCommand.kind] at selected ⊢
          rcases (ReflectionCommand.kind_eq_continuation_iff first).mp firstKind with
            ⟨firstMirror, firstActor, firstActivation, firstValue, rfl⟩
          rcases (ReflectionCommand.kind_eq_continuation_iff second).mp secondKind with
            ⟨secondMirror, secondActor, secondActivation, secondValue, rfl⟩
          exact False.elim (continuationTransferCommands_incompatible compatible)

theorem continuationCommands_permutation_eq
    {original permuted : List ReflectionCommand}
    (nonconflicting :
      original.Pairwise ReflectionCommandsCompatible)
    (permutation : original.Perm permuted) :
    continuationCommands original = continuationCommands permuted := by
  have filteredPermutation :
      (continuationCommands original).Perm
        (continuationCommands permuted) := by
    exact permutation.filter _
  have short :=
    pairwiseNonconflicting_continuationCommands_length_le_one nonconflicting
  cases originalFiltered : continuationCommands original with
  | nil =>
      rw [originalFiltered] at filteredPermutation
      exact (filteredPermutation.symm.eq_nil).symm
  | cons command remaining =>
      cases remaining with
      | nil =>
          rw [originalFiltered] at filteredPermutation
          exact (filteredPermutation.symm.eq_singleton).symm
      | cons second tail =>
          rw [originalFiltered] at short
          simp at short

theorem continuationPhase_permutation_invariant
    {original permuted : List ReflectionCommand}
    (nonconflicting :
      original.Pairwise ReflectionCommandsCompatible)
    (permutation : original.Perm permuted) (world : ActorWorld) :
    world.applyContinuationTransferSequence (continuationCommands original) =
      world.applyContinuationTransferSequence
        (continuationCommands permuted) := by
  rw [continuationCommands_permutation_eq nonconflicting permutation]

theorem applyOptionalCommandSequence_adjacent_swap
    {State Command : Type} {applyOne : State → Command → Option State}
    {first second : Command}
    (commute : OptionalCommandsCommute applyOne first second)
    (state : State) (remaining : List Command) :
    applyOptionalCommandSequence applyOne state
        (first :: second :: remaining) =
      applyOptionalCommandSequence applyOne state
        (second :: first :: remaining) := by
  simp only [applyOptionalCommandSequence]
  rw [← bind_assoc, ← bind_assoc, commute state]

theorem applyOptionalCommandSequence_adjacent_swap_under
    {State Command : Type} {invariant : State → Prop}
    {applyOne : State → Command → Option State} {first second : Command}
    (commute : OptionalCommandsCommuteUnder invariant applyOne first second)
    (state : State) (valid : invariant state) (remaining : List Command) :
    applyOptionalCommandSequence applyOne state
        (first :: second :: remaining) =
      applyOptionalCommandSequence applyOne state
        (second :: first :: remaining) := by
  simp only [applyOptionalCommandSequence]
  rw [← bind_assoc, ← bind_assoc, commute state valid]

theorem applyOptionalCommandSequence_respects
    {State Command : Type} {related : State → State → Prop}
    {applyOne : State → Command → Option State}
    {commands : List Command}
    (respects : ∀ command, command ∈ commands →
      OptionalCommandRespects related applyOne command)
    {left right : State} (statesRelated : related left right) :
    OptionalResultsRelated related
      (applyOptionalCommandSequence applyOne left commands)
      (applyOptionalCommandSequence applyOne right commands) := by
  induction commands generalizing left right with
  | nil => exact .bothSucceeded statesRelated
  | cons command remaining inductionHypothesis =>
      simp only [applyOptionalCommandSequence]
      exact (respects command (by simp) statesRelated).bind
        (fun updated =>
          applyOptionalCommandSequence applyOne updated remaining)
        (fun updated =>
          applyOptionalCommandSequence applyOne updated remaining)
        (fun relatedUpdates =>
          inductionHypothesis
            (fun candidate member => respects candidate (by simp [member]))
            relatedUpdates)

theorem applyOptionalCommandSequence_adjacent_swap_modulo
    {State Command : Type} {related : State → State → Prop}
    {applyOne : State → Command → Option State} {first second : Command}
    (commute : OptionalCommandsCommuteModulo related applyOne first second)
    (state : State) (remaining : List Command)
    (remainingRespects : ∀ command, command ∈ remaining →
      OptionalCommandRespects related applyOne command) :
    OptionalResultsRelated related
      (applyOptionalCommandSequence applyOne state
        (first :: second :: remaining))
      (applyOptionalCommandSequence applyOne state
        (second :: first :: remaining)) := by
  simp only [applyOptionalCommandSequence, ← bind_assoc]
  exact (commute state).bind
    (fun updated => applyOptionalCommandSequence applyOne updated remaining)
    (fun updated => applyOptionalCommandSequence applyOne updated remaining)
    (fun relatedUpdates =>
      applyOptionalCommandSequence_respects remainingRespects relatedUpdates)

/-- Pairwise diamonds plus command extensionality lift commutation to every
    permutation even when successful states are only observationally equal. -/
theorem applyOptionalCommandSequence_permutation_modulo
    {State Command : Type} {related : State → State → Prop}
    {applyOne : State → Command → Option State}
    {Independent : Command → Command → Prop}
    (relatedReflexive : ∀ state, related state state)
    (relatedTransitive : ∀ {first second third},
      related first second → related second third → related first third)
    (independentSymmetric :
      ∀ {first second}, Independent first second → Independent second first)
    (independentCommutes :
      ∀ {first second}, Independent first second →
        OptionalCommandsCommuteModulo related applyOne first second)
    {original permuted : List Command}
    (pairwiseIndependent : original.Pairwise Independent)
    (respects : ∀ command, command ∈ original →
      OptionalCommandRespects related applyOne command)
    (permutation : original.Perm permuted) (state : State) :
    OptionalResultsRelated related
      (applyOptionalCommandSequence applyOne state original)
      (applyOptionalCommandSequence applyOne state permuted) := by
  induction permutation generalizing state with
  | nil => exact .bothSucceeded (relatedReflexive state)
  | cons command permutation inductionHypothesis =>
      simp only [applyOptionalCommandSequence]
      cases result : applyOne state command with
      | none => exact .bothFailed
      | some updated =>
          exact inductionHypothesis pairwiseIndependent.tail
            (fun remaining member => respects remaining (by simp [member]))
            updated
  | swap first second remaining =>
      have independent : Independent second first :=
        (List.pairwise_cons.mp pairwiseIndependent).1 first
          (List.mem_cons_self ..)
      exact applyOptionalCommandSequence_adjacent_swap_modulo
        (independentCommutes independent) state remaining
        (fun command member => respects command (by simp [member]))
  | trans firstPermutation secondPermutation firstIH secondIH =>
      have leftRelated := firstIH pairwiseIndependent respects state
      have rightRelated := secondIH
          (pairwiseIndependent.perm firstPermutation independentSymmetric)
          (fun command member =>
            respects command ((firstPermutation.mem_iff).mpr member)) state
      exact OptionalResultsRelated.transitive (related := related)
        relatedTransitive leftRelated rightRelated

/-- Pairwise independence plus the adjacent commutation equation makes the
    result invariant under every permutation.  This is the nontrivial list
    lifting required by M6; it also preserves failure, not merely successful
    final states. -/
theorem applyOptionalCommandSequence_permutation
    {State Command : Type} {applyOne : State → Command → Option State}
    {Independent : Command → Command → Prop}
    (independentSymmetric :
      ∀ {first second}, Independent first second → Independent second first)
    (independentCommutes :
      ∀ {first second}, Independent first second →
        OptionalCommandsCommute applyOne first second)
    {original permuted : List Command}
    (pairwiseIndependent : original.Pairwise Independent)
    (permutation : original.Perm permuted) (state : State) :
    applyOptionalCommandSequence applyOne state original =
      applyOptionalCommandSequence applyOne state permuted := by
  induction permutation generalizing state with
  | nil => rfl
  | cons command permutation inductionHypothesis =>
      simp only [applyOptionalCommandSequence]
      cases result : applyOne state command with
      | none => rfl
      | some updated =>
          exact inductionHypothesis pairwiseIndependent.tail updated
  | swap first second remaining =>
      have independent : Independent second first :=
        (List.pairwise_cons.mp pairwiseIndependent).1 first
          (List.mem_cons_self ..)
      have commute : OptionalCommandsCommute applyOne second first :=
        independentCommutes independent
      exact applyOptionalCommandSequence_adjacent_swap commute state remaining
  | trans firstPermutation secondPermutation firstIH secondIH =>
      calc
        applyOptionalCommandSequence applyOne state _ =
            applyOptionalCommandSequence applyOne state _ :=
          firstIH pairwiseIndependent state
        _ = applyOptionalCommandSequence applyOne state _ :=
          secondIH
            (pairwiseIndependent.perm firstPermutation independentSymmetric)
            state

/-- State-indexed version of the permutation theorem.  It is the form needed
    by reflection: store-domain coherence and actor/run-state coherence are
    invariants of valid intermediate states, rather than properties of every
    syntactically constructible state. -/
theorem applyOptionalCommandSequence_permutation_under_invariant
    {State Command : Type} {invariant : State → Prop}
    {applyOne : State → Command → Option State}
    {Independent : Command → Command → Prop}
    (independentSymmetric :
      ∀ {first second}, Independent first second → Independent second first)
    (independentCommutes :
      ∀ {first second}, Independent first second →
        OptionalCommandsCommuteUnder invariant applyOne first second)
    {original permuted : List Command}
    (pairwiseIndependent : original.Pairwise Independent)
    (preserves : ∀ command, command ∈ original →
      OptionalCommandPreserves invariant applyOne command)
    (permutation : original.Perm permuted) (state : State)
    (valid : invariant state) :
    applyOptionalCommandSequence applyOne state original =
      applyOptionalCommandSequence applyOne state permuted := by
  induction permutation generalizing state with
  | nil => rfl
  | cons command permutation inductionHypothesis =>
      simp only [applyOptionalCommandSequence]
      cases result : applyOne state command with
      | none => rfl
      | some updated =>
          have updatedValid : invariant updated :=
            preserves command (by simp) state updated valid result
          exact inductionHypothesis pairwiseIndependent.tail
            (fun remaining member => preserves remaining (by simp [member]))
            updated updatedValid
  | swap first second remaining =>
      have independent : Independent second first :=
        (List.pairwise_cons.mp pairwiseIndependent).1 first
          (List.mem_cons_self ..)
      exact applyOptionalCommandSequence_adjacent_swap_under
        (independentCommutes independent) state valid remaining
  | trans firstPermutation secondPermutation firstIH secondIH =>
      calc
        applyOptionalCommandSequence applyOne state _ =
            applyOptionalCommandSequence applyOne state _ :=
          firstIH pairwiseIndependent preserves state valid
        _ = applyOptionalCommandSequence applyOne state _ :=
          secondIH
            (pairwiseIndependent.perm firstPermutation independentSymmetric)
            (fun command member =>
              preserves command ((firstPermutation.mem_iff).mpr member))
            state valid

theorem debuggerPhase_permutation_invariant
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {original permuted : List ReflectionCommand}
    (independent : DebuggerTransactionIndependent materialize program requester
      original)
    (permutation : original.Perm permuted) (world : ActorWorld)
    (coherent : ActorStoreDomainsCoherent world) :
    applyDebuggerCommandSequence materialize program requester world
        (debuggerCommands original) =
      applyDebuggerCommandSequence materialize program requester world
        (debuggerCommands permuted) := by
  rw [applyDebuggerCommandSequence_eq_optional,
    applyDebuggerCommandSequence_eq_optional]
  apply applyOptionalCommandSequence_permutation_under_invariant
    (Independent := OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun current command =>
        applyDebuggerCommand materialize program requester current command))
    (fun commute => commute.symmetric) (fun commute => commute) independent
  · intro command _member
    exact applyDebuggerCommand_preserves_actorStoreDomains materialize program
      requester command
  · exact permutation.filter _
  · exact coherent

def SourceTransactionIndependentModulo
    (transaction : List ReflectionCommand) : Prop :=
  (codeCommands transaction).Pairwise
    (OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand)

def SourceTransactionExtensional
    (transaction : List ReflectionCommand) : Prop :=
  ∀ command, command ∈ codeCommands transaction →
    OptionalCommandRespects IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand command

theorem sourceTransactionExtensional
    (transaction : List ReflectionCommand) :
    SourceTransactionExtensional transaction := by
  intro command _member left right equivalent
  exact left.patchSourceCodeCommand_respects_lookupEquivalent equivalent command

theorem IdentifiedSourceImage.applySourceCodeCommands_eq_optional
    (source : IdentifiedSourceImage) (commands : List ReflectionCommand) :
    source.applySourceCodeCommands commands =
      applyOptionalCommandSequence
        IdentifiedSourceImage.patchSourceCodeCommand source commands := by
  induction commands generalizing source with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [IdentifiedSourceImage.applySourceCodeCommands,
        applyOptionalCommandSequence]
      cases result : source.patchSourceCodeCommand command with
      | none => rfl
      | some updated => exact inductionHypothesis updated

theorem sourcePhase_permutation_invariant_modulo
    {original permuted : List ReflectionCommand}
    (independent : SourceTransactionIndependentModulo original)
    (extensional : SourceTransactionExtensional original)
    (permutation : original.Perm permuted) (source : IdentifiedSourceImage) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (source.applySourceCodeCommands (codeCommands original))
      (source.applySourceCodeCommands (codeCommands permuted)) := by
  rw [source.applySourceCodeCommands_eq_optional,
    source.applySourceCodeCommands_eq_optional]
  exact applyOptionalCommandSequence_permutation_modulo
    IdentifiedSourceImage.LookupEquivalent.refl
    (fun left right => left.trans right)
    (fun commute => commute.symmetric
      IdentifiedSourceImage.LookupEquivalent.symm)
    (fun commute => commute) independent extensional
    (permutation.filter _) source

theorem sourcePhase_permutation_invariant
    {original permuted : List ReflectionCommand}
    (independent : SourceTransactionIndependentModulo original)
    (permutation : original.Perm permuted) (source : IdentifiedSourceImage) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (source.applySourceCodeCommands (codeCommands original))
      (source.applySourceCodeCommands (codeCommands permuted)) :=
  sourcePhase_permutation_invariant_modulo independent
    (sourceTransactionExtensional original) permutation source

theorem applyCohortClassGraphCommands_eq_optional
    (world : ActorWorld) (commands : List ReflectionCommand) :
    applyCohortClassGraphCommands world commands =
      applyOptionalCommandSequence applyCohortClassGraphCommand world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyCohortClassGraphCommands, applyOptionalCommandSequence]
      cases result : applyCohortClassGraphCommand world command with
      | none => rfl
      | some updated => exact inductionHypothesis updated

theorem applyCohortObjectClassCommands_eq_optional
    (world : ActorWorld) (commands : List ReflectionCommand) :
    applyCohortObjectClassCommands world commands =
      applyOptionalCommandSequence applyCohortObjectClassCommand world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyCohortObjectClassCommands, applyOptionalCommandSequence]
      cases result : applyCohortObjectClassCommand world command with
      | none => rfl
      | some updated => exact inductionHypothesis updated

theorem applyCohortObjectSlotCommands_eq_optional
    (program : Program) (world : ActorWorld)
    (commands : List ReflectionCommand) :
    applyCohortObjectSlotCommands program world commands =
      applyOptionalCommandSequence
        (applyCohortObjectSlotCommand program) world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyCohortObjectSlotCommands, applyOptionalCommandSequence]
      cases result : applyCohortObjectSlotCommand program world command with
      | none => rfl
      | some updated => exact inductionHypothesis updated

theorem applyCohortActivationCommands_eq_optional
    (world : ActorWorld) (commands : List ReflectionCommand) :
    applyCohortActivationCommands world commands =
      applyOptionalCommandSequence applyCohortActivationCommand world commands := by
  induction commands generalizing world with
  | nil => rfl
  | cons command remaining inductionHypothesis =>
      simp only [applyCohortActivationCommands, applyOptionalCommandSequence]
      cases result : applyCohortActivationCommand world command with
      | none => rfl
      | some updated => exact inductionHypothesis updated

theorem applyCohortClassGraphCommands_preserve_actorStoreDomains
    {before after : ActorWorld} (commands : List ReflectionCommand)
    (coherent : ActorStoreDomainsCoherent before)
    (result : applyCohortClassGraphCommands before commands = some after) :
    ActorStoreDomainsCoherent after := by
  rw [applyCohortClassGraphCommands_eq_optional] at result
  exact applyOptionalCommandSequence_preserves
    applyCohortClassGraphCommand_preserves_actorStoreDomains commands coherent
    result

theorem applyCohortObjectClassCommands_preserve_actorStoreDomains
    {before after : ActorWorld} (commands : List ReflectionCommand)
    (coherent : ActorStoreDomainsCoherent before)
    (result : applyCohortObjectClassCommands before commands = some after) :
    ActorStoreDomainsCoherent after := by
  rw [applyCohortObjectClassCommands_eq_optional] at result
  exact applyOptionalCommandSequence_preserves
    applyCohortObjectClassCommand_preserves_actorStoreDomains commands coherent
    result

theorem applyCohortObjectSlotCommands_preserve_actorStoreDomains
    (program : Program) {before after : ActorWorld}
    (commands : List ReflectionCommand)
    (coherent : ActorStoreDomainsCoherent before)
    (result : applyCohortObjectSlotCommands program before commands =
      some after) : ActorStoreDomainsCoherent after := by
  rw [applyCohortObjectSlotCommands_eq_optional] at result
  exact applyOptionalCommandSequence_preserves
    (applyCohortObjectSlotCommand_preserves_actorStoreDomains program)
    commands coherent result

theorem applyCohortActivationCommands_preserve_actorStoreDomains
    {before after : ActorWorld} (commands : List ReflectionCommand)
    (coherent : ActorStoreDomainsCoherent before)
    (result : applyCohortActivationCommands before commands = some after) :
    ActorStoreDomainsCoherent after := by
  rw [applyCohortActivationCommands_eq_optional] at result
  exact applyOptionalCommandSequence_preserves
    applyCohortActivationCommand_preserves_actorStoreDomains commands coherent
    result

theorem reconcileEveryObjectLayout_preserves_actorStoreDomains
    (program : Program) {before after : ActorWorld}
    (coherent : ActorStoreDomainsCoherent before)
    (result : reconcileEveryObjectLayout program before = some after) :
    ActorStoreDomainsCoherent after :=
  coherent.transformEveryHeap (Heap.reconcileAllObjectLayouts program) result

theorem reconcileEveryNestedCache_preserves_actorStoreDomains
    (program : Program) {before after : ActorWorld}
    (coherent : ActorStoreDomainsCoherent before)
    (result : reconcileEveryNestedCache program before = some after) :
    ActorStoreDomainsCoherent after :=
  coherent.transformEveryHeap (Heap.reconcileAllNestedCaches program) result

def CohortClassGraphTransactionIndependent
    (transaction : List ReflectionCommand) : Prop :=
  (classGraphCommands transaction).Pairwise
    (OptionalCommandsCommute applyCohortClassGraphCommand)

def CohortObjectClassTransactionIndependent
    (transaction : List ReflectionCommand) : Prop :=
  (objectClassCommands transaction).Pairwise
    (OptionalCommandsCommute applyCohortObjectClassCommand)

def CohortObjectSlotTransactionIndependent (program : Program)
    (transaction : List ReflectionCommand) : Prop :=
  (objectSlotCommands transaction).Pairwise
    (OptionalCommandsCommute (applyCohortObjectSlotCommand program))

def CohortActivationTransactionIndependent
    (transaction : List ReflectionCommand) : Prop :=
  (activationCommands transaction).Pairwise
    (OptionalCommandsCommute applyCohortActivationCommand)

theorem cohortClassGraphPhase_permutation_invariant
    {original permuted : List ReflectionCommand}
    (independent : CohortClassGraphTransactionIndependent original)
    (permutation : original.Perm permuted) (world : ActorWorld) :
    applyCohortClassGraphCommands world (classGraphCommands original) =
      applyCohortClassGraphCommands world (classGraphCommands permuted) := by
  rw [applyCohortClassGraphCommands_eq_optional,
    applyCohortClassGraphCommands_eq_optional]
  exact applyOptionalCommandSequence_permutation
    (fun commute => commute.symmetric) (fun commute => commute) independent
    (permutation.filter _) world

theorem cohortObjectClassPhase_permutation_invariant
    {original permuted : List ReflectionCommand}
    (independent : CohortObjectClassTransactionIndependent original)
    (permutation : original.Perm permuted) (world : ActorWorld) :
    applyCohortObjectClassCommands world (objectClassCommands original) =
      applyCohortObjectClassCommands world (objectClassCommands permuted) := by
  rw [applyCohortObjectClassCommands_eq_optional,
    applyCohortObjectClassCommands_eq_optional]
  exact applyOptionalCommandSequence_permutation
    (fun commute => commute.symmetric) (fun commute => commute) independent
    (permutation.filter _) world

theorem cohortObjectSlotPhase_permutation_invariant
    (program : Program) {original permuted : List ReflectionCommand}
    (independent : CohortObjectSlotTransactionIndependent program original)
    (permutation : original.Perm permuted) (world : ActorWorld) :
    applyCohortObjectSlotCommands program world (objectSlotCommands original) =
      applyCohortObjectSlotCommands program world
        (objectSlotCommands permuted) := by
  rw [applyCohortObjectSlotCommands_eq_optional,
    applyCohortObjectSlotCommands_eq_optional]
  exact applyOptionalCommandSequence_permutation
    (fun commute => commute.symmetric) (fun commute => commute) independent
    (permutation.filter _) world

theorem cohortActivationPhase_permutation_invariant
    {original permuted : List ReflectionCommand}
    (independent : CohortActivationTransactionIndependent original)
    (permutation : original.Perm permuted) (world : ActorWorld) :
    applyCohortActivationCommands world (activationCommands original) =
      applyCohortActivationCommands world (activationCommands permuted) := by
  rw [applyCohortActivationCommands_eq_optional,
    applyCohortActivationCommands_eq_optional]
  exact applyOptionalCommandSequence_permutation
    (fun commute => commute.symmetric) (fun commute => commute) independent
    (permutation.filter _) world

/-- The deterministic prefix of runtime reflection, ending immediately before
    debugger commands.  Naming it makes the coherence premise of the debugger
    fold explicit. -/
noncomputable def prepareReflectionRuntimeBeforeDebugger
    (program : Program) (transaction : List ReflectionCommand)
    (world : ActorWorld) : Option ActorWorld := do
  let classUpdated ← applyCohortClassGraphCommands world
    (classGraphCommands transaction)
  let objectClassUpdated ← applyCohortObjectClassCommands classUpdated
    (objectClassCommands transaction)
  let layoutsReconciled ← reconcileEveryObjectLayout program objectClassUpdated
  let cachesReconciled ← reconcileEveryNestedCache program layoutsReconciled
  let slotsUpdated ← applyCohortObjectSlotCommands program cachesReconciled
    (objectSlotCommands transaction)
  applyCohortActivationCommands slotsUpdated (activationCommands transaction)

theorem prepareReflectionRuntimeBeforeDebugger_preserves_actorStoreDomains
    (program : Program) (transaction : List ReflectionCommand)
    {before after : ActorWorld}
    (coherent : ActorStoreDomainsCoherent before)
    (result : prepareReflectionRuntimeBeforeDebugger program transaction before =
      some after) : ActorStoreDomainsCoherent after := by
  unfold prepareReflectionRuntimeBeforeDebugger at result
  cases classResult : applyCohortClassGraphCommands before
      (classGraphCommands transaction) with
  | none => simp [classResult] at result
  | some classUpdated =>
      have classCoherent :=
        applyCohortClassGraphCommands_preserve_actorStoreDomains
          (classGraphCommands transaction) coherent classResult
      cases objectClassResult : applyCohortObjectClassCommands classUpdated
          (objectClassCommands transaction) with
      | none => simp [classResult, objectClassResult] at result
      | some objectClassUpdated =>
          have objectClassCoherent :=
            applyCohortObjectClassCommands_preserve_actorStoreDomains
              (objectClassCommands transaction) classCoherent objectClassResult
          cases layoutResult :
              reconcileEveryObjectLayout program objectClassUpdated with
          | none =>
              simp [classResult, objectClassResult, layoutResult] at result
          | some layoutsReconciled =>
              have layoutCoherent :=
                reconcileEveryObjectLayout_preserves_actorStoreDomains program
                  objectClassCoherent layoutResult
              cases cacheResult :
                  reconcileEveryNestedCache program layoutsReconciled with
              | none =>
                  simp [classResult, objectClassResult, layoutResult,
                    cacheResult] at result
              | some cachesReconciled =>
                  have cacheCoherent :=
                    reconcileEveryNestedCache_preserves_actorStoreDomains program
                      layoutCoherent cacheResult
                  cases slotResult : applyCohortObjectSlotCommands program
                      cachesReconciled (objectSlotCommands transaction) with
                  | none =>
                      simp [classResult, objectClassResult, layoutResult,
                        cacheResult, slotResult] at result
                  | some slotsUpdated =>
                      have slotCoherent :=
                        applyCohortObjectSlotCommands_preserve_actorStoreDomains
                          program (objectSlotCommands transaction) cacheCoherent
                          slotResult
                      simp [classResult, objectClassResult, layoutResult,
                        cacheResult, slotResult] at result
                      exact
                        applyCohortActivationCommands_preserve_actorStoreDomains
                          (activationCommands transaction) slotCoherent result

theorem prepareReflectionRuntime_eq_beforeDebugger
    (program : Program) (requester : ActorId)
    (transaction : List ReflectionCommand) (world : ActorWorld) :
    prepareReflectionRuntime program requester transaction world = (do
      let activationsUpdated ←
        prepareReflectionRuntimeBeforeDebugger program transaction world
      let debuggerUpdated ← applyDebuggerCommandSequence materializeStackTemplate
        program requester activationsUpdated (debuggerCommands transaction)
      debuggerUpdated.applyContinuationTransferSequence
        (continuationCommands transaction)) := by
  unfold prepareReflectionRuntime prepareReflectionRuntimeBeforeDebugger
  cases classResult : applyCohortClassGraphCommands world
      (classGraphCommands transaction) with
  | none => simp
  | some classUpdated =>
      cases objectClassResult : applyCohortObjectClassCommands classUpdated
          (objectClassCommands transaction) with
      | none => simp [objectClassResult]
      | some objectClassUpdated =>
          cases layoutResult :
              reconcileEveryObjectLayout program objectClassUpdated with
          | none => simp [objectClassResult, layoutResult]
          | some layoutsReconciled =>
              cases cacheResult :
                  reconcileEveryNestedCache program layoutsReconciled with
              | none =>
                  simp [objectClassResult, layoutResult, cacheResult]
              | some cachesReconciled =>
                  cases slotResult : applyCohortObjectSlotCommands program
                      cachesReconciled (objectSlotCommands transaction) with
                  | none =>
                      simp [objectClassResult, layoutResult, cacheResult,
                        slotResult]
                  | some slotsUpdated =>
                      simp [objectClassResult, layoutResult, cacheResult,
                        slotResult]

theorem prepareReflectionRuntimeBeforeDebugger_permutation_invariant
    (program : Program) {original permuted : List ReflectionCommand}
    (classIndependent : CohortClassGraphTransactionIndependent original)
    (objectClassIndependent : CohortObjectClassTransactionIndependent original)
    (slotIndependent : CohortObjectSlotTransactionIndependent program original)
    (activationIndependent : CohortActivationTransactionIndependent original)
    (permutation : original.Perm permuted) (world : ActorWorld) :
    prepareReflectionRuntimeBeforeDebugger program original world =
      prepareReflectionRuntimeBeforeDebugger program permuted world := by
  have classEqual := cohortClassGraphPhase_permutation_invariant
    classIndependent permutation world
  cases classResult : applyCohortClassGraphCommands world
      (classGraphCommands original) with
  | none =>
      have permutedClassResult : applyCohortClassGraphCommands world
          (classGraphCommands permuted) = none := by
        rw [← classEqual]
        exact classResult
      simp [prepareReflectionRuntimeBeforeDebugger, classResult,
        permutedClassResult]
  | some classUpdated =>
      have permutedClassResult : applyCohortClassGraphCommands world
          (classGraphCommands permuted) = some classUpdated := by
        rw [← classEqual]
        exact classResult
      have objectClassEqual := cohortObjectClassPhase_permutation_invariant
        objectClassIndependent permutation classUpdated
      cases objectClassResult : applyCohortObjectClassCommands classUpdated
          (objectClassCommands original) with
      | none =>
          have permutedObjectClassResult :
              applyCohortObjectClassCommands classUpdated
                (objectClassCommands permuted) = none := by
            rw [← objectClassEqual]
            exact objectClassResult
          simp [prepareReflectionRuntimeBeforeDebugger, classResult,
            permutedClassResult, objectClassResult, permutedObjectClassResult]
      | some objectClassUpdated =>
          have permutedObjectClassResult :
              applyCohortObjectClassCommands classUpdated
                (objectClassCommands permuted) = some objectClassUpdated := by
            rw [← objectClassEqual]
            exact objectClassResult
          cases layoutResult :
              reconcileEveryObjectLayout program objectClassUpdated with
          | none =>
              simp [prepareReflectionRuntimeBeforeDebugger, classResult,
                permutedClassResult, objectClassResult,
                permutedObjectClassResult, layoutResult]
          | some layoutsReconciled =>
              cases cacheResult :
                  reconcileEveryNestedCache program layoutsReconciled with
              | none =>
                  simp [prepareReflectionRuntimeBeforeDebugger, classResult,
                    permutedClassResult, objectClassResult,
                    permutedObjectClassResult, layoutResult, cacheResult]
              | some cachesReconciled =>
                  have slotsEqual :=
                    cohortObjectSlotPhase_permutation_invariant program
                      slotIndependent permutation cachesReconciled
                  cases slotResult : applyCohortObjectSlotCommands program
                      cachesReconciled (objectSlotCommands original) with
                  | none =>
                      have permutedSlotResult :
                          applyCohortObjectSlotCommands program cachesReconciled
                            (objectSlotCommands permuted) = none := by
                        rw [← slotsEqual]
                        exact slotResult
                      simp [prepareReflectionRuntimeBeforeDebugger, classResult,
                        permutedClassResult, objectClassResult,
                        permutedObjectClassResult, layoutResult, cacheResult,
                        slotResult, permutedSlotResult]
                  | some slotsUpdated =>
                      have permutedSlotResult :
                          applyCohortObjectSlotCommands program cachesReconciled
                            (objectSlotCommands permuted) = some slotsUpdated := by
                        rw [← slotsEqual]
                        exact slotResult
                      have activationsEqual :=
                        cohortActivationPhase_permutation_invariant
                          activationIndependent permutation slotsUpdated
                      simp [prepareReflectionRuntimeBeforeDebugger, classResult,
                        permutedClassResult, objectClassResult,
                        permutedObjectClassResult, layoutResult, cacheResult,
                        slotResult, permutedSlotResult]
                      exact activationsEqual

theorem prepareReflectionRuntime_permutation_invariant
    (program : Program) (requester : ActorId)
    {original permuted : List ReflectionCommand}
    (classIndependent : CohortClassGraphTransactionIndependent original)
    (objectClassIndependent : CohortObjectClassTransactionIndependent original)
    (slotIndependent : CohortObjectSlotTransactionIndependent program original)
    (activationIndependent : CohortActivationTransactionIndependent original)
    (debuggerIndependent : DebuggerTransactionIndependent materializeStackTemplate
      program requester original)
    (nonconflicting : original.Pairwise ReflectionCommandsCompatible)
    (permutation : original.Perm permuted) (world : ActorWorld)
    (coherent : ActorStoreDomainsCoherent world) :
    prepareReflectionRuntime program requester original world =
      prepareReflectionRuntime program requester permuted world := by
  rw [prepareReflectionRuntime_eq_beforeDebugger,
    prepareReflectionRuntime_eq_beforeDebugger]
  have prefixEqual := prepareReflectionRuntimeBeforeDebugger_permutation_invariant
    program classIndependent objectClassIndependent slotIndependent
    activationIndependent permutation world
  cases prefixResult :
      prepareReflectionRuntimeBeforeDebugger program original world with
  | none =>
      have permutedPrefixResult :
          prepareReflectionRuntimeBeforeDebugger program permuted world = none := by
        rw [← prefixEqual]
        exact prefixResult
      simp [permutedPrefixResult]
  | some preparedWorld =>
      have permutedPrefixResult :
          prepareReflectionRuntimeBeforeDebugger program permuted world =
            some preparedWorld := by
        rw [← prefixEqual]
        exact prefixResult
      have debuggerEqual := debuggerPhase_permutation_invariant
        materializeStackTemplate program requester debuggerIndependent permutation
        preparedWorld
        (prepareReflectionRuntimeBeforeDebugger_preserves_actorStoreDomains
          program original coherent prefixResult)
      cases debuggerResult : applyDebuggerCommandSequence materializeStackTemplate
          program requester preparedWorld (debuggerCommands original) with
      | none =>
          have permutedDebuggerResult :
              applyDebuggerCommandSequence materializeStackTemplate program
                requester preparedWorld (debuggerCommands permuted) = none := by
            rw [← debuggerEqual]
            exact debuggerResult
          simp [permutedPrefixResult, debuggerResult,
            permutedDebuggerResult]
      | some debuggerUpdated =>
          have permutedDebuggerResult :
              applyDebuggerCommandSequence materializeStackTemplate program
                requester preparedWorld (debuggerCommands permuted) =
                  some debuggerUpdated := by
            rw [← debuggerEqual]
            exact debuggerResult
          simp [permutedPrefixResult, debuggerResult,
            permutedDebuggerResult]
          exact continuationPhase_permutation_invariant nonconflicting
            permutation debuggerUpdated

/-- Actor worlds agree observably when their installed programs agree by
    lookup and every other component is literally identical. -/
structure ActorWorld.ProgramLookupEquivalent (left right : ActorWorld) : Prop where
  program : left.program.LookupEquivalent right.program
  nonProgramState : { left with program := right.program } = right

/-- Final reflective VMs quotient source and installed-program store order,
    while retaining exact equality of every runtime component. -/
structure ReflectiveVM.LookupEquivalent
    (left right : ReflectiveVM IdentifiedSourceImage) : Prop where
  source : left.source.LookupEquivalent right.source
  world : left.world.ProgramLookupEquivalent right.world

/-- The two extensionality obligations at the compiler/runtime boundary.
    `reelaboration` includes agreement on failure; `runtimePreparation`
    permits a different but lookup-equivalent installed program on each side
    while requiring the same prepared runtime state. -/
structure ReflectionPipelineExtensionality
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    (original permuted : List ReflectionCommand) : Prop where
  reelaboration : ∀ {leftSource rightSource : IdentifiedSourceImage},
    leftSource.LookupEquivalent rightSource →
      OptionalResultsRelated Program.LookupEquivalent
        (leftSource.reelaborateInstalledProgram before.world.program)
        (rightSource.reelaborateInstalledProgram before.world.program)
  runtimePreparation : ∀ {leftProgram rightProgram : Program},
    leftProgram.LookupEquivalent rightProgram →
      OptionalResultsRelated Eq
        (prepareReflectionRuntime leftProgram requester original before.world)
        (prepareReflectionRuntime rightProgram requester permuted before.world)

/-- The concrete phase obligations sufficient for a whole-runtime permutation.
    Program-sensitive certificates are universally quantified because the
    source phase determines the rebuilt candidate only after patching. -/
structure ReflectionRuntimePermutationCertificates
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    (original permuted : List ReflectionCommand) : Prop where
  classIndependent : CohortClassGraphTransactionIndependent original
  objectClassIndependent : CohortObjectClassTransactionIndependent original
  slotIndependent : ∀ program,
    CohortObjectSlotTransactionIndependent program original
  activationIndependent : CohortActivationTransactionIndependent original
  debuggerIndependent : ∀ program,
    DebuggerTransactionIndependent materializeStackTemplate program requester
      original
  nonconflicting : original.Pairwise ReflectionCommandsCompatible
  permutation : original.Perm permuted
  initialCoherent : ActorStoreDomainsCoherent before.world

/-- Lookup-equivalent source images re-elaborate together, and the concrete
    runtime's program extensionality plus phase permutation theorem discharge
    the former abstract compiler/runtime boundary assumption. -/
theorem reflectionPipelineExtensionality_of_runtimeCertificates
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    {original permuted : List ReflectionCommand}
    (certificates : ReflectionRuntimePermutationCertificates before requester
      original permuted) :
    ReflectionPipelineExtensionality before requester original permuted :=
  { reelaboration := by
      intro leftSource rightSource equivalent
      exact leftSource.reelaborateInstalledProgram_related_of_lookupEquivalent
        before.world.program equivalent
    runtimePreparation := by
      intro leftProgram rightProgram equivalent
      have programsEqual :=
        prepareReflectionRuntime_of_program_lookupEquivalent equivalent requester
          original before.world
      have phasesEqual := prepareReflectionRuntime_permutation_invariant
        rightProgram requester certificates.classIndependent
        certificates.objectClassIndependent
        (certificates.slotIndependent rightProgram)
        certificates.activationIndependent
        (certificates.debuggerIndependent rightProgram)
        certificates.nonconflicting certificates.permutation before.world
        certificates.initialCoherent
      rw [programsEqual, phasesEqual]
      exact OptionalResultsRelated.reflexive (fun _ => rfl) _ }

/-- Full outer-shell M6 composition.  Source permutation, re-elaboration, all
    runtime phases, and atomic installation preserve both failure and the
    observational result relation. -/
theorem prepareReflection_permutation_modulo
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    {original permuted : List ReflectionCommand}
    (sourceRelated :
      OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
        (before.source.applySourceCodeCommands (codeCommands original))
        (before.source.applySourceCodeCommands (codeCommands permuted)))
    (extensional : ReflectionPipelineExtensionality before requester original
      permuted) :
    OptionalResultsRelated ReflectiveVM.LookupEquivalent
      (prepareReflection identifiedSourceReflectionFrontEnd
        prepareReflectionRuntime before requester original)
      (prepareReflection identifiedSourceReflectionFrontEnd
        prepareReflectionRuntime before requester permuted) := by
  unfold prepareReflection identifiedSourceReflectionFrontEnd
  exact sourceRelated.bind
    (fun source => do
      let program ← source.reelaborateInstalledProgram before.world.program
      let runtime ←
        prepareReflectionRuntime program requester original before.world
      some (⟨source,
        { runtime with
          program := program
          programVersion := before.world.programVersion + 1 }⟩ :
            ReflectiveVM IdentifiedSourceImage))
    (fun source => do
      let program ← source.reelaborateInstalledProgram before.world.program
      let runtime ←
        prepareReflectionRuntime program requester permuted before.world
      some (⟨source,
        { runtime with
          program := program
          programVersion := before.world.programVersion + 1 }⟩ :
            ReflectiveVM IdentifiedSourceImage))
    (fun {leftSource rightSource} sourcesEquivalent =>
      (extensional.reelaboration sourcesEquivalent).bind
        (fun program => do
          let runtime ←
            prepareReflectionRuntime program requester original before.world
          some (⟨leftSource,
            { runtime with
              program := program
              programVersion := before.world.programVersion + 1 }⟩ :
                ReflectiveVM IdentifiedSourceImage))
        (fun program => do
          let runtime ←
            prepareReflectionRuntime program requester permuted before.world
          some (⟨rightSource,
            { runtime with
              program := program
              programVersion := before.world.programVersion + 1 }⟩ :
                ReflectiveVM IdentifiedSourceImage))
        (fun {leftProgram rightProgram} programsEquivalent =>
          (extensional.runtimePreparation programsEquivalent).bind
            (fun runtime => some (⟨leftSource,
              { runtime with
                program := leftProgram
                programVersion := before.world.programVersion + 1 }⟩ :
                  ReflectiveVM IdentifiedSourceImage))
            (fun runtime => some (⟨rightSource,
              { runtime with
                program := rightProgram
                programVersion := before.world.programVersion + 1 }⟩ :
                  ReflectiveVM IdentifiedSourceImage))
            (fun runtimeEqual => by
              subst runtimeEqual
              exact .bothSucceeded
                { source := sourcesEquivalent
                  world :=
                    { program := programsEquivalent
                      nonProgramState := rfl } })))

theorem prepareReflection_permutation_of_certificates
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    {original permuted : List ReflectionCommand}
    (sourceIndependent : SourceTransactionIndependentModulo original)
    (runtimeCertificates : ReflectionRuntimePermutationCertificates before
      requester original permuted) :
    OptionalResultsRelated ReflectiveVM.LookupEquivalent
      (prepareReflection identifiedSourceReflectionFrontEnd
        prepareReflectionRuntime before requester original)
      (prepareReflection identifiedSourceReflectionFrontEnd
        prepareReflectionRuntime before requester permuted) :=
  prepareReflection_permutation_modulo before requester
    (sourcePhase_permutation_invariant sourceIndependent
      runtimeCertificates.permutation
      before.source)
    (reflectionPipelineExtensionality_of_runtimeCertificates before requester
      runtimeCertificates)

theorem applyOptionalCommandSequence_permutation_of_pairwise_commutation
    {State Command : Type} {applyOne : State → Command → Option State}
    {original permuted : List Command}
    (pairwiseCommutes :
      original.Pairwise (OptionalCommandsCommute applyOne))
    (permutation : original.Perm permuted) (state : State) :
    applyOptionalCommandSequence applyOne state original =
      applyOptionalCommandSequence applyOne state permuted := by
  exact applyOptionalCommandSequence_permutation
    (Independent := OptionalCommandsCommute applyOne)
    (fun commute => commute.symmetric) (fun commute => commute)
    pairwiseCommutes permutation state

theorem filteredCommandPermutation
    {Command : Type} (select : Command → Bool)
    {original permuted : List Command}
    (permutation : original.Perm permuted) :
    (original.filter select).Perm (permuted.filter select) :=
  permutation.filter select

theorem Heap.transformExistingClass_distinct_commutes
    (heap : Heap) {first second : ClassId} (different : first ≠ second)
    (firstTransform secondTransform : ClassDef → ClassDef)
    {firstDefinition secondDefinition : ClassDef}
    (firstPresent : heap.classes first = some firstDefinition)
    (secondPresent : heap.classes second = some secondDefinition) :
    (do
      let afterFirst ← heap.transformExistingClass first firstTransform
      afterFirst.transformExistingClass second secondTransform) =
    (do
      let afterSecond ← heap.transformExistingClass second secondTransform
      afterSecond.transformExistingClass first firstTransform) := by
  have firstMember := heap.classes.mem_domain_of_lookup_eq_some firstPresent
  have secondMember := heap.classes.mem_domain_of_lookup_eq_some secondPresent
  simp [Heap.transformExistingClass, firstPresent, secondPresent, different,
    different.symm, Heap.installClass]
  rw [heap.classes.install_distinct_commute_of_mem different firstMember
    secondMember (firstTransform firstDefinition)
    (secondTransform secondDefinition)]

theorem Heap.transformExistingClass_distinct_commutes_total
    (heap : Heap) {first second : ClassId} (different : first ≠ second)
    (firstTransform secondTransform : ClassDef → ClassDef) :
    (do
      let afterFirst ← heap.transformExistingClass first firstTransform
      afterFirst.transformExistingClass second secondTransform) =
    (do
      let afterSecond ← heap.transformExistingClass second secondTransform
      afterSecond.transformExistingClass first firstTransform) := by
  cases firstResult : heap.classes first with
  | none =>
      cases secondResult : heap.classes second <;>
        simp [Heap.transformExistingClass, Heap.installClass, firstResult,
          secondResult, different]
  | some firstDefinition =>
      cases secondResult : heap.classes second with
      | none =>
          simp [Heap.transformExistingClass, Heap.installClass, firstResult,
            secondResult, different.symm]
      | some secondDefinition =>
          exact heap.transformExistingClass_distinct_commutes different
            firstTransform secondTransform firstResult secondResult

theorem Heap.transformExistingClass_preserves_containsClassId
    {heap updated : Heap} (classId query : ClassId)
    (transform : ClassDef → ClassDef)
    (result : heap.transformExistingClass classId transform = some updated) :
    updated.containsClassId query = heap.containsClassId query := by
  unfold Heap.transformExistingClass at result
  cases present : heap.classes classId with
  | none => simp [present] at result
  | some definition =>
      simp [present] at result
      subst updated
      by_cases atClass : query = classId
      · subst query
        simp [Heap.containsClassId, present]
      · simp [Heap.containsClassId, Heap.installClass, atClass]

theorem Heap.transformExistingClass_same_commutes
    (heap : Heap) (classId : ClassId)
    (firstTransform secondTransform : ClassDef → ClassDef)
    {definition : ClassDef} (present : heap.classes classId = some definition)
    (transformsCommute :
      secondTransform (firstTransform definition) =
        firstTransform (secondTransform definition)) :
    (do
      let afterFirst ← heap.transformExistingClass classId firstTransform
      afterFirst.transformExistingClass classId secondTransform) =
    (do
      let afterSecond ← heap.transformExistingClass classId secondTransform
      afterSecond.transformExistingClass classId firstTransform) := by
  simp [Heap.transformExistingClass, Heap.installClass, present,
    transformsCommute]
  rw [FiniteStore.install_same_key_overwrites,
    FiniteStore.install_same_key_overwrites]

theorem Heap.superclassAndEnclosingObjectChanges_commute
    (heap : Heap) (superclassClass enclosingClass superclass : ClassId)
    (enclosingObject : ObjRef)
    {superclassDefinition enclosingDefinition : ClassDef}
    (superclassPresent :
      heap.classes superclassClass = some superclassDefinition)
    (enclosingPresent : heap.classes enclosingClass = some enclosingDefinition) :
    (do
      let afterSuperclass ←
        heap.reflectChangeSuperclass superclassClass superclass
      afterSuperclass.reflectChangeClassEnclosingObject enclosingClass
        enclosingObject) =
    (do
      let afterEnclosing ←
        heap.reflectChangeClassEnclosingObject enclosingClass enclosingObject
      afterEnclosing.reflectChangeSuperclass superclassClass superclass) := by
  by_cases equal : superclassClass = enclosingClass
  · subst enclosingClass
    have definitionsEqual : superclassDefinition = enclosingDefinition := by
      rw [superclassPresent] at enclosingPresent
      injection enclosingPresent
    subst enclosingDefinition
    exact heap.transformExistingClass_same_commutes superclassClass _ _
      superclassPresent (by rfl)
  · exact heap.transformExistingClass_distinct_commutes equal _ _
      superclassPresent enclosingPresent

theorem Heap.superclassAndEnclosingObjectChanges_commute_total
    (heap : Heap) (superclassClass enclosingClass superclass : ClassId)
    (enclosingObject : ObjRef) :
    (do
      let afterSuperclass ←
        heap.reflectChangeSuperclass superclassClass superclass
      afterSuperclass.reflectChangeClassEnclosingObject enclosingClass
        enclosingObject) =
    (do
      let afterEnclosing ←
        heap.reflectChangeClassEnclosingObject enclosingClass enclosingObject
      afterEnclosing.reflectChangeSuperclass superclassClass superclass) := by
  by_cases equal : superclassClass = enclosingClass
  · subst enclosingClass
    cases present : heap.classes superclassClass with
    | none =>
        simp [Heap.reflectChangeSuperclass,
          Heap.reflectChangeClassEnclosingObject,
          Heap.transformExistingClass, present]
    | some definition =>
        exact heap.superclassAndEnclosingObjectChanges_commute
          superclassClass superclassClass superclass enclosingObject present
          present
  · simpa [Heap.reflectChangeSuperclass,
      Heap.reflectChangeClassEnclosingObject] using
      heap.transformExistingClass_distinct_commutes_total equal
        (Heap.reflectedSuperclassTransform superclass)
        (Heap.reflectedEnclosingObjectTransform enclosingObject)

theorem Heap.transformExistingObject_distinct_commutes
    (heap : Heap) {first second : ObjectId} (different : first ≠ second)
    (firstTransform secondTransform : ObjectDef → ObjectDef)
    {firstDefinition secondDefinition : ObjectDef}
    (firstPresent : heap.objects first = some firstDefinition)
    (secondPresent : heap.objects second = some secondDefinition) :
    (do
      let afterFirst ← heap.transformExistingObject first firstTransform
      afterFirst.transformExistingObject second secondTransform) =
    (do
      let afterSecond ← heap.transformExistingObject second secondTransform
      afterSecond.transformExistingObject first firstTransform) := by
  have firstMember := heap.objects.mem_domain_of_lookup_eq_some firstPresent
  have secondMember := heap.objects.mem_domain_of_lookup_eq_some secondPresent
  simp [Heap.transformExistingObject, firstPresent, secondPresent, different,
    different.symm, Heap.installObject]
  rw [heap.objects.install_distinct_commute_of_mem different firstMember
    secondMember (firstTransform firstDefinition)
    (secondTransform secondDefinition)]

theorem Heap.transformExistingObject_distinct_commutes_total
    (heap : Heap) {first second : ObjectId} (different : first ≠ second)
    (firstTransform secondTransform : ObjectDef → ObjectDef) :
    (do
      let afterFirst ← heap.transformExistingObject first firstTransform
      afterFirst.transformExistingObject second secondTransform) =
    (do
      let afterSecond ← heap.transformExistingObject second secondTransform
      afterSecond.transformExistingObject first firstTransform) := by
  cases firstResult : heap.objects first with
  | none =>
      cases secondResult : heap.objects second <;>
        simp [Heap.transformExistingObject, Heap.installObject, firstResult,
          secondResult, different]
  | some firstDefinition =>
      cases secondResult : heap.objects second with
      | none =>
          simp [Heap.transformExistingObject, Heap.installObject, firstResult,
            secondResult, different.symm]
      | some secondDefinition =>
          exact heap.transformExistingObject_distinct_commutes different
            firstTransform secondTransform firstResult secondResult

theorem Heap.transformExistingObject_preserves_containsObjectId
    {heap updated : Heap} (object query : ObjectId)
    (transform : ObjectDef → ObjectDef)
    (result : heap.transformExistingObject object transform = some updated) :
    updated.containsObjectId query = heap.containsObjectId query := by
  unfold Heap.transformExistingObject at result
  cases present : heap.objects object with
  | none => simp [present] at result
  | some definition =>
      simp [present] at result
      subst updated
      by_cases atObject : query = object
      · subst query
        simp [Heap.containsObjectId, present]
      · simp [Heap.containsObjectId, Heap.installObject, atObject]

theorem Heap.transformExistingActivation_distinct_commutes
    (heap : Heap) {first second : ActivationId} (different : first ≠ second)
    (firstTransform secondTransform : ActivationDef → ActivationDef)
    {firstDefinition secondDefinition : ActivationDef}
    (firstPresent : heap.activations first = some firstDefinition)
    (secondPresent : heap.activations second = some secondDefinition) :
    (do
      let afterFirst ← heap.transformExistingActivation first firstTransform
      afterFirst.transformExistingActivation second secondTransform) =
    (do
      let afterSecond ← heap.transformExistingActivation second secondTransform
      afterSecond.transformExistingActivation first firstTransform) := by
  have firstMember :=
    heap.activations.mem_domain_of_lookup_eq_some firstPresent
  have secondMember :=
    heap.activations.mem_domain_of_lookup_eq_some secondPresent
  simp [Heap.transformExistingActivation, firstPresent, secondPresent,
    different, different.symm, Heap.installActivation]
  rw [heap.activations.install_distinct_commute_of_mem different firstMember
    secondMember (firstTransform firstDefinition)
    (secondTransform secondDefinition)]

theorem Heap.transformExistingActivation_distinct_commutes_total
    (heap : Heap) {first second : ActivationId} (different : first ≠ second)
    (firstTransform secondTransform : ActivationDef → ActivationDef) :
    (do
      let afterFirst ← heap.transformExistingActivation first firstTransform
      afterFirst.transformExistingActivation second secondTransform) =
    (do
      let afterSecond ← heap.transformExistingActivation second secondTransform
      afterSecond.transformExistingActivation first firstTransform) := by
  cases firstResult : heap.activations first with
  | none =>
      cases secondResult : heap.activations second <;>
        simp [Heap.transformExistingActivation, Heap.installActivation,
          firstResult, secondResult, different]
  | some firstDefinition =>
      cases secondResult : heap.activations second with
      | none =>
          simp [Heap.transformExistingActivation, Heap.installActivation,
            firstResult, secondResult, different.symm]
      | some secondDefinition =>
          exact heap.transformExistingActivation_distinct_commutes different
            firstTransform secondTransform firstResult secondResult

theorem Heap.applyActivationRecordEdit_preserves_containsActivationId
    {heap updated : Heap} (activation query : ActivationId)
    (edit : ActivationRecordEdit)
    (result : heap.applyActivationRecordEdit activation edit = some updated) :
    updated.containsActivationId query = heap.containsActivationId query := by
  unfold Heap.applyActivationRecordEdit at result
  cases present : heap.activations activation with
  | none => simp [present] at result
  | some definition =>
      cases enabled : edit.enabled definition with
      | false => simp [present, enabled] at result
      | true =>
          simp [present, enabled] at result
          subst updated
          by_cases atActivation : query = activation
          · subst query
            simp [Heap.containsActivationId, present]
          · simp [Heap.containsActivationId, Heap.installActivation,
              atActivation]

theorem Heap.transformExistingActivation_same_commutes
    (heap : Heap) (activation : ActivationId)
    (firstTransform secondTransform : ActivationDef → ActivationDef)
    {definition : ActivationDef}
    (present : heap.activations activation = some definition)
    (transformsCommute :
      secondTransform (firstTransform definition) =
        firstTransform (secondTransform definition)) :
    (do
      let afterFirst ←
        heap.transformExistingActivation activation firstTransform
      afterFirst.transformExistingActivation activation secondTransform) =
    (do
      let afterSecond ←
        heap.transformExistingActivation activation secondTransform
      afterSecond.transformExistingActivation activation firstTransform) := by
  simp [Heap.transformExistingActivation, Heap.installActivation, present,
    transformsCommute]
  rw [FiniteStore.install_same_key_overwrites,
    FiniteStore.install_same_key_overwrites]

theorem Heap.currentClassAndContinuationChanges_commute
    (heap : Heap) (currentClassActivation continuationActivation : ActivationId)
    (classId : Option ClassId) (continuation : Option ActivationId)
    {currentClassDefinition continuationDefinition : ActivationDef}
    (currentClassPresent :
      heap.activations currentClassActivation = some currentClassDefinition)
    (continuationPresent :
      heap.activations continuationActivation = some continuationDefinition) :
    (do
      let afterCurrentClass ←
        heap.reflectChangeActivationCurrentClass currentClassActivation classId
      afterCurrentClass.reflectChangeActivationContinuation
        continuationActivation continuation) =
    (do
      let afterContinuation ←
        heap.reflectChangeActivationContinuation continuationActivation continuation
      afterContinuation.reflectChangeActivationCurrentClass currentClassActivation
        classId) := by
  by_cases equal : currentClassActivation = continuationActivation
  · subst continuationActivation
    have definitionsEqual :
        currentClassDefinition = continuationDefinition := by
      rw [currentClassPresent] at continuationPresent
      injection continuationPresent
    subst continuationDefinition
    exact heap.transformExistingActivation_same_commutes
      currentClassActivation _ _ currentClassPresent (by rfl)
  · exact heap.transformExistingActivation_distinct_commutes equal _ _
      currentClassPresent continuationPresent

theorem Heap.reflectedParameterTransforms_commute
    {firstParameter secondParameter : ParameterId}
    (different : firstParameter ≠ secondParameter)
    (firstValue secondValue : ObjRef) (definition : ActivationDef)
    {oldFirstValue oldSecondValue : ObjRef}
    (firstPresent : definition.parameters firstParameter = some oldFirstValue)
    (secondPresent : definition.parameters secondParameter = some oldSecondValue) :
    reflectedParameterTransform secondParameter secondValue
        (reflectedParameterTransform firstParameter firstValue definition) =
      reflectedParameterTransform firstParameter firstValue
        (reflectedParameterTransform secondParameter secondValue definition) := by
  have firstMember :=
    definition.parameters.mem_domain_of_lookup_eq_some firstPresent
  have secondMember :=
    definition.parameters.mem_domain_of_lookup_eq_some secondPresent
  unfold reflectedParameterTransform
  congr 1
  exact definition.parameters.install_distinct_commute_of_mem different
    firstMember secondMember firstValue secondValue

theorem Heap.reflectedLocalTransforms_commute
    {firstSlot secondSlot : LocalSlotId} (different : firstSlot ≠ secondSlot)
    (firstValue secondValue : ObjRef) (definition : ActivationDef)
    {oldFirstCell oldSecondCell : LocalCell}
    (firstPresent : definition.locals firstSlot = some oldFirstCell)
    (secondPresent : definition.locals secondSlot = some oldSecondCell) :
    reflectedLocalTransform secondSlot secondValue
        (reflectedLocalTransform firstSlot firstValue definition) =
      reflectedLocalTransform firstSlot firstValue
        (reflectedLocalTransform secondSlot secondValue definition) := by
  have firstMember := definition.locals.mem_domain_of_lookup_eq_some firstPresent
  have secondMember := definition.locals.mem_domain_of_lookup_eq_some secondPresent
  unfold reflectedLocalTransform
  congr 1
  exact definition.locals.install_distinct_commute_of_mem different
    firstMember secondMember (.value firstValue) (.value secondValue)

theorem Heap.reflectedParameterAndLocalTransforms_commute
    (parameter : ParameterId) (parameterValue : ObjRef)
    (slot : LocalSlotId) (localValue : ObjRef) (definition : ActivationDef) :
    reflectedLocalTransform slot localValue
        (reflectedParameterTransform parameter parameterValue definition) =
      reflectedParameterTransform parameter parameterValue
        (reflectedLocalTransform slot localValue definition) := by
  rfl

theorem Heap.reflectedParameterAndCurrentClassTransforms_commute
    (parameter : ParameterId) (value : ObjRef) (classId : Option ClassId)
    (definition : ActivationDef) :
    reflectedCurrentClassTransform classId
        (reflectedParameterTransform parameter value definition) =
      reflectedParameterTransform parameter value
        (reflectedCurrentClassTransform classId definition) := by
  rfl

theorem Heap.reflectedParameterAndContinuationTransforms_commute
    (parameter : ParameterId) (value : ObjRef)
    (continuation : Option ActivationId) (definition : ActivationDef) :
    reflectedContinuationTransform continuation
        (reflectedParameterTransform parameter value definition) =
      reflectedParameterTransform parameter value
        (reflectedContinuationTransform continuation definition) := by
  rfl

theorem Heap.reflectedLocalAndCurrentClassTransforms_commute
    (slot : LocalSlotId) (value : ObjRef) (classId : Option ClassId)
    (definition : ActivationDef) :
    reflectedCurrentClassTransform classId
        (reflectedLocalTransform slot value definition) =
      reflectedLocalTransform slot value
        (reflectedCurrentClassTransform classId definition) := by
  rfl

theorem Heap.reflectedLocalAndContinuationTransforms_commute
    (slot : LocalSlotId) (value : ObjRef)
    (continuation : Option ActivationId) (definition : ActivationDef) :
    reflectedContinuationTransform continuation
        (reflectedLocalTransform slot value definition) =
      reflectedLocalTransform slot value
        (reflectedContinuationTransform continuation definition) := by
  rfl

theorem Heap.reflectWriteActivationParameter_eq_transform
    (heap : Heap) (activation : ActivationId) (parameter : ParameterId)
    (value : ObjRef) {definition : ActivationDef} {oldValue : ObjRef}
    (activationPresent : heap.activations activation = some definition)
    (parameterPresent : definition.parameters parameter = some oldValue) :
    heap.reflectWriteActivationParameter activation parameter value =
      heap.transformExistingActivation activation
        (reflectedParameterTransform parameter value) := by
  simp [Heap.reflectWriteActivationParameter, Heap.transformExistingActivation,
    Heap.applyActivationRecordEdit, Heap.parameterRecordEdit,
    activationPresent, parameterPresent]

theorem Heap.reflectWriteActivationLocal_eq_transform
    (heap : Heap) (activation : ActivationId) (slot : LocalSlotId)
    (value : ObjRef) {definition : ActivationDef} {oldCell : LocalCell}
    (activationPresent : heap.activations activation = some definition)
    (localPresent : definition.locals slot = some oldCell) :
    heap.reflectWriteActivationLocal activation slot value =
      heap.transformExistingActivation activation
        (reflectedLocalTransform slot value) := by
  simp [Heap.reflectWriteActivationLocal, Heap.transformExistingActivation,
    Heap.applyActivationRecordEdit, Heap.localRecordEdit,
    activationPresent, localPresent]

theorem Heap.applyActivationRecordEdits_distinct_commute
    (heap : Heap) {first second : ActivationId} (different : first ≠ second)
    (firstEdit secondEdit : ActivationRecordEdit)
    {firstDefinition secondDefinition : ActivationDef}
    (firstPresent : heap.activations first = some firstDefinition)
    (secondPresent : heap.activations second = some secondDefinition)
    (firstEnabled : firstEdit.enabled firstDefinition = true)
    (secondEnabled : secondEdit.enabled secondDefinition = true) :
    (do
      let afterFirst ← heap.applyActivationRecordEdit first firstEdit
      afterFirst.applyActivationRecordEdit second secondEdit) =
    (do
      let afterSecond ← heap.applyActivationRecordEdit second secondEdit
      afterSecond.applyActivationRecordEdit first firstEdit) := by
  have firstMember :=
    heap.activations.mem_domain_of_lookup_eq_some firstPresent
  have secondMember :=
    heap.activations.mem_domain_of_lookup_eq_some secondPresent
  simp [Heap.applyActivationRecordEdit, firstPresent, secondPresent,
    firstEnabled, secondEnabled, different, different.symm,
    Heap.installActivation]
  rw [heap.activations.install_distinct_commute_of_mem different firstMember
    secondMember (firstEdit.transform firstDefinition)
    (secondEdit.transform secondDefinition)]

theorem Heap.applyActivationRecordEdits_distinct_commute_total
    (heap : Heap) {first second : ActivationId} (different : first ≠ second)
    (firstEdit secondEdit : ActivationRecordEdit) :
    (do
      let afterFirst ← heap.applyActivationRecordEdit first firstEdit
      afterFirst.applyActivationRecordEdit second secondEdit) =
    (do
      let afterSecond ← heap.applyActivationRecordEdit second secondEdit
      afterSecond.applyActivationRecordEdit first firstEdit) := by
  cases firstResult : heap.activations first with
  | none =>
      cases secondResult : heap.activations second with
      | none => simp [Heap.applyActivationRecordEdit, firstResult, secondResult]
      | some secondDefinition =>
          cases secondEnabled : secondEdit.enabled secondDefinition <;>
            simp [Heap.applyActivationRecordEdit, firstResult, secondResult,
              secondEnabled, different]
  | some firstDefinition =>
      cases secondResult : heap.activations second with
      | none =>
          cases firstEnabled : firstEdit.enabled firstDefinition <;>
            simp [Heap.applyActivationRecordEdit, firstResult, secondResult,
              firstEnabled, different.symm]
      | some secondDefinition =>
          cases firstEnabled : firstEdit.enabled firstDefinition <;>
            cases secondEnabled : secondEdit.enabled secondDefinition <;>
            try simp [Heap.applyActivationRecordEdit, firstResult,
              secondResult, firstEnabled, secondEnabled, different,
              different.symm]
          unfold Heap.installActivation
          congr 1
          exact heap.activations.install_distinct_commute_of_mem different
            (heap.activations.mem_domain_of_lookup_eq_some firstResult)
            (heap.activations.mem_domain_of_lookup_eq_some secondResult) _ _

/-- State-free compatibility law for two edits of the same activation record.
    Each edit preserves the other's applicability, and their record
    transformers commute even before applicability is known. -/
structure ActivationRecordEditsCommuteStatically
    (first second : Heap.ActivationRecordEdit) : Prop where
  secondEnabledAfterFirst : ∀ definition,
    second.enabled (first.transform definition) = second.enabled definition
  firstEnabledAfterSecond : ∀ definition,
    first.enabled (second.transform definition) = first.enabled definition
  transformsCommute : ∀ definition,
    first.enabled definition = true → second.enabled definition = true →
    second.transform (first.transform definition) =
      first.transform (second.transform definition)

theorem Heap.applyActivationRecordEdits_same_commute_total
    (heap : Heap) (activation : ActivationId)
    (firstEdit secondEdit : ActivationRecordEdit)
    (static : ActivationRecordEditsCommuteStatically firstEdit secondEdit) :
    (do
      let afterFirst ← heap.applyActivationRecordEdit activation firstEdit
      afterFirst.applyActivationRecordEdit activation secondEdit) =
    (do
      let afterSecond ← heap.applyActivationRecordEdit activation secondEdit
      afterSecond.applyActivationRecordEdit activation firstEdit) := by
  cases present : heap.activations activation with
  | none => simp [Heap.applyActivationRecordEdit, present]
  | some definition =>
      cases firstEnabled : firstEdit.enabled definition with
      | false =>
          cases secondEnabled : secondEdit.enabled definition <;>
            simp [Heap.applyActivationRecordEdit, present, firstEnabled,
              secondEnabled, static.firstEnabledAfterSecond]
      | true =>
          cases secondEnabled : secondEdit.enabled definition with
          | false =>
              simp [Heap.applyActivationRecordEdit, present, firstEnabled,
                secondEnabled, static.secondEnabledAfterFirst]
          | true =>
              simp [Heap.applyActivationRecordEdit, present, firstEnabled,
                secondEnabled, static.secondEnabledAfterFirst,
                static.firstEnabledAfterSecond,
                static.transformsCommute definition firstEnabled secondEnabled,
                Heap.installActivation]
              rw [FiniteStore.install_same_key_overwrites,
                FiniteStore.install_same_key_overwrites]

theorem ActivationRecordEditsCommuteStatically.symmetric
    {first second : Heap.ActivationRecordEdit}
    (static : ActivationRecordEditsCommuteStatically first second) :
    ActivationRecordEditsCommuteStatically second first :=
  { secondEnabledAfterFirst := static.firstEnabledAfterSecond
    firstEnabledAfterSecond := static.secondEnabledAfterFirst
    transformsCommute := by
      intro definition secondEnabled firstEnabled
      exact (static.transformsCommute definition firstEnabled secondEnabled).symm }

theorem parameterRecordEdits_commuteStatically
    {first second : ParameterId} (different : first ≠ second)
    (firstValue secondValue : ObjRef) :
    ActivationRecordEditsCommuteStatically
      (Heap.parameterRecordEdit first firstValue)
      (Heap.parameterRecordEdit second secondValue) :=
  { secondEnabledAfterFirst := by
      intro definition
      simp only [Heap.parameterRecordEdit, Heap.reflectedParameterTransform]
      rw [definition.parameters.install_away firstValue different.symm]
    firstEnabledAfterSecond := by
      intro definition
      simp only [Heap.parameterRecordEdit, Heap.reflectedParameterTransform]
      rw [definition.parameters.install_away secondValue different]
    transformsCommute := by
      intro definition firstEnabled secondEnabled
      cases firstResult : definition.parameters first with
      | none => simp [Heap.parameterRecordEdit, firstResult] at firstEnabled
      | some oldFirst =>
          cases secondResult : definition.parameters second with
          | none => simp [Heap.parameterRecordEdit, secondResult] at secondEnabled
          | some oldSecond =>
              exact Heap.reflectedParameterTransforms_commute different
                firstValue secondValue definition firstResult secondResult }

theorem localRecordEdits_commuteStatically
    {first second : LocalSlotId} (different : first ≠ second)
    (firstValue secondValue : ObjRef) :
    ActivationRecordEditsCommuteStatically
      (Heap.localRecordEdit first firstValue)
      (Heap.localRecordEdit second secondValue) :=
  { secondEnabledAfterFirst := by
      intro definition
      simp only [Heap.localRecordEdit, Heap.reflectedLocalTransform]
      rw [definition.locals.install_away (.value firstValue) different.symm]
    firstEnabledAfterSecond := by
      intro definition
      simp only [Heap.localRecordEdit, Heap.reflectedLocalTransform]
      rw [definition.locals.install_away (.value secondValue) different]
    transformsCommute := by
      intro definition firstEnabled secondEnabled
      cases firstResult : definition.locals first with
      | none => simp [Heap.localRecordEdit, firstResult] at firstEnabled
      | some oldFirst =>
          cases secondResult : definition.locals second with
          | none => simp [Heap.localRecordEdit, secondResult] at secondEnabled
          | some oldSecond =>
              exact Heap.reflectedLocalTransforms_commute different firstValue
                secondValue definition firstResult secondResult }

theorem parameterAndLocalRecordEdits_commuteStatically
    (parameter : ParameterId) (parameterValue : ObjRef)
    (slot : LocalSlotId) (localValue : ObjRef) :
    ActivationRecordEditsCommuteStatically
      (Heap.parameterRecordEdit parameter parameterValue)
      (Heap.localRecordEdit slot localValue) := by
  constructor <;> intro definition
  · rfl
  · rfl
  · intro _ _
    exact Heap.reflectedParameterAndLocalTransforms_commute parameter
      parameterValue slot localValue definition

theorem parameterAndCurrentClassRecordEdits_commuteStatically
    (parameter : ParameterId) (value : ObjRef) (classId : Option ClassId) :
    ActivationRecordEditsCommuteStatically
      (Heap.parameterRecordEdit parameter value)
      (Heap.currentClassRecordEdit classId) := by
  constructor <;> intro definition
  · rfl
  · rfl
  · intro _ _
    exact Heap.reflectedParameterAndCurrentClassTransforms_commute parameter
      value classId definition

theorem parameterAndContinuationRecordEdits_commuteStatically
    (parameter : ParameterId) (value : ObjRef)
    (continuation : Option ActivationId) :
    ActivationRecordEditsCommuteStatically
      (Heap.parameterRecordEdit parameter value)
      (Heap.continuationRecordEdit continuation) := by
  constructor <;> intro definition
  · rfl
  · rfl
  · intro _ _
    exact Heap.reflectedParameterAndContinuationTransforms_commute parameter
      value continuation definition

theorem localAndCurrentClassRecordEdits_commuteStatically
    (slot : LocalSlotId) (value : ObjRef) (classId : Option ClassId) :
    ActivationRecordEditsCommuteStatically
      (Heap.localRecordEdit slot value)
      (Heap.currentClassRecordEdit classId) := by
  constructor <;> intro definition
  · rfl
  · rfl
  · intro _ _
    exact Heap.reflectedLocalAndCurrentClassTransforms_commute slot value
      classId definition

theorem localAndContinuationRecordEdits_commuteStatically
    (slot : LocalSlotId) (value : ObjRef)
    (continuation : Option ActivationId) :
    ActivationRecordEditsCommuteStatically
      (Heap.localRecordEdit slot value)
      (Heap.continuationRecordEdit continuation) := by
  constructor <;> intro definition
  · rfl
  · rfl
  · intro _ _
    exact Heap.reflectedLocalAndContinuationTransforms_commute slot value
      continuation definition

theorem currentClassAndContinuationRecordEdits_commuteStatically
    (classId : Option ClassId) (continuation : Option ActivationId) :
    ActivationRecordEditsCommuteStatically
      (Heap.currentClassRecordEdit classId)
      (Heap.continuationRecordEdit continuation) := by
  constructor <;> intro definition
  · rfl
  · rfl
  · intro _ _
    rfl

theorem ordinaryActivationCommands_commute_of_sameActivationStatic
    {first second : ReflectionCommand}
    {firstActivation secondActivation : ActivationId}
    {firstEdit secondEdit : Heap.ActivationRecordEdit}
    (firstDecoded : ordinaryActivationRecordEdit? first =
      some (firstActivation, firstEdit))
    (secondDecoded : ordinaryActivationRecordEdit? second =
      some (secondActivation, secondEdit))
    (sameStatic : firstActivation = secondActivation →
      ActivationRecordEditsCommuteStatically firstEdit secondEdit) :
    OptionalCommandsCommute applyActivationCommand first second := by
  intro heap
  have firstApply : ∀ current,
      applyActivationCommand current first = current.applyActivationRecordEdit
        firstActivation firstEdit := fun current =>
    applyActivationCommand_of_ordinary_edit current first firstActivation
      firstEdit firstDecoded
  have secondApply : ∀ current,
      applyActivationCommand current second = current.applyActivationRecordEdit
        secondActivation secondEdit := fun current =>
    applyActivationCommand_of_ordinary_edit current second secondActivation
      secondEdit secondDecoded
  simp only [firstApply, secondApply]
  by_cases different : firstActivation ≠ secondActivation
  · exact heap.applyActivationRecordEdits_distinct_commute_total different
      firstEdit secondEdit
  · have equal : firstActivation = secondActivation :=
      Decidable.not_not.mp different
    subst secondActivation
    exact heap.applyActivationRecordEdits_same_commute_total firstActivation
      firstEdit secondEdit (sameStatic rfl)

theorem Heap.applyActivationRecordEdits_same_commute
    (heap : Heap) (activation : ActivationId)
    (firstEdit secondEdit : ActivationRecordEdit) {definition : ActivationDef}
    (present : heap.activations activation = some definition)
    (firstEnabled : firstEdit.enabled definition = true)
    (secondEnabled : secondEdit.enabled definition = true)
    (secondAfterFirstEnabled :
      secondEdit.enabled (firstEdit.transform definition) = true)
    (firstAfterSecondEnabled :
      firstEdit.enabled (secondEdit.transform definition) = true)
    (transformsCommute :
      secondEdit.transform (firstEdit.transform definition) =
        firstEdit.transform (secondEdit.transform definition)) :
    (do
      let afterFirst ← heap.applyActivationRecordEdit activation firstEdit
      afterFirst.applyActivationRecordEdit activation secondEdit) =
    (do
      let afterSecond ← heap.applyActivationRecordEdit activation secondEdit
      afterSecond.applyActivationRecordEdit activation firstEdit) := by
  simp [Heap.applyActivationRecordEdit, present, firstEnabled, secondEnabled,
    secondAfterFirstEnabled, firstAfterSecondEnabled, transformsCommute,
    Heap.installActivation]
  rw [FiniteStore.install_same_key_overwrites,
    FiniteStore.install_same_key_overwrites]

/-- State-dependent independence certificate for the four ordinary activation
    record edits.  Graph-changing retirement is deliberately outside this
    structure and conflicts through `.activationGraph`. -/
structure ActivationRecordEditsIndependentAt (heap : Heap)
    (firstActivation : ActivationId) (firstEdit : Heap.ActivationRecordEdit)
    (secondActivation : ActivationId)
    (secondEdit : Heap.ActivationRecordEdit) where
  firstDefinition : ActivationDef
  secondDefinition : ActivationDef
  firstPresent :
    heap.activations firstActivation = some firstDefinition
  secondPresent :
    heap.activations secondActivation = some secondDefinition
  firstEnabled : firstEdit.enabled firstDefinition = true
  secondEnabled : secondEdit.enabled secondDefinition = true
  sameActivationSafe : firstActivation = secondActivation →
    secondEdit.enabled (firstEdit.transform firstDefinition) = true ∧
    firstEdit.enabled (secondEdit.transform firstDefinition) = true ∧
    secondEdit.transform (firstEdit.transform firstDefinition) =
      firstEdit.transform (secondEdit.transform firstDefinition)

theorem ActivationRecordEditsIndependentAt.commands_commute
    {heap : Heap} {firstActivation secondActivation : ActivationId}
    {firstEdit secondEdit : Heap.ActivationRecordEdit}
    (independent : ActivationRecordEditsIndependentAt heap firstActivation
      firstEdit secondActivation secondEdit) :
    (do
      let afterFirst ←
        heap.applyActivationRecordEdit firstActivation firstEdit
      afterFirst.applyActivationRecordEdit secondActivation secondEdit) =
    (do
      let afterSecond ←
        heap.applyActivationRecordEdit secondActivation secondEdit
      afterSecond.applyActivationRecordEdit firstActivation firstEdit) := by
  rcases independent with
    ⟨firstDefinition, secondDefinition, firstPresent, secondPresent,
      firstEnabled, secondEnabled, sameActivationSafe⟩
  by_cases equal : firstActivation = secondActivation
  · subst secondActivation
    have definitionsEqual :
        firstDefinition = secondDefinition := by
      rw [firstPresent] at secondPresent
      injection secondPresent
    have safe := sameActivationSafe rfl
    subst secondDefinition
    exact heap.applyActivationRecordEdits_same_commute firstActivation
      firstEdit secondEdit firstPresent firstEnabled secondEnabled safe.1
      safe.2.1 safe.2.2
  · exact heap.applyActivationRecordEdits_distinct_commute equal firstEdit
      secondEdit firstPresent secondPresent firstEnabled secondEnabled

/-- A command-level certificate connecting two concrete ordinary activation
    commands to the record-edit algebra above. -/
structure OrdinaryActivationCommandsIndependentAt (heap : Heap)
    (first second : ReflectionCommand) where
  firstActivation : ActivationId
  secondActivation : ActivationId
  firstEdit : Heap.ActivationRecordEdit
  secondEdit : Heap.ActivationRecordEdit
  firstDecoded :
    ordinaryActivationRecordEdit? first = some (firstActivation, firstEdit)
  secondDecoded :
    ordinaryActivationRecordEdit? second = some (secondActivation, secondEdit)
  recordEditsIndependent : ActivationRecordEditsIndependentAt heap
    firstActivation firstEdit secondActivation secondEdit

theorem OrdinaryActivationCommandsIndependentAt.commands_commute
    {heap : Heap} {first second : ReflectionCommand}
    (independent : OrdinaryActivationCommandsIndependentAt heap first second) :
    ActivationCommandsCommuteAt heap first second := by
  unfold ActivationCommandsCommuteAt
  have firstApply : ∀ current,
      applyActivationCommand current first = current.applyActivationRecordEdit
        independent.firstActivation independent.firstEdit := fun current =>
    applyActivationCommand_of_ordinary_edit current first
      independent.firstActivation independent.firstEdit independent.firstDecoded
  have secondApply : ∀ current,
      applyActivationCommand current second = current.applyActivationRecordEdit
        independent.secondActivation independent.secondEdit := fun current =>
    applyActivationCommand_of_ordinary_edit current second
      independent.secondActivation independent.secondEdit independent.secondDecoded
  simp only [firstApply, secondApply]
  exact independent.recordEditsIndependent.commands_commute

theorem resumePausedActorCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld)
    {firstMirror secondMirror : MirrorId} {firstActor secondActor : ActorId}
    (different : firstActor ≠ secondActor)
    {firstToken secondToken : PauseTokenId}
    {firstConfig secondConfig : SequentialConfig}
    {firstReply secondReply : PromiseId} {firstEvent secondEvent : EventId}
    {firstReason secondReason : DebuggerStopReason}
    (firstPaused : world.runStates firstActor = some
      (.pausedTurn firstConfig firstReply firstEvent firstToken firstReason))
    (secondPaused : world.runStates secondActor = some
      (.pausedTurn secondConfig secondReply secondEvent secondToken secondReason))
    {firstAllocation secondAllocation : AllocationState}
    (firstAllocationPresent :
      world.actorAllocations firstActor = some firstAllocation)
    (secondAllocationPresent :
      world.actorAllocations secondActor = some secondAllocation) :
    DebuggerCommandsCommuteAt materialize program requester world
      (.resumePausedActorAtFullSpeed firstMirror firstActor firstToken)
      (.resumePausedActorAtFullSpeed secondMirror secondActor secondToken) := by
  have firstRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some firstPaused
  have secondRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some secondPaused
  have firstAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some firstAllocationPresent
  have secondAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some secondAllocationPresent
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, firstPaused,
    secondPaused, different, different.symm,
    ActorWorld.resumePausedActorConfiguration, ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different firstRunMember
    secondRunMember]
  rw [world.actorAllocations.install_distinct_commute_of_mem different
    firstAllocationMember secondAllocationMember]
  exact ⟨rfl, rfl⟩

theorem pauseAndResumeActorCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld)
    {pauseMirror resumeMirror : MirrorId} {pausedActor resumedActor : ActorId}
    (different : pausedActor ≠ resumedActor)
    (requesterDifferent : requester ≠ pausedActor)
    (reason : DebuggerStopReason)
    {runningConfig resumedConfig : SequentialConfig}
    {runningReply resumedReply : PromiseId}
    {runningEvent resumedEvent : EventId}
    {token : PauseTokenId} {oldReason : DebuggerStopReason}
    {rest : ActivationStack} {frame : ActivationFrame}
    (running : world.runStates pausedActor = some
      (.runningTurn runningConfig runningReply runningEvent))
    (nonempty : runningConfig.stack = .push rest frame)
    (paused : world.runStates resumedActor = some
      (.pausedTurn resumedConfig resumedReply resumedEvent token oldReason))
    :
    DebuggerCommandsCommuteAt materialize program requester world
      (.pauseActor pauseMirror pausedActor reason)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) := by
  have pausedRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some running
  have resumedRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some paused
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, running, paused,
    requesterDifferent, nonempty, different, different.symm,
    ActorWorld.pauseRunningActor, ActorWorld.resumePausedActorConfiguration,
    ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different pausedRunMember
    resumedRunMember]

theorem replaceCurrentStackAndResumeCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (world : ActorWorld) {replaceMirror resumeMirror : MirrorId}
    {replacedActor resumedActor : ActorId}
    (different : replacedActor ≠ resumedActor)
    (template : StackTemplate)
    {runningConfig resumedConfig replacementConfig : SequentialConfig}
    {runningReply resumedReply : PromiseId}
    {runningEvent resumedEvent : EventId}
    {token : PauseTokenId} {reason : DebuggerStopReason}
    (running : world.runStates replacedActor = some
      (.runningTurn runningConfig runningReply runningEvent))
    (paused : world.runStates resumedActor = some
      (.pausedTurn resumedConfig resumedReply resumedEvent token reason))
    (materialized : materialize program runningConfig.allocation
      runningConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control))
    {firstAllocation secondAllocation : AllocationState}
    (firstAllocationPresent :
      world.actorAllocations replacedActor = some firstAllocation)
    (secondAllocationPresent :
      world.actorAllocations resumedActor = some secondAllocation) :
    DebuggerCommandsCommuteAt materialize program replacedActor world
      (.replaceCurrentActorStack replaceMirror replacedActor template)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) := by
  have firstRunMember := world.runStates.mem_domain_of_lookup_eq_some running
  have secondRunMember := world.runStates.mem_domain_of_lookup_eq_some paused
  have firstAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some firstAllocationPresent
  have secondAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some secondAllocationPresent
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, running, paused,
    materialized, different, different.symm,
    ActorWorld.replaceRunningActorConfiguration,
    ActorWorld.resumePausedActorConfiguration, ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different firstRunMember
    secondRunMember]
  rw [world.actorAllocations.install_distinct_commute_of_mem different
    firstAllocationMember secondAllocationMember]
  exact ⟨rfl, rfl⟩

theorem replaceAndResumeStackAndResumeCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld)
    {replaceMirror resumeMirror : MirrorId}
    {replacedActor resumedActor : ActorId}
    (different : replacedActor ≠ resumedActor)
    (template : StackTemplate)
    {replacedConfig resumedConfig replacementConfig : SequentialConfig}
    {replacedReply resumedReply : PromiseId}
    {replacedEvent resumedEvent : EventId}
    {replacedToken resumedToken : PauseTokenId}
    {replacedReason resumedReason : DebuggerStopReason}
    (replacedPaused : world.runStates replacedActor = some
      (.pausedTurn replacedConfig replacedReply replacedEvent replacedToken
        replacedReason))
    (resumedPaused : world.runStates resumedActor = some
      (.pausedTurn resumedConfig resumedReply resumedEvent resumedToken
        resumedReason))
    (materialized : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control))
    {firstAllocation secondAllocation : AllocationState}
    (firstAllocationPresent :
      world.actorAllocations replacedActor = some firstAllocation)
    (secondAllocationPresent :
      world.actorAllocations resumedActor = some secondAllocation) :
    DebuggerCommandsCommuteAt materialize program requester world
      (.replaceAndResumePausedActorStack replaceMirror replacedActor
        replacedToken template)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor resumedToken) := by
  have firstRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some replacedPaused
  have secondRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some resumedPaused
  have firstAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some firstAllocationPresent
  have secondAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some secondAllocationPresent
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, replacedPaused,
    resumedPaused, materialized, different, different.symm,
    ActorWorld.resumePausedActorConfiguration, ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different firstRunMember
    secondRunMember]
  rw [world.actorAllocations.install_distinct_commute_of_mem different
    firstAllocationMember secondAllocationMember]
  exact ⟨rfl, rfl⟩

theorem replacePausedStackAndResumeCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld)
    {replaceMirror resumeMirror : MirrorId}
    {replacedActor resumedActor : ActorId}
    (different : replacedActor ≠ resumedActor)
    (template : StackTemplate)
    {replacedConfig resumedConfig replacementConfig : SequentialConfig}
    {replacedReply resumedReply : PromiseId}
    {replacedEvent resumedEvent : EventId}
    {replacedToken resumedToken : PauseTokenId}
    {replacedReason resumedReason : DebuggerStopReason}
    (replacedPaused : world.runStates replacedActor = some
      (.pausedTurn replacedConfig replacedReply replacedEvent replacedToken
        replacedReason))
    (resumedPaused : world.runStates resumedActor = some
      (.pausedTurn resumedConfig resumedReply resumedEvent resumedToken
        resumedReason))
    (materialized : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control))
    {firstAllocation secondAllocation : AllocationState}
    (firstAllocationPresent :
      world.actorAllocations replacedActor = some firstAllocation)
    (secondAllocationPresent :
      world.actorAllocations resumedActor = some secondAllocation) :
    DebuggerCommandsCommuteAt materialize program requester world
      (.replacePausedActorStack replaceMirror replacedActor replacedToken
        template)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor resumedToken) := by
  have firstRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some replacedPaused
  have secondRunMember :=
    world.runStates.mem_domain_of_lookup_eq_some resumedPaused
  have firstAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some firstAllocationPresent
  have secondAllocationMember :=
    world.actorAllocations.mem_domain_of_lookup_eq_some secondAllocationPresent
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, replacedPaused,
    resumedPaused, materialized, different, different.symm,
    ActorWorld.replacePausedActorConfiguration,
    ActorWorld.resumePausedActorConfiguration, ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different firstRunMember
    secondRunMember]
  rw [world.actorAllocations.install_distinct_commute_of_mem different
    firstAllocationMember secondAllocationMember]
  exact ⟨rfl, rfl⟩

theorem pauseAndReplaceCurrentStackCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (world : ActorWorld) {pauseMirror replaceMirror : MirrorId}
    {pausedActor replacedActor : ActorId}
    (different : pausedActor ≠ replacedActor)
    (reason : DebuggerStopReason) (template : StackTemplate)
    {pausedConfig replacedConfig replacementConfig : SequentialConfig}
    {pausedReply replacedReply : PromiseId}
    {pausedEvent replacedEvent : EventId}
    {rest : ActivationStack} {frame : ActivationFrame}
    (pausedRunning : world.runStates pausedActor = some
      (.runningTurn pausedConfig pausedReply pausedEvent))
    (nonempty : pausedConfig.stack = .push rest frame)
    (replacedRunning : world.runStates replacedActor = some
      (.runningTurn replacedConfig replacedReply replacedEvent))
    (materialized : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control)) :
    DebuggerCommandsCommuteAt materialize program replacedActor world
      (.pauseActor pauseMirror pausedActor reason)
      (.replaceCurrentActorStack replaceMirror replacedActor template) := by
  have pauseMember :=
    world.runStates.mem_domain_of_lookup_eq_some pausedRunning
  have replaceMember :=
    world.runStates.mem_domain_of_lookup_eq_some replacedRunning
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, pausedRunning,
    replacedRunning, different, different.symm, nonempty, materialized,
    ActorWorld.pauseRunningActor,
    ActorWorld.replaceRunningActorConfiguration, ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different pauseMember
    replaceMember]

theorem pauseAndReplaceAndResumeCommands_distinct_commuteAt
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld)
    {pauseMirror replaceMirror : MirrorId}
    {pausedActor replacedActor : ActorId}
    (different : pausedActor ≠ replacedActor)
    (requesterDifferent : requester ≠ pausedActor)
    (reason : DebuggerStopReason) (template : StackTemplate)
    {pausedConfig replacedConfig replacementConfig : SequentialConfig}
    {pausedReply replacedReply : PromiseId}
    {pausedEvent replacedEvent : EventId}
    {token : PauseTokenId} {oldReason : DebuggerStopReason}
    {rest : ActivationStack} {frame : ActivationFrame}
    (pausedRunning : world.runStates pausedActor = some
      (.runningTurn pausedConfig pausedReply pausedEvent))
    (nonempty : pausedConfig.stack = .push rest frame)
    (replacedPaused : world.runStates replacedActor = some
      (.pausedTurn replacedConfig replacedReply replacedEvent token oldReason))
    (materialized : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control)) :
    DebuggerCommandsCommuteAt materialize program requester world
      (.pauseActor pauseMirror pausedActor reason)
      (.replaceAndResumePausedActorStack replaceMirror replacedActor token
        template) := by
  have pauseMember :=
    world.runStates.mem_domain_of_lookup_eq_some pausedRunning
  have replaceMember :=
    world.runStates.mem_domain_of_lookup_eq_some replacedPaused
  simp [DebuggerCommandsCommuteAt, applyDebuggerCommand, pausedRunning,
    replacedPaused, requesterDifferent, different, different.symm, nonempty,
    materialized, ActorWorld.pauseRunningActor,
    ActorWorld.resumePausedActorConfiguration, ActorWorld.advanceRunningTurn]
  rw [world.runStates.install_distinct_commute_of_mem different pauseMember
    replaceMember]

@[simp] theorem ActorWorld.pauseRunningActor_runState_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) :
    (world.pauseRunningActor actor config reply event reason).runStates other =
      world.runStates other := by
  simp [ActorWorld.pauseRunningActor, different]

@[simp] theorem ActorWorld.advanceRunningTurn_runState_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    (world.advanceRunningTurn actor config reply event).runStates other =
      world.runStates other := by
  simp [ActorWorld.advanceRunningTurn, different]

@[simp] theorem ActorWorld.advanceRunningTurn_allocation_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    (world.advanceRunningTurn actor config reply event).actorAllocations other =
      world.actorAllocations other := by
  simp [ActorWorld.advanceRunningTurn, different]

@[simp] theorem ActorWorld.replacePausedActorConfiguration_runState_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) :
    (ActorWorld.replacePausedActorConfiguration world actor config reply event
      reason).runStates other = world.runStates other := by
  simp [ActorWorld.replacePausedActorConfiguration, different]

@[simp] theorem ActorWorld.replacePausedActorConfiguration_allocation_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId)
    (reason : DebuggerStopReason) :
    (ActorWorld.replacePausedActorConfiguration world actor config reply event
      reason).actorAllocations other = world.actorAllocations other := by
  simp [ActorWorld.replacePausedActorConfiguration, different]

@[simp] theorem ActorWorld.resumePausedActorConfiguration_runState_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    (world.resumePausedActorConfiguration actor config reply event).runStates
        other = world.runStates other := by
  exact world.advanceRunningTurn_runState_away different config reply event

@[simp] theorem ActorWorld.resumePausedActorConfiguration_allocation_away
    (world : ActorWorld) {actor other : ActorId} (different : other ≠ actor)
    (config : SequentialConfig) (reply : PromiseId) (event : EventId) :
    (world.resumePausedActorConfiguration actor config reply event).actorAllocations
        other = world.actorAllocations other := by
  exact world.advanceRunningTurn_allocation_away different config reply event

theorem applyDebuggerCommand_preserves_runState_away
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {command : ReflectionCommand} {actor other : ActorId}
    (target : command.debuggerActor? = some actor)
    (different : other ≠ actor) {before after : ActorWorld}
    (result : applyDebuggerCommand materialize program requester before command =
      some after) :
    after.runStates other = before.runStates other := by
  cases command <;> simp [ReflectionCommand.debuggerActor?] at target
  all_goals try contradiction
  case pauseActor mirror targetActor reason =>
    subst targetActor
    cases stateResult : before.runStates actor with
    | none => simp [applyDebuggerCommand, stateResult] at result
    | some state =>
        cases state with
        | idle => simp [applyDebuggerCommand, stateResult] at result
        | pausedTurn => simp [applyDebuggerCommand, stateResult] at result
        | runningTurn config reply event =>
            by_cases self : requester = actor
            · simp [applyDebuggerCommand, stateResult, self] at result
            · cases stackResult : config.stack with
              | empty =>
                  simp [applyDebuggerCommand, stateResult, self, stackResult]
                    at result
              | push rest frame =>
                  simp [applyDebuggerCommand, stateResult, self, stackResult]
                    at result
                  subst after
                  exact before.pauseRunningActor_runState_away different config
                    reply event reason
  case replaceCurrentActorStack mirror targetActor template =>
    subst targetActor
    by_cases self : requester = actor
    · cases stateResult : before.runStates actor with
      | none => simp [applyDebuggerCommand, self, stateResult] at result
      | some state =>
          cases state with
          | idle => simp [applyDebuggerCommand, self, stateResult] at result
          | pausedTurn =>
              simp [applyDebuggerCommand, self, stateResult] at result
          | runningTurn config reply event =>
              cases materializedResult : materialize program config.allocation
                  config.stack template with
              | none =>
                  simp [applyDebuggerCommand, self, stateResult,
                    materializedResult] at result
              | some materialized =>
                  rcases materialized with ⟨allocation, stack, control⟩
                  simp [applyDebuggerCommand, self, stateResult,
                    materializedResult] at result
                  subst after
                  exact before.advanceRunningTurn_runState_away different _
                    reply event
    · simp [applyDebuggerCommand, self] at result
  case replacePausedActorStack mirror targetActor token template =>
    subst targetActor
    cases stateResult : before.runStates actor with
    | none => simp [applyDebuggerCommand, stateResult] at result
    | some state =>
        cases state with
        | idle => simp [applyDebuggerCommand, stateResult] at result
        | runningTurn => simp [applyDebuggerCommand, stateResult] at result
        | pausedTurn config reply event currentToken reason =>
            by_cases current : token = currentToken
            · cases materializedResult : materialize program config.allocation
                  config.stack template with
              | none =>
                  simp [applyDebuggerCommand, stateResult, current,
                    materializedResult] at result
              | some materialized =>
                  rcases materialized with ⟨allocation, stack, control⟩
                  simp [applyDebuggerCommand, stateResult, current,
                    materializedResult] at result
                  subst after
                  exact before.replacePausedActorConfiguration_runState_away
                    different _ reply event reason
            · simp [applyDebuggerCommand, stateResult, current] at result

  case resumePausedActorAtFullSpeed mirror targetActor token =>
    subst targetActor
    cases stateResult : before.runStates actor with
    | none => simp [applyDebuggerCommand, stateResult] at result
    | some state =>
        cases state with
        | idle => simp [applyDebuggerCommand, stateResult] at result
        | runningTurn => simp [applyDebuggerCommand, stateResult] at result
        | pausedTurn config reply event currentToken reason =>
            by_cases current : token = currentToken
            · simp [applyDebuggerCommand, stateResult, current] at result
              subst after
              exact before.resumePausedActorConfiguration_runState_away
                different config reply event
            · simp [applyDebuggerCommand, stateResult, current] at result
  case replaceAndResumePausedActorStack mirror targetActor token template =>
    subst targetActor
    cases stateResult : before.runStates actor with
    | none => simp [applyDebuggerCommand, stateResult] at result
    | some state =>
        cases state with
        | idle => simp [applyDebuggerCommand, stateResult] at result
        | runningTurn => simp [applyDebuggerCommand, stateResult] at result
        | pausedTurn config reply event currentToken reason =>
            by_cases current : token = currentToken
            · cases materializedResult : materialize program config.allocation
                  config.stack template with
              | none =>
                  simp [applyDebuggerCommand, stateResult, current,
                    materializedResult] at result
              | some materialized =>
                  rcases materialized with ⟨allocation, stack, control⟩
                  simp [applyDebuggerCommand, stateResult, current,
                    materializedResult] at result
                  subst after
                  exact before.resumePausedActorConfiguration_runState_away
                    different _ reply event
            · simp [applyDebuggerCommand, stateResult, current] at result

theorem applyDebuggerCommand_isSome_of_target_runState_eq
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {command : ReflectionCommand} {actor : ActorId}
    (target : command.debuggerActor? = some actor)
    {left right : ActorWorld}
    (runStateEqual : left.runStates actor = right.runStates actor) :
    (applyDebuggerCommand materialize program requester left command).isSome =
      (applyDebuggerCommand materialize program requester right command).isSome := by
  cases command <;> simp [ReflectionCommand.debuggerActor?] at target
  all_goals try contradiction
  all_goals subst actor
  all_goals simp only [applyDebuggerCommand]
  all_goals rw [runStateEqual]
  all_goals cases stateResult : right.runStates _ with
    | none => simp [stateResult]
    | some state =>
        cases state <;> simp [stateResult]
        all_goals split <;> simp_all
        all_goals try (split <;> simp_all)
        all_goals cases materialized : materialize program _ _ _ <;> rfl

theorem debuggerCommands_distinct_commuteUnder_of_success
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {first second : ReflectionCommand}
    {firstActor secondActor : ActorId}
    (firstTarget : first.debuggerActor? = some firstActor)
    (secondTarget : second.debuggerActor? = some secondActor)
    (different : firstActor ≠ secondActor)
    (successCommutes : ∀ (world : ActorWorld),
      ActorStoreDomainsCoherent world →
      (applyDebuggerCommand materialize program requester world first).isSome =
        true →
      (applyDebuggerCommand materialize program requester world second).isSome =
        true →
      DebuggerCommandsCommuteAt materialize program requester world first
        second) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      first second := by
  intro world coherent
  change DebuggerCommandsCommuteAt materialize program requester world first
    second
  cases firstResult : applyDebuggerCommand materialize program requester world
      first with
  | none =>
      cases secondResult : applyDebuggerCommand materialize program requester
          world second with
      | none => simp [DebuggerCommandsCommuteAt, firstResult, secondResult]
      | some afterSecond =>
          have stateEqual := applyDebuggerCommand_preserves_runState_away
            materialize program requester secondTarget different secondResult
          have applicability := applyDebuggerCommand_isSome_of_target_runState_eq
            materialize program requester firstTarget stateEqual.symm
          rw [firstResult] at applicability
          cases afterResult : applyDebuggerCommand materialize program requester
              afterSecond first with
          | none =>
              simp [DebuggerCommandsCommuteAt, firstResult, secondResult,
                afterResult]
          | some final => simp [afterResult] at applicability
  | some afterFirst =>
      cases secondResult : applyDebuggerCommand materialize program requester
          world second with
      | none =>
          have stateEqual := applyDebuggerCommand_preserves_runState_away
            materialize program requester firstTarget different.symm firstResult
          have applicability := applyDebuggerCommand_isSome_of_target_runState_eq
            materialize program requester secondTarget stateEqual.symm
          rw [secondResult] at applicability
          cases afterResult : applyDebuggerCommand materialize program requester
              afterFirst second with
          | none =>
              simp [DebuggerCommandsCommuteAt, firstResult, secondResult,
                afterResult]
          | some final => simp [afterResult] at applicability
      | some afterSecond =>
          exact successCommutes world coherent (by simp [firstResult])
            (by simp [secondResult])

theorem pauseActor_success_witnesses
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) (mirror : MirrorId)
    (actor : ActorId) (reason : DebuggerStopReason)
    (success : (applyDebuggerCommand materialize program requester world
      (.pauseActor mirror actor reason)).isSome = true) :
    ∃ config reply event rest frame,
      world.runStates actor = some (.runningTurn config reply event) ∧
      requester ≠ actor ∧ config.stack = .push rest frame := by
  cases stateResult : world.runStates actor with
  | none => simp [applyDebuggerCommand, stateResult] at success
  | some state =>
      cases state with
      | idle => simp [applyDebuggerCommand, stateResult] at success
      | pausedTurn => simp [applyDebuggerCommand, stateResult] at success
      | runningTurn config reply event =>
          by_cases self : requester = actor
          · simp [applyDebuggerCommand, stateResult, self] at success
          · cases stackResult : config.stack with
            | empty =>
                simp [applyDebuggerCommand, stateResult, self, stackResult] at success
            | push rest frame =>
                exact ⟨config, reply, event, rest, frame, rfl, self,
                  stackResult⟩

theorem replaceCurrentActorStack_success_witnesses
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) (mirror : MirrorId)
    (actor : ActorId) (template : StackTemplate)
    (success : (applyDebuggerCommand materialize program requester world
      (.replaceCurrentActorStack mirror actor template)).isSome = true) :
    requester = actor ∧ ∃ config reply event materialized,
      world.runStates actor = some (.runningTurn config reply event) ∧
      materialize program config.allocation config.stack template =
        some materialized := by
  by_cases self : requester = actor
  · refine ⟨self, ?_⟩
    cases stateResult : world.runStates actor with
    | none => simp [applyDebuggerCommand, self, stateResult] at success
    | some state =>
        cases state with
        | idle => simp [applyDebuggerCommand, self, stateResult] at success
        | pausedTurn =>
            simp [applyDebuggerCommand, self, stateResult] at success
        | runningTurn config reply event =>
            cases materializedResult : materialize program config.allocation
                config.stack template with
            | none =>
                simp [applyDebuggerCommand, self, stateResult,
                  materializedResult] at success
            | some materialized =>
                exact ⟨config, reply, event, materialized, rfl,
                  materializedResult⟩
  · simp [applyDebuggerCommand, self] at success

theorem replacePausedActorStack_success_witnesses
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) (mirror : MirrorId)
    (actor : ActorId) (token : PauseTokenId) (template : StackTemplate)
    (success : (applyDebuggerCommand materialize program requester world
      (.replacePausedActorStack mirror actor token template)).isSome = true) :
    ∃ config reply event reason materialized,
      world.runStates actor = some
        (.pausedTurn config reply event token reason) ∧
      materialize program config.allocation config.stack template =
        some materialized := by
  cases stateResult : world.runStates actor with
  | none => simp [applyDebuggerCommand, stateResult] at success
  | some state =>
      cases state with
      | idle => simp [applyDebuggerCommand, stateResult] at success
      | runningTurn => simp [applyDebuggerCommand, stateResult] at success
      | pausedTurn config reply event currentToken reason =>
          by_cases current : token = currentToken
          · subst currentToken
            cases materializedResult : materialize program config.allocation
                config.stack template with
            | none =>
                simp [applyDebuggerCommand, stateResult,
                  materializedResult] at success
            | some materialized =>
                exact ⟨config, reply, event, reason, materialized, rfl,
                  materializedResult⟩
          · simp [applyDebuggerCommand, stateResult, current] at success

theorem resumePausedActorAtFullSpeed_success_witnesses
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) (mirror : MirrorId)
    (actor : ActorId) (token : PauseTokenId)
    (success : (applyDebuggerCommand materialize program requester world
      (.resumePausedActorAtFullSpeed mirror actor token)).isSome = true) :
    ∃ config reply event reason,
      world.runStates actor = some
        (.pausedTurn config reply event token reason) := by
  cases stateResult : world.runStates actor with
  | none => simp [applyDebuggerCommand, stateResult] at success
  | some state =>
      cases state with
      | idle => simp [applyDebuggerCommand, stateResult] at success
      | runningTurn => simp [applyDebuggerCommand, stateResult] at success
      | pausedTurn config reply event currentToken reason =>
          by_cases current : token = currentToken
          · subst currentToken
            exact ⟨config, reply, event, reason, rfl⟩
          · simp [applyDebuggerCommand, stateResult, current] at success

theorem replaceAndResumePausedActorStack_success_witnesses
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) (mirror : MirrorId)
    (actor : ActorId) (token : PauseTokenId) (template : StackTemplate)
    (success : (applyDebuggerCommand materialize program requester world
      (.replaceAndResumePausedActorStack mirror actor token template)).isSome =
        true) :
    ∃ config reply event reason materialized,
      world.runStates actor = some
        (.pausedTurn config reply event token reason) ∧
      materialize program config.allocation config.stack template =
        some materialized := by
  cases stateResult : world.runStates actor with
  | none => simp [applyDebuggerCommand, stateResult] at success
  | some state =>
      cases state with
      | idle => simp [applyDebuggerCommand, stateResult] at success
      | runningTurn => simp [applyDebuggerCommand, stateResult] at success
      | pausedTurn config reply event currentToken reason =>
          by_cases current : token = currentToken
          · subst currentToken
            cases materializedResult : materialize program config.allocation
                config.stack template with
            | none =>
                simp [applyDebuggerCommand, stateResult,
                  materializedResult] at success
            | some materialized =>
                exact ⟨config, reply, event, reason, materialized, rfl,
                  materializedResult⟩
          · simp [applyDebuggerCommand, stateResult, current] at success

theorem pauseAndResumeActorCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {pauseMirror resumeMirror : MirrorId}
    {pausedActor resumedActor : ActorId}
    (different : pausedActor ≠ resumedActor)
    (reason : DebuggerStopReason) (token : PauseTokenId) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.pauseActor pauseMirror pausedActor reason)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) := by
  intro world coherent
  change DebuggerCommandsCommuteAt materialize program requester world
    (.pauseActor pauseMirror pausedActor reason)
    (.resumePausedActorAtFullSpeed resumeMirror resumedActor token)
  unfold DebuggerCommandsCommuteAt
  cases pausedStateResult : world.runStates pausedActor with
  | none =>
      cases secondResult : applyDebuggerCommand materialize program requester
          world (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) with
      | none =>
          simp [applyDebuggerCommand, pausedStateResult]
      | some afterSecond =>
          have stateEqual := applyDebuggerCommand_preserves_runState_away
            materialize program requester (command :=
              .resumePausedActorAtFullSpeed resumeMirror resumedActor token)
              (actor := resumedActor) (other := pausedActor) rfl different
              secondResult
          simp [applyDebuggerCommand, pausedStateResult, stateEqual]
  | some pausedState =>
      cases pausedState with
      | idle =>
          cases secondResult : applyDebuggerCommand materialize program requester
              world (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) with
          | none =>
              simp [applyDebuggerCommand, pausedStateResult]
          | some afterSecond =>
              have stateEqual := applyDebuggerCommand_preserves_runState_away
                materialize program requester (command :=
                  .resumePausedActorAtFullSpeed resumeMirror resumedActor token)
                  (actor := resumedActor) (other := pausedActor) rfl different
                  secondResult
              simp [applyDebuggerCommand, pausedStateResult, stateEqual]
      | pausedTurn =>
          cases secondResult : applyDebuggerCommand materialize program requester
              world (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) with
          | none =>
              simp [applyDebuggerCommand, pausedStateResult]
          | some afterSecond =>
              have stateEqual := applyDebuggerCommand_preserves_runState_away
                materialize program requester (command :=
                  .resumePausedActorAtFullSpeed resumeMirror resumedActor token)
                  (actor := resumedActor) (other := pausedActor) rfl different
                  secondResult
              simp [applyDebuggerCommand, pausedStateResult, stateEqual]
      | runningTurn pausedConfig pausedReply pausedEvent =>
          by_cases requesterDifferent : requester ≠ pausedActor
          · cases stackResult : pausedConfig.stack with
            | empty =>
                cases secondResult : applyDebuggerCommand materialize program
                    requester world (.resumePausedActorAtFullSpeed resumeMirror
                      resumedActor token) with
                | none =>
                    simp [applyDebuggerCommand, pausedStateResult,
                      requesterDifferent, stackResult]
                | some afterSecond =>
                    have stateEqual :=
                      applyDebuggerCommand_preserves_runState_away materialize
                        program requester (command :=
                          .resumePausedActorAtFullSpeed resumeMirror resumedActor
                            token) (actor := resumedActor) (other := pausedActor)
                        rfl different secondResult
                    simp [applyDebuggerCommand, pausedStateResult,
                      requesterDifferent, stackResult, stateEqual]
            | push rest frame =>
                cases resumedStateResult : world.runStates resumedActor with
                | none =>
                    simp [applyDebuggerCommand, pausedStateResult,
                      resumedStateResult, requesterDifferent, stackResult,
                      different, different.symm]
                | some resumedState =>
                    cases resumedState with
                    | idle =>
                        simp [applyDebuggerCommand, pausedStateResult,
                          resumedStateResult, requesterDifferent, stackResult,
                          different, different.symm]
                    | runningTurn =>
                        simp [applyDebuggerCommand, pausedStateResult,
                          resumedStateResult, requesterDifferent, stackResult,
                          different, different.symm]
                    | pausedTurn resumedConfig resumedReply resumedEvent
                        currentToken oldReason =>
                        by_cases current : token = currentToken
                        · subst currentToken
                          exact pauseAndResumeActorCommands_distinct_commuteAt
                            materialize program requester world different
                            requesterDifferent reason pausedStateResult
                            stackResult resumedStateResult
                        · simp [applyDebuggerCommand, pausedStateResult,
                            resumedStateResult, requesterDifferent, stackResult,
                            current, different, different.symm]
          · have requesterEqual : requester = pausedActor :=
              Decidable.not_not.mp requesterDifferent
            subst requester
            cases secondResult : applyDebuggerCommand materialize program
                pausedActor world (.resumePausedActorAtFullSpeed resumeMirror
                  resumedActor token) with
            | none =>
                simp [applyDebuggerCommand, pausedStateResult]
            | some afterSecond =>
                have stateEqual :=
                  applyDebuggerCommand_preserves_runState_away materialize
                    program pausedActor (command :=
                      .resumePausedActorAtFullSpeed resumeMirror resumedActor
                        token) (actor := resumedActor) (other := pausedActor)
                    rfl different secondResult
                simp [applyDebuggerCommand, pausedStateResult, stateEqual]

theorem resumePausedActorCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {firstMirror secondMirror : MirrorId}
    {firstActor secondActor : ActorId} (different : firstActor ≠ secondActor)
    (firstToken secondToken : PauseTokenId) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.resumePausedActorAtFullSpeed firstMirror firstActor firstToken)
      (.resumePausedActorAtFullSpeed secondMirror secondActor secondToken) := by
  apply debuggerCommands_distinct_commuteUnder_of_success materialize program
    requester rfl rfl different
  intro world coherent firstSuccess secondSuccess
  cases firstStateResult : world.runStates firstActor with
  | none => simp [applyDebuggerCommand, firstStateResult] at firstSuccess
  | some firstState =>
      cases firstState with
      | idle => simp [applyDebuggerCommand, firstStateResult] at firstSuccess
      | runningTurn =>
          simp [applyDebuggerCommand, firstStateResult] at firstSuccess
      | pausedTurn firstConfig firstReply firstEvent currentFirstToken
          firstReason =>
          by_cases firstCurrent : firstToken = currentFirstToken
          · subst currentFirstToken
            cases secondStateResult : world.runStates secondActor with
            | none =>
                simp [applyDebuggerCommand, secondStateResult] at secondSuccess
            | some secondState =>
                cases secondState with
                | idle =>
                    simp [applyDebuggerCommand, secondStateResult] at secondSuccess
                | runningTurn =>
                    simp [applyDebuggerCommand, secondStateResult] at secondSuccess
                | pausedTurn secondConfig secondReply secondEvent
                    currentSecondToken secondReason =>
                    by_cases secondCurrent : secondToken = currentSecondToken
                    · subst currentSecondToken
                      have firstMember :=
                        coherent.allocation_member_of_runState firstStateResult
                      have secondMember :=
                        coherent.allocation_member_of_runState secondStateResult
                      rcases world.actorAllocations.exists_value_of_mem_domain
                          firstMember with ⟨firstAllocation, firstPresent⟩
                      rcases world.actorAllocations.exists_value_of_mem_domain
                          secondMember with ⟨secondAllocation, secondPresent⟩
                      exact resumePausedActorCommands_distinct_commuteAt
                        materialize program requester world different
                        firstStateResult secondStateResult firstPresent
                        secondPresent
                    · simp [applyDebuggerCommand, secondStateResult,
                        secondCurrent] at secondSuccess
          · simp [applyDebuggerCommand, firstStateResult, firstCurrent] at firstSuccess

theorem pauseAndReplaceCurrentStackCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId)
    {pauseMirror replaceMirror : MirrorId} {pausedActor replacedActor : ActorId}
    (different : pausedActor ≠ replacedActor) (reason : DebuggerStopReason)
    (template : StackTemplate) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.pauseActor pauseMirror pausedActor reason)
      (.replaceCurrentActorStack replaceMirror replacedActor template) := by
  apply debuggerCommands_distinct_commuteUnder_of_success materialize program
    requester rfl rfl different
  intro world coherent pauseSuccess replaceSuccess
  rcases pauseActor_success_witnesses materialize program requester world
      pauseMirror pausedActor reason pauseSuccess with
    ⟨pausedConfig, pausedReply, pausedEvent, rest, frame, pausedRunning,
      requesterDifferent, nonempty⟩
  rcases replaceCurrentActorStack_success_witnesses materialize program
      requester world replaceMirror replacedActor template replaceSuccess with
    ⟨requesterEqual, replacedConfig, replacedReply, replacedEvent, materialized,
      replacedRunning, materializedResult⟩
  subst requester
  rcases materialized with ⟨allocation, stack, control⟩
  let replacementConfig : SequentialConfig := ⟨allocation, stack, control⟩
  have materializedConfig : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control) := materializedResult
  exact pauseAndReplaceCurrentStackCommands_distinct_commuteAt materialize
    program world different reason template pausedRunning nonempty
    replacedRunning materializedConfig

theorem pauseAndReplaceAndResumeCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {pauseMirror replaceMirror : MirrorId}
    {pausedActor replacedActor : ActorId}
    (different : pausedActor ≠ replacedActor) (reason : DebuggerStopReason)
    (token : PauseTokenId) (template : StackTemplate) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.pauseActor pauseMirror pausedActor reason)
      (.replaceAndResumePausedActorStack replaceMirror replacedActor token
        template) := by
  apply debuggerCommands_distinct_commuteUnder_of_success materialize program
    requester rfl rfl different
  intro world coherent pauseSuccess replaceSuccess
  rcases pauseActor_success_witnesses materialize program requester world
      pauseMirror pausedActor reason pauseSuccess with
    ⟨pausedConfig, pausedReply, pausedEvent, rest, frame, pausedRunning,
      requesterDifferent, nonempty⟩
  rcases replaceAndResumePausedActorStack_success_witnesses materialize program
      requester world replaceMirror replacedActor token template replaceSuccess with
    ⟨replacedConfig, replacedReply, replacedEvent, oldReason, materialized,
      replacedPaused, materializedResult⟩
  rcases materialized with ⟨allocation, stack, control⟩
  let replacementConfig : SequentialConfig := ⟨allocation, stack, control⟩
  have materializedConfig : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control) := materializedResult
  exact pauseAndReplaceAndResumeCommands_distinct_commuteAt materialize program
    requester world different requesterDifferent reason template pausedRunning
    nonempty replacedPaused materializedConfig

theorem replaceCurrentStackAndResumeCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {replaceMirror resumeMirror : MirrorId}
    {replacedActor resumedActor : ActorId}
    (different : replacedActor ≠ resumedActor) (template : StackTemplate)
    (token : PauseTokenId) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.replaceCurrentActorStack replaceMirror replacedActor template)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor token) := by
  apply debuggerCommands_distinct_commuteUnder_of_success materialize program
    requester rfl rfl different
  intro world coherent replaceSuccess resumeSuccess
  rcases replaceCurrentActorStack_success_witnesses materialize program
      requester world replaceMirror replacedActor template replaceSuccess with
    ⟨requesterEqual, runningConfig, runningReply, runningEvent, materialized,
      running, materializedResult⟩
  subst requester
  rcases resumePausedActorAtFullSpeed_success_witnesses materialize program
      replacedActor world resumeMirror resumedActor token resumeSuccess with
    ⟨resumedConfig, resumedReply, resumedEvent, reason, paused⟩
  rcases materialized with ⟨allocation, stack, control⟩
  let replacementConfig : SequentialConfig := ⟨allocation, stack, control⟩
  have materializedConfig : materialize program runningConfig.allocation
      runningConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control) := materializedResult
  have firstMember := coherent.allocation_member_of_runState running
  have secondMember := coherent.allocation_member_of_runState paused
  rcases world.actorAllocations.exists_value_of_mem_domain firstMember with
    ⟨firstAllocation, firstPresent⟩
  rcases world.actorAllocations.exists_value_of_mem_domain secondMember with
    ⟨secondAllocation, secondPresent⟩
  exact replaceCurrentStackAndResumeCommands_distinct_commuteAt materialize
    program world different template running paused materializedConfig
    firstPresent secondPresent

theorem replacePausedStackAndResumeCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {replaceMirror resumeMirror : MirrorId}
    {replacedActor resumedActor : ActorId}
    (different : replacedActor ≠ resumedActor) (replaceToken : PauseTokenId)
    (template : StackTemplate) (resumeToken : PauseTokenId) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.replacePausedActorStack replaceMirror replacedActor replaceToken
        template)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor resumeToken) := by
  apply debuggerCommands_distinct_commuteUnder_of_success materialize program
    requester rfl rfl different
  intro world coherent replaceSuccess resumeSuccess
  rcases replacePausedActorStack_success_witnesses materialize program requester
      world replaceMirror replacedActor replaceToken template replaceSuccess with
    ⟨replacedConfig, replacedReply, replacedEvent, replacedReason,
      materialized, replacedPaused, materializedResult⟩
  rcases resumePausedActorAtFullSpeed_success_witnesses materialize program
      requester world resumeMirror resumedActor resumeToken resumeSuccess with
    ⟨resumedConfig, resumedReply, resumedEvent, resumedReason, resumedPaused⟩
  rcases materialized with ⟨allocation, stack, control⟩
  let replacementConfig : SequentialConfig := ⟨allocation, stack, control⟩
  have materializedConfig : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control) := materializedResult
  have firstMember := coherent.allocation_member_of_runState replacedPaused
  have secondMember := coherent.allocation_member_of_runState resumedPaused
  rcases world.actorAllocations.exists_value_of_mem_domain firstMember with
    ⟨firstAllocation, firstPresent⟩
  rcases world.actorAllocations.exists_value_of_mem_domain secondMember with
    ⟨secondAllocation, secondPresent⟩
  exact replacePausedStackAndResumeCommands_distinct_commuteAt materialize
    program requester world different template replacedPaused resumedPaused
    materializedConfig firstPresent secondPresent

theorem replaceAndResumeStackAndResumeCommands_distinct_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {replaceMirror resumeMirror : MirrorId}
    {replacedActor resumedActor : ActorId}
    (different : replacedActor ≠ resumedActor) (replaceToken : PauseTokenId)
    (template : StackTemplate) (resumeToken : PauseTokenId) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      (.replaceAndResumePausedActorStack replaceMirror replacedActor
        replaceToken template)
      (.resumePausedActorAtFullSpeed resumeMirror resumedActor resumeToken) := by
  apply debuggerCommands_distinct_commuteUnder_of_success materialize program
    requester rfl rfl different
  intro world coherent replaceSuccess resumeSuccess
  rcases replaceAndResumePausedActorStack_success_witnesses materialize program
      requester world replaceMirror replacedActor replaceToken template
      replaceSuccess with
    ⟨replacedConfig, replacedReply, replacedEvent, replacedReason,
      materialized, replacedPaused, materializedResult⟩
  rcases resumePausedActorAtFullSpeed_success_witnesses materialize program
      requester world resumeMirror resumedActor resumeToken resumeSuccess with
    ⟨resumedConfig, resumedReply, resumedEvent, resumedReason, resumedPaused⟩
  rcases materialized with ⟨allocation, stack, control⟩
  let replacementConfig : SequentialConfig := ⟨allocation, stack, control⟩
  have materializedConfig : materialize program replacedConfig.allocation
      replacedConfig.stack template = some
        (replacementConfig.allocation, replacementConfig.stack,
          replacementConfig.control) := materializedResult
  have firstMember := coherent.allocation_member_of_runState replacedPaused
  have secondMember := coherent.allocation_member_of_runState resumedPaused
  rcases world.actorAllocations.exists_value_of_mem_domain firstMember with
    ⟨firstAllocation, firstPresent⟩
  rcases world.actorAllocations.exists_value_of_mem_domain secondMember with
    ⟨secondAllocation, secondPresent⟩
  exact replaceAndResumeStackAndResumeCommands_distinct_commuteAt materialize
    program requester world different template replacedPaused resumedPaused
    materializedConfig firstPresent secondPresent

theorem compatibleDebuggerCommands_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {first second : ReflectionCommand}
    (firstKind : first.kind = .debugger)
    (secondKind : second.kind = .debugger)
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      first second := by
  rcases compatibleDebuggerCommands_classified firstKind secondKind compatible with
    ⟨firstActor, secondActor, firstTarget, secondTarget, different,
      firstMints, secondMints, firstReplaces, secondReplaces⟩
  cases first <;> cases second <;>
    simp [ReflectionCommand.debuggerActor?] at firstTarget secondTarget
  all_goals simp [ReflectionCommand.mintsPauseToken,
    ReflectionCommand.replacesStack] at firstMints secondMints firstReplaces secondReplaces
  all_goals simp_all only
  all_goals first
    | exact pauseAndReplaceCurrentStackCommands_distinct_commuteUnder
        materialize program requester different _ _
    | exact pauseAndResumeActorCommands_distinct_commuteUnder materialize
        program requester different _ _
    | exact pauseAndReplaceAndResumeCommands_distinct_commuteUnder materialize
        program requester different _ _ _
    | exact (pauseAndReplaceCurrentStackCommands_distinct_commuteUnder
        materialize program requester different.symm _ _).symmetric
    | exact replaceCurrentStackAndResumeCommands_distinct_commuteUnder
        materialize program requester different _ _
    | exact (pauseAndResumeActorCommands_distinct_commuteUnder materialize
        program requester different.symm _ _).symmetric
    | exact (replaceCurrentStackAndResumeCommands_distinct_commuteUnder
        materialize program requester different.symm _ _).symmetric
    | exact (replacePausedStackAndResumeCommands_distinct_commuteUnder
        materialize program requester different.symm _ _ _).symmetric
    | exact resumePausedActorCommands_distinct_commuteUnder materialize program
        requester different _ _
    | exact (replaceAndResumeStackAndResumeCommands_distinct_commuteUnder
        materialize program requester different.symm _ _ _).symmetric
    | exact (pauseAndReplaceAndResumeCommands_distinct_commuteUnder materialize
        program requester different.symm _ _ _).symmetric
    | exact replacePausedStackAndResumeCommands_distinct_commuteUnder
        materialize program requester different _ _ _
    | exact replaceAndResumeStackAndResumeCommands_distinct_commuteUnder
        materialize program requester different _ _ _

theorem applyDebuggerCommand_eq_none_of_kind_ne_debugger
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) (world : ActorWorld) {command : ReflectionCommand}
    (notDebugger : command.kind ≠ .debugger) :
    applyDebuggerCommand materialize program requester world command = none := by
  cases command <;> simp [ReflectionCommand.kind, applyDebuggerCommand] at notDebugger ⊢

theorem compatibleCommands_debuggerPhase_commuteUnder
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommuteUnder ActorStoreDomainsCoherent
      (fun world command =>
        applyDebuggerCommand materialize program requester world command)
      first second := by
  by_cases firstKind : first.kind = .debugger
  · by_cases secondKind : second.kind = .debugger
    · exact compatibleDebuggerCommands_commuteUnder materialize program
        requester firstKind secondKind compatible
    · intro world _coherent
      exact (OptionalCommandsCommute.of_right_failure fun current =>
        applyDebuggerCommand_eq_none_of_kind_ne_debugger materialize program
          requester current secondKind) world
  · intro world _coherent
    exact (OptionalCommandsCommute.of_left_failure fun current =>
      applyDebuggerCommand_eq_none_of_kind_ne_debugger materialize program
        requester current firstKind) world

theorem debuggerTransactionIndependent_of_nonconflicting
    (materialize : StackTemplateMaterializer) (program : Program)
    (requester : ActorId) {transaction : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting transaction) :
    DebuggerTransactionIndependent materialize program requester transaction := by
  unfold DebuggerTransactionIndependent debuggerCommands
  exact (nonconflicting.filter _).imp fun compatible =>
    compatibleCommands_debuggerPhase_commuteUnder materialize program requester
      compatible

theorem Heap.writeObjectSlot_distinct_objects_commutes
    (heap : Heap) {firstObject secondObject : ObjectId}
    (different : firstObject ≠ secondObject)
    (firstSlot secondSlot : SlotId) (firstValue secondValue : ObjRef)
    {firstDefinition secondDefinition : ObjectDef}
    {oldFirstValue oldSecondValue : ObjRef}
    (firstObjectPresent : heap.objects firstObject = some firstDefinition)
    (secondObjectPresent : heap.objects secondObject = some secondDefinition)
    (firstSlotPresent : firstDefinition.slots firstSlot = some oldFirstValue)
    (secondSlotPresent : secondDefinition.slots secondSlot = some oldSecondValue) :
    (do
      let afterFirst ←
        heap.writeObjectSlot firstObject firstSlot firstValue
      afterFirst.writeObjectSlot secondObject secondSlot secondValue) =
    (do
      let afterSecond ←
        heap.writeObjectSlot secondObject secondSlot secondValue
      afterSecond.writeObjectSlot firstObject firstSlot firstValue) := by
  have firstMember :=
    heap.objects.mem_domain_of_lookup_eq_some firstObjectPresent
  have secondMember :=
    heap.objects.mem_domain_of_lookup_eq_some secondObjectPresent
  simp [Heap.writeObjectSlot, firstObjectPresent, secondObjectPresent,
    firstSlotPresent, secondSlotPresent, different, different.symm,
    Heap.installObject]
  rw [heap.objects.install_distinct_commute_of_mem different firstMember
    secondMember
    { firstDefinition with
      slots := firstDefinition.slots.install firstSlot firstValue }
    { secondDefinition with
      slots := secondDefinition.slots.install secondSlot secondValue }]

theorem Heap.writeObjectSlot_same_object_distinct_slots_commutes
    (heap : Heap) (object : ObjectId) {firstSlot secondSlot : SlotId}
    (different : firstSlot ≠ secondSlot) (firstValue secondValue : ObjRef)
    {definition : ObjectDef} {oldFirstValue oldSecondValue : ObjRef}
    (objectPresent : heap.objects object = some definition)
    (firstSlotPresent : definition.slots firstSlot = some oldFirstValue)
    (secondSlotPresent : definition.slots secondSlot = some oldSecondValue) :
    (do
      let afterFirst ← heap.writeObjectSlot object firstSlot firstValue
      afterFirst.writeObjectSlot object secondSlot secondValue) =
    (do
      let afterSecond ← heap.writeObjectSlot object secondSlot secondValue
      afterSecond.writeObjectSlot object firstSlot firstValue) := by
  have firstMember :=
    definition.slots.mem_domain_of_lookup_eq_some firstSlotPresent
  have secondMember :=
    definition.slots.mem_domain_of_lookup_eq_some secondSlotPresent
  simp [Heap.writeObjectSlot, objectPresent, firstSlotPresent,
    secondSlotPresent, different, different.symm, Heap.installObject,
    Heap.objectSlotTransform]
  rw [definition.slots.install_distinct_commute_of_mem different firstMember
    secondMember firstValue secondValue]
  rw [FiniteStore.install_same_key_overwrites,
    FiniteStore.install_same_key_overwrites]

@[simp] theorem Program.instanceLayout?_installObject
    (program : Program) (heap : Heap) (object : ObjectId)
    (definition : ObjectDef) (classId : ClassId) :
    program.instanceLayout? (heap.installObject object definition) classId =
      program.instanceLayout? heap classId := by
  exact program.instanceLayout?_of_classes_eq
    (left := heap.installObject object definition) (right := heap) rfl classId

theorem Heap.reflectWriteObjectSlot_distinct_objects_commutes
    (program : Program) (heap : Heap) {firstObject secondObject : ObjectId}
    (different : firstObject ≠ secondObject)
    (firstSlot secondSlot : SlotId) (firstValue secondValue : ObjRef)
    {firstDefinition secondDefinition : ObjectDef}
    {oldFirstValue oldSecondValue : ObjRef}
    {firstLayout secondLayout : List SlotId}
    (firstObjectPresent : heap.objects firstObject = some firstDefinition)
    (secondObjectPresent : heap.objects secondObject = some secondDefinition)
    (firstSlotPresent : firstDefinition.slots firstSlot = some oldFirstValue)
    (secondSlotPresent : secondDefinition.slots secondSlot = some oldSecondValue)
    (firstLayoutPresent :
      program.instanceLayout? heap firstDefinition.classId = some firstLayout)
    (secondLayoutPresent :
      program.instanceLayout? heap secondDefinition.classId = some secondLayout)
    (firstContained : Program.containsSlot firstLayout firstSlot = true)
    (secondContained : Program.containsSlot secondLayout secondSlot = true) :
    (do
      let afterFirst ←
        heap.reflectWriteObjectSlot program firstObject firstSlot firstValue
      afterFirst.reflectWriteObjectSlot program secondObject secondSlot
        secondValue) =
    (do
      let afterSecond ←
        heap.reflectWriteObjectSlot program secondObject secondSlot secondValue
      afterSecond.reflectWriteObjectSlot program firstObject firstSlot
        firstValue) := by
  have secondLayoutAfterFirst :
      program.instanceLayout?
          (heap.installObject firstObject
            (Heap.objectSlotTransform firstSlot firstValue firstDefinition))
          secondDefinition.classId = some secondLayout := by
    rw [Program.instanceLayout?_installObject]
    exact secondLayoutPresent
  have firstLayoutAfterSecond :
      program.instanceLayout?
          (heap.installObject secondObject
            (Heap.objectSlotTransform secondSlot secondValue secondDefinition))
          firstDefinition.classId = some firstLayout := by
    rw [Program.instanceLayout?_installObject]
    exact firstLayoutPresent
  simpa [Heap.reflectWriteObjectSlot, firstObjectPresent, secondObjectPresent,
    firstLayoutPresent, secondLayoutPresent, firstContained, secondContained,
    different, different.symm, Heap.writeObjectSlot, firstSlotPresent,
    secondSlotPresent, secondLayoutAfterFirst, firstLayoutAfterSecond] using
    heap.writeObjectSlot_distinct_objects_commutes different firstSlot secondSlot
      firstValue secondValue firstObjectPresent secondObjectPresent
      firstSlotPresent secondSlotPresent

theorem Heap.reflectWriteObjectSlot_same_object_distinct_slots_commutes
    (program : Program) (heap : Heap) (object : ObjectId)
    {firstSlot secondSlot : SlotId} (different : firstSlot ≠ secondSlot)
    (firstValue secondValue : ObjRef) {definition : ObjectDef}
    {oldFirstValue oldSecondValue : ObjRef} {layout : List SlotId}
    (objectPresent : heap.objects object = some definition)
    (firstSlotPresent : definition.slots firstSlot = some oldFirstValue)
    (secondSlotPresent : definition.slots secondSlot = some oldSecondValue)
    (layoutPresent :
      program.instanceLayout? heap definition.classId = some layout)
    (firstContained : Program.containsSlot layout firstSlot = true)
    (secondContained : Program.containsSlot layout secondSlot = true) :
    (do
      let afterFirst ←
        heap.reflectWriteObjectSlot program object firstSlot firstValue
      afterFirst.reflectWriteObjectSlot program object secondSlot secondValue) =
    (do
      let afterSecond ←
        heap.reflectWriteObjectSlot program object secondSlot secondValue
      afterSecond.reflectWriteObjectSlot program object firstSlot firstValue) := by
  have layoutAfterFirst :
      program.instanceLayout?
          (heap.installObject object
            (Heap.objectSlotTransform firstSlot firstValue definition))
          definition.classId = some layout := by
    rw [Program.instanceLayout?_installObject]
    exact layoutPresent
  have layoutAfterSecond :
      program.instanceLayout?
          (heap.installObject object
            (Heap.objectSlotTransform secondSlot secondValue definition))
          definition.classId = some layout := by
    rw [Program.instanceLayout?_installObject]
    exact layoutPresent
  simpa [Heap.reflectWriteObjectSlot, objectPresent, layoutPresent,
    firstContained, secondContained, Heap.writeObjectSlot, firstSlotPresent,
    secondSlotPresent, different, different.symm, layoutAfterFirst,
    layoutAfterSecond] using
    heap.writeObjectSlot_same_object_distinct_slots_commutes object different
      firstValue secondValue objectPresent firstSlotPresent secondSlotPresent

theorem compatibleMethodBodyCommands_have_distinct_methods
    {firstMirror secondMirror : MirrorId} {first second : MethodId}
    {firstBody secondBody : List Statement}
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodBody firstMirror first firstBody)
      (.replaceMethodBody secondMirror second secondBody)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.methodBody first) (by simp [ReflectionCommand.writes])
    (.methodBody first) (by simp [ReflectionCommand.writes])
    (.same (.methodBody first))

theorem compatibleRemoveMethodCommands_have_distinct_targets
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    (compatible : ReflectionCommandsCompatible
      (.removeMethodDefinition firstMirror firstMixin firstMethod)
      (.removeMethodDefinition secondMirror secondMixin secondMethod)) :
    firstMixin ≠ secondMixin ∧ firstMethod ≠ secondMethod := by
  constructor
  · intro equal
    subst secondMixin
    exact compatible (.methodDictionary firstMixin)
      (by simp [ReflectionCommand.writes]) (.methodDictionary firstMixin)
      (by simp [ReflectionCommand.writes]) (.same (.methodDictionary firstMixin))
  · intro equal
    subst secondMethod
    exact compatible (.methodDefinition firstMethod)
      (by simp [ReflectionCommand.writes]) (.methodDefinition firstMethod)
      (by simp [ReflectionCommand.writes]) (.same (.methodDefinition firstMethod))

theorem compatibleAddMethodCommands_have_distinct_targets
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId}
    {firstDefinition secondDefinition : MethodDef}
    {firstLocals secondLocals : List LocalDeclarationGroup}
    {firstBody secondBody : List Statement}
    (compatible : ReflectionCommandsCompatible
      (.addMethodDefinition firstMirror firstMixin firstDefinition firstLocals
        firstBody)
      (.addMethodDefinition secondMirror secondMixin secondDefinition secondLocals
        secondBody)) :
    firstMixin ≠ secondMixin ∧
      firstDefinition.identity ≠ secondDefinition.identity := by
  constructor
  · intro equal
    subst secondMixin
    exact compatible (.methodDictionary firstMixin)
      (by simp [ReflectionCommand.writes]) (.methodDictionary firstMixin)
      (by simp [ReflectionCommand.writes]) (.same (.methodDictionary firstMixin))
  · intro equal
    exact compatible (.methodDefinition firstDefinition.identity)
      (by simp [ReflectionCommand.writes])
      (.methodDefinition firstDefinition.identity)
      (by simp [ReflectionCommand.writes, equal])
      (.same (.methodDefinition firstDefinition.identity))

theorem compatibleReplaceMethodDefinitionCommands_have_distinct_targets
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    {firstDefinition secondDefinition : MethodDef}
    {firstLocals secondLocals : List LocalDeclarationGroup}
    {firstBody secondBody : List Statement}
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodDefinition firstMirror firstMixin firstMethod
        firstDefinition firstLocals firstBody)
      (.replaceMethodDefinition secondMirror secondMixin secondMethod
        secondDefinition secondLocals secondBody)) :
    firstMixin ≠ secondMixin ∧ firstMethod ≠ secondMethod := by
  constructor
  · intro equal
    subst secondMixin
    exact compatible (.methodDictionary firstMixin)
      (by simp [ReflectionCommand.writes]) (.methodDictionary firstMixin)
      (by simp [ReflectionCommand.writes]) (.same (.methodDictionary firstMixin))
  · intro equal
    subst secondMethod
    exact compatible (.methodDefinition firstMethod)
      (by simp [ReflectionCommand.writes]) (.methodDefinition firstMethod)
      (by simp [ReflectionCommand.writes]) (.same (.methodDefinition firstMethod))

theorem compatibleSuperclassCommands_have_distinct_classes
    {firstMirror secondMirror : MirrorId}
    {first second firstSuperclass secondSuperclass : ClassId}
    (compatible : ReflectionCommandsCompatible
      (.changeSuperclass firstMirror first firstSuperclass)
      (.changeSuperclass secondMirror second secondSuperclass)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.superclass first) (by simp [ReflectionCommand.writes])
    (.superclass first) (by simp [ReflectionCommand.writes])
    (.same (.superclass first))

theorem compatibleClassEnclosingCommands_have_distinct_classes
    {firstMirror secondMirror : MirrorId} {first second : ClassId}
    {firstObject secondObject : ObjRef}
    (compatible : ReflectionCommandsCompatible
      (.changeClassEnclosingObject firstMirror first firstObject)
      (.changeClassEnclosingObject secondMirror second secondObject)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.classEnclosingObject first)
    (by simp [ReflectionCommand.writes]) (.classEnclosingObject first)
    (by simp [ReflectionCommand.writes]) (.same (.classEnclosingObject first))

theorem compatibleObjectClassCommands_have_distinct_objects
    {firstMirror secondMirror : MirrorId} {first second : ObjectId}
    {firstClass secondClass : ClassId}
    (compatible : ReflectionCommandsCompatible
      (.changeObjectClass firstMirror first firstClass)
      (.changeObjectClass secondMirror second secondClass)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.objectClass first) (by simp [ReflectionCommand.writes])
    (.objectClass first) (by simp [ReflectionCommand.writes])
    (.same (.objectClass first))

theorem compatibleObjectSlotCommands_separate_locations
    {firstMirror secondMirror : MirrorId}
    {firstObject secondObject : ObjectId} {firstSlot secondSlot : SlotId}
    {firstValue secondValue : ObjRef}
    (compatible : ReflectionCommandsCompatible
      (.objectSlotWrite firstMirror firstObject firstSlot firstValue)
      (.objectSlotWrite secondMirror secondObject secondSlot secondValue)) :
    firstObject ≠ secondObject ∨ firstSlot ≠ secondSlot := by
  by_cases objectsDifferent : firstObject ≠ secondObject
  · exact .inl objectsDifferent
  · right
    intro slotsEqual
    have objectsEqual : firstObject = secondObject := by
      exact Decidable.not_not.mp objectsDifferent
    subst secondObject
    subst secondSlot
    exact compatible (.objectSlot firstObject firstSlot)
      (by simp [ReflectionCommand.writes]) (.objectSlot firstObject firstSlot)
      (by simp [ReflectionCommand.writes])
      (.same (.objectSlot firstObject firstSlot))

theorem compatibleCurrentClassCommands_have_distinct_activations
    {firstMirror secondMirror : MirrorId} {first second : ActivationId}
    {firstClass secondClass : Option ClassId}
    (compatible : ReflectionCommandsCompatible
      (.changeActivationCurrentClass firstMirror first firstClass)
      (.changeActivationCurrentClass secondMirror second secondClass)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.activationField first .currentClass)
    (by simp [ReflectionCommand.writes])
    (.activationField first .currentClass)
    (by simp [ReflectionCommand.writes])
    (.same (.activationField first .currentClass))

theorem compatibleContinuationCommands_have_distinct_activations
    {firstMirror secondMirror : MirrorId} {first second : ActivationId}
    {firstContinuation secondContinuation : Option ActivationId}
    (compatible : ReflectionCommandsCompatible
      (.changeActivationContinuation firstMirror first firstContinuation)
      (.changeActivationContinuation secondMirror second secondContinuation)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.activationField first .continuation)
    (by simp [ReflectionCommand.writes])
    (.activationField first .continuation)
    (by simp [ReflectionCommand.writes])
    (.same (.activationField first .continuation))

theorem changeSuperclassCommands_commuteAt
    (heap : Heap) {firstMirror secondMirror : MirrorId}
    {first second firstSuperclass secondSuperclass : ClassId}
    {firstDefinition secondDefinition : ClassDef}
    (compatible : ReflectionCommandsCompatible
      (.changeSuperclass firstMirror first firstSuperclass)
      (.changeSuperclass secondMirror second secondSuperclass))
    (firstPresent : heap.classes first = some firstDefinition)
    (secondPresent : heap.classes second = some secondDefinition) :
    ClassGraphCommandsCommuteAt heap
      (.changeSuperclass firstMirror first firstSuperclass)
      (.changeSuperclass secondMirror second secondSuperclass) := by
  simpa [ClassGraphCommandsCommuteAt, applyClassGraphCommand,
    Heap.reflectChangeSuperclass] using
    heap.transformExistingClass_distinct_commutes
      (compatibleSuperclassCommands_have_distinct_classes compatible)
      (Heap.reflectedSuperclassTransform firstSuperclass)
      (Heap.reflectedSuperclassTransform secondSuperclass)
      firstPresent secondPresent

theorem changeClassEnclosingCommands_commuteAt
    (heap : Heap) {firstMirror secondMirror : MirrorId}
    {first second : ClassId} {firstObject secondObject : ObjRef}
    {firstDefinition secondDefinition : ClassDef}
    (compatible : ReflectionCommandsCompatible
      (.changeClassEnclosingObject firstMirror first firstObject)
      (.changeClassEnclosingObject secondMirror second secondObject))
    (firstPresent : heap.classes first = some firstDefinition)
    (secondPresent : heap.classes second = some secondDefinition) :
    ClassGraphCommandsCommuteAt heap
      (.changeClassEnclosingObject firstMirror first firstObject)
      (.changeClassEnclosingObject secondMirror second secondObject) := by
  simpa [ClassGraphCommandsCommuteAt, applyClassGraphCommand,
    Heap.reflectChangeClassEnclosingObject] using
    heap.transformExistingClass_distinct_commutes
      (compatibleClassEnclosingCommands_have_distinct_classes compatible)
      (Heap.reflectedEnclosingObjectTransform firstObject)
      (Heap.reflectedEnclosingObjectTransform secondObject)
      firstPresent secondPresent

theorem changeSuperclassAndEnclosingCommands_commuteAt
    (heap : Heap) {superclassMirror enclosingMirror : MirrorId}
    (superclassClass enclosingClass superclass : ClassId)
    (enclosingObject : ObjRef)
    {superclassDefinition enclosingDefinition : ClassDef}
    (superclassPresent :
      heap.classes superclassClass = some superclassDefinition)
    (enclosingPresent : heap.classes enclosingClass = some enclosingDefinition) :
    ClassGraphCommandsCommuteAt heap
      (.changeSuperclass superclassMirror superclassClass superclass)
      (.changeClassEnclosingObject enclosingMirror enclosingClass
        enclosingObject) := by
  simpa [ClassGraphCommandsCommuteAt, applyClassGraphCommand] using
    heap.superclassAndEnclosingObjectChanges_commute superclassClass
      enclosingClass superclass enclosingObject superclassPresent
      enclosingPresent

theorem compatibleClassGraphCommands_commute
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute applyClassGraphCommand first second := by
  intro heap
  cases first <;> cases second <;>
    simp only [applyClassGraphCommand]
  all_goals try simp
  case changeSuperclass.changeSuperclass firstMirror first firstSuperclass
      secondMirror second secondSuperclass =>
    simpa [Heap.reflectChangeSuperclass] using
      heap.transformExistingClass_distinct_commutes_total
        (compatibleSuperclassCommands_have_distinct_classes compatible)
        (Heap.reflectedSuperclassTransform firstSuperclass)
        (Heap.reflectedSuperclassTransform secondSuperclass)
  case changeSuperclass.changeClassEnclosingObject superclassMirror
      superclassClass superclass enclosingMirror enclosingClass
      enclosingObject =>
    exact heap.superclassAndEnclosingObjectChanges_commute_total
      superclassClass enclosingClass superclass enclosingObject
  case changeClassEnclosingObject.changeSuperclass enclosingMirror
      enclosingClass enclosingObject superclassMirror superclassClass
      superclass =>
    exact (heap.superclassAndEnclosingObjectChanges_commute_total
      superclassClass enclosingClass superclass enclosingObject).symm
  case changeClassEnclosingObject.changeClassEnclosingObject firstMirror first
      firstObject secondMirror second secondObject =>
    simpa [Heap.reflectChangeClassEnclosingObject] using
      heap.transformExistingClass_distinct_commutes_total
        (compatibleClassEnclosingCommands_have_distinct_classes compatible)
        (Heap.reflectedEnclosingObjectTransform firstObject)
        (Heap.reflectedEnclosingObjectTransform secondObject)

theorem applyClassGraphCommand_preserves_containsClassId
    (command : ReflectionCommand) (query : ClassId)
    {heap updated : Heap}
    (result : applyClassGraphCommand heap command = some updated) :
    updated.containsClassId query = heap.containsClassId query := by
  cases command <;> simp only [applyClassGraphCommand] at result
  all_goals try contradiction
  case changeSuperclass mirror classId superclass =>
    exact heap.transformExistingClass_preserves_containsClassId classId query
      (Heap.reflectedSuperclassTransform superclass) result
  case changeClassEnclosingObject mirror classId enclosingObject =>
    exact heap.transformExistingClass_preserves_containsClassId classId query
      (Heap.reflectedEnclosingObjectTransform enclosingObject) result

theorem changeObjectClassCommands_commuteAt
    (heap : Heap) {firstMirror secondMirror : MirrorId}
    {first second : ObjectId} {firstClass secondClass : ClassId}
    {firstDefinition secondDefinition : ObjectDef}
    (compatible : ReflectionCommandsCompatible
      (.changeObjectClass firstMirror first firstClass)
      (.changeObjectClass secondMirror second secondClass))
    (firstPresent : heap.objects first = some firstDefinition)
    (secondPresent : heap.objects second = some secondDefinition) :
    ObjectClassCommandsCommuteAt heap
      (.changeObjectClass firstMirror first firstClass)
      (.changeObjectClass secondMirror second secondClass) := by
  simpa [ObjectClassCommandsCommuteAt, applyObjectClassCommand,
    Heap.reflectChangeObjectClass] using
    heap.transformExistingObject_distinct_commutes
      (compatibleObjectClassCommands_have_distinct_objects compatible)
      (Heap.reflectedObjectClassTransform firstClass)
      (Heap.reflectedObjectClassTransform secondClass)
      firstPresent secondPresent

theorem compatibleObjectClassCommands_commute
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute applyObjectClassCommand first second := by
  intro heap
  cases first <;> cases second <;>
    simp only [applyObjectClassCommand]
  all_goals try simp
  case changeObjectClass.changeObjectClass firstMirror first firstClass
      secondMirror second secondClass =>
    simpa [Heap.reflectChangeObjectClass] using
      heap.transformExistingObject_distinct_commutes_total
        (compatibleObjectClassCommands_have_distinct_objects compatible)
        (Heap.reflectedObjectClassTransform firstClass)
        (Heap.reflectedObjectClassTransform secondClass)

theorem applyObjectClassCommand_preserves_containsObjectId
    (command : ReflectionCommand) (query : ObjectId)
    {heap updated : Heap}
    (result : applyObjectClassCommand heap command = some updated) :
    updated.containsObjectId query = heap.containsObjectId query := by
  cases command <;> simp only [applyObjectClassCommand] at result
  all_goals try contradiction
  case changeObjectClass mirror object classId =>
    exact heap.transformExistingObject_preserves_containsObjectId object query
      (Heap.reflectedObjectClassTransform classId) result

theorem objectSlotCommands_distinct_objects_commuteAt
    (program : Program) (heap : Heap)
    {firstMirror secondMirror : MirrorId}
    {firstObject secondObject : ObjectId} (different : firstObject ≠ secondObject)
    (firstSlot secondSlot : SlotId) (firstValue secondValue : ObjRef)
    {firstDefinition secondDefinition : ObjectDef}
    {oldFirstValue oldSecondValue : ObjRef}
    {firstLayout secondLayout : List SlotId}
    (firstObjectPresent : heap.objects firstObject = some firstDefinition)
    (secondObjectPresent : heap.objects secondObject = some secondDefinition)
    (firstSlotPresent : firstDefinition.slots firstSlot = some oldFirstValue)
    (secondSlotPresent : secondDefinition.slots secondSlot = some oldSecondValue)
    (firstLayoutPresent :
      program.instanceLayout? heap firstDefinition.classId = some firstLayout)
    (secondLayoutPresent :
      program.instanceLayout? heap secondDefinition.classId = some secondLayout)
    (firstContained : Program.containsSlot firstLayout firstSlot = true)
    (secondContained : Program.containsSlot secondLayout secondSlot = true) :
    ObjectSlotCommandsCommuteAt program heap
      (.objectSlotWrite firstMirror firstObject firstSlot firstValue)
      (.objectSlotWrite secondMirror secondObject secondSlot secondValue) := by
  simpa [ObjectSlotCommandsCommuteAt, applyReflectiveObjectSlotCommand] using
    heap.reflectWriteObjectSlot_distinct_objects_commutes program different
      firstSlot secondSlot firstValue secondValue firstObjectPresent
      secondObjectPresent firstSlotPresent secondSlotPresent firstLayoutPresent
      secondLayoutPresent firstContained secondContained

theorem Heap.reflectWriteObjectSlot_distinct_objects_commutes_total
    (program : Program) (heap : Heap)
    {firstObject secondObject : ObjectId} (different : firstObject ≠ secondObject)
    (firstSlot secondSlot : SlotId) (firstValue secondValue : ObjRef) :
    (do
      let afterFirst ← heap.reflectWriteObjectSlot program firstObject
        firstSlot firstValue
      afterFirst.reflectWriteObjectSlot program secondObject secondSlot
        secondValue) =
    (do
      let afterSecond ← heap.reflectWriteObjectSlot program secondObject
        secondSlot secondValue
      afterSecond.reflectWriteObjectSlot program firstObject firstSlot
        firstValue) := by
  cases firstObjectResult : heap.objects firstObject with
  | none =>
      cases secondObjectResult : heap.objects secondObject with
      | none => simp [Heap.reflectWriteObjectSlot, firstObjectResult,
          secondObjectResult]
      | some secondDefinition =>
          cases secondLayoutResult :
              program.instanceLayout? heap secondDefinition.classId with
          | none => simp [Heap.reflectWriteObjectSlot, firstObjectResult,
              secondObjectResult, secondLayoutResult]
          | some secondLayout =>
              cases secondContained :
                  Program.containsSlot secondLayout secondSlot with
              | false => simp [Heap.reflectWriteObjectSlot, firstObjectResult,
                  secondObjectResult, secondLayoutResult, secondContained]
              | true =>
                  cases secondSlotResult :
                      secondDefinition.slots secondSlot <;>
                    simp [Heap.reflectWriteObjectSlot, Heap.writeObjectSlot,
                      firstObjectResult, secondObjectResult,
                      secondLayoutResult, secondContained, secondSlotResult,
                      different]
  | some firstDefinition =>
      cases secondObjectResult : heap.objects secondObject with
      | none =>
          cases firstLayoutResult :
              program.instanceLayout? heap firstDefinition.classId with
          | none => simp [Heap.reflectWriteObjectSlot, firstObjectResult,
              secondObjectResult, firstLayoutResult]
          | some firstLayout =>
              cases firstContained :
                  Program.containsSlot firstLayout firstSlot with
              | false => simp [Heap.reflectWriteObjectSlot, firstObjectResult,
                  secondObjectResult, firstLayoutResult, firstContained]
              | true =>
                  cases firstSlotResult : firstDefinition.slots firstSlot <;>
                    simp [Heap.reflectWriteObjectSlot, Heap.writeObjectSlot,
                      firstObjectResult, secondObjectResult, firstLayoutResult,
                      firstContained, firstSlotResult, different.symm]
      | some secondDefinition =>
          cases firstLayoutResult :
              program.instanceLayout? heap firstDefinition.classId with
          | none =>
              cases secondLayoutResult :
                  program.instanceLayout? heap secondDefinition.classId with
              | none => simp [Heap.reflectWriteObjectSlot, firstObjectResult,
                  secondObjectResult, firstLayoutResult, secondLayoutResult]
              | some secondLayout =>
                  cases secondContained :
                      Program.containsSlot secondLayout secondSlot with
                  | false => simp [Heap.reflectWriteObjectSlot,
                      firstObjectResult, secondObjectResult, firstLayoutResult,
                      secondLayoutResult, secondContained]
                  | true =>
                      cases secondSlotResult :
                          secondDefinition.slots secondSlot <;>
                        simp [Heap.reflectWriteObjectSlot, Heap.writeObjectSlot,
                          firstObjectResult, secondObjectResult,
                          firstLayoutResult, secondLayoutResult,
                          secondContained, secondSlotResult, different]
          | some firstLayout =>
              cases secondLayoutResult :
                  program.instanceLayout? heap secondDefinition.classId with
              | none =>
                  cases firstContained :
                      Program.containsSlot firstLayout firstSlot with
                  | false => simp [Heap.reflectWriteObjectSlot,
                      firstObjectResult, secondObjectResult, firstLayoutResult,
                      secondLayoutResult, firstContained]
                  | true =>
                      cases firstSlotResult : firstDefinition.slots firstSlot <;>
                        simp [Heap.reflectWriteObjectSlot, Heap.writeObjectSlot,
                          firstObjectResult, secondObjectResult,
                          firstLayoutResult, secondLayoutResult,
                          firstContained, firstSlotResult, different.symm]
              | some secondLayout =>
                  cases firstContained :
                      Program.containsSlot firstLayout firstSlot <;>
                    cases secondContained :
                      Program.containsSlot secondLayout secondSlot <;>
                    cases firstSlotResult :
                      firstDefinition.slots firstSlot <;>
                    cases secondSlotResult :
                      secondDefinition.slots secondSlot <;>
                    try simp [Heap.reflectWriteObjectSlot,
                      Heap.writeObjectSlot, firstObjectResult,
                      secondObjectResult, firstLayoutResult,
                      secondLayoutResult, firstContained, secondContained,
                      firstSlotResult, secondSlotResult, different,
                      different.symm]
                  unfold Heap.installObject
                  congr 1
                  exact heap.objects.install_distinct_commute_of_mem different
                    (heap.objects.mem_domain_of_lookup_eq_some firstObjectResult)
                    (heap.objects.mem_domain_of_lookup_eq_some secondObjectResult)
                    _ _

theorem objectSlotCommands_same_object_commuteAt
    (program : Program) (heap : Heap)
    {firstMirror secondMirror : MirrorId} (object : ObjectId)
    {firstSlot secondSlot : SlotId} (firstValue secondValue : ObjRef)
    {definition : ObjectDef} {oldFirstValue oldSecondValue : ObjRef}
    {layout : List SlotId}
    (compatible : ReflectionCommandsCompatible
      (.objectSlotWrite firstMirror object firstSlot firstValue)
      (.objectSlotWrite secondMirror object secondSlot secondValue))
    (objectPresent : heap.objects object = some definition)
    (firstSlotPresent : definition.slots firstSlot = some oldFirstValue)
    (secondSlotPresent : definition.slots secondSlot = some oldSecondValue)
    (layoutPresent :
      program.instanceLayout? heap definition.classId = some layout)
    (firstContained : Program.containsSlot layout firstSlot = true)
    (secondContained : Program.containsSlot layout secondSlot = true) :
    ObjectSlotCommandsCommuteAt program heap
      (.objectSlotWrite firstMirror object firstSlot firstValue)
      (.objectSlotWrite secondMirror object secondSlot secondValue) := by
  have slotsDifferent : firstSlot ≠ secondSlot := by
    rcases compatibleObjectSlotCommands_separate_locations compatible with
      objectsDifferent | slotsDifferent
    · exact False.elim (objectsDifferent rfl)
    · exact slotsDifferent
  simpa [ObjectSlotCommandsCommuteAt, applyReflectiveObjectSlotCommand] using
    heap.reflectWriteObjectSlot_same_object_distinct_slots_commutes program
      object slotsDifferent firstValue secondValue objectPresent
      firstSlotPresent secondSlotPresent layoutPresent firstContained
      secondContained

theorem Heap.reflectWriteObjectSlot_same_object_distinct_slots_commutes_total
    (program : Program) (heap : Heap) (object : ObjectId)
    {firstSlot secondSlot : SlotId} (different : firstSlot ≠ secondSlot)
    (firstValue secondValue : ObjRef) :
    (do
      let afterFirst ← heap.reflectWriteObjectSlot program object firstSlot
        firstValue
      afterFirst.reflectWriteObjectSlot program object secondSlot secondValue) =
    (do
      let afterSecond ← heap.reflectWriteObjectSlot program object secondSlot
        secondValue
      afterSecond.reflectWriteObjectSlot program object firstSlot firstValue) := by
  cases objectResult : heap.objects object with
  | none => simp [Heap.reflectWriteObjectSlot, objectResult]
  | some definition =>
      cases layoutResult :
          program.instanceLayout? heap definition.classId with
      | none => simp [Heap.reflectWriteObjectSlot, objectResult, layoutResult]
      | some layout =>
          cases firstContained : Program.containsSlot layout firstSlot <;>
            cases secondContained : Program.containsSlot layout secondSlot <;>
            cases firstSlotResult : definition.slots firstSlot <;>
            cases secondSlotResult : definition.slots secondSlot <;>
            try simp [Heap.reflectWriteObjectSlot, Heap.writeObjectSlot,
              objectResult, layoutResult, firstContained, secondContained,
              firstSlotResult, secondSlotResult, different, different.symm,
              Heap.objectSlotTransform]
          have firstMember :=
            definition.slots.mem_domain_of_lookup_eq_some firstSlotResult
          have secondMember :=
            definition.slots.mem_domain_of_lookup_eq_some secondSlotResult
          simp [Heap.installObject]
          rw [definition.slots.install_distinct_commute_of_mem different
            firstMember secondMember firstValue secondValue]
          rw [FiniteStore.install_same_key_overwrites,
            FiniteStore.install_same_key_overwrites]

theorem compatibleObjectSlotCommands_commute
    (program : Program) {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute (applyReflectiveObjectSlotCommand program)
      first second := by
  intro heap
  cases first <;> cases second <;>
    simp only [applyReflectiveObjectSlotCommand]
  all_goals try simp
  case objectSlotWrite.objectSlotWrite firstMirror firstObject firstSlot
      firstValue secondMirror secondObject secondSlot secondValue =>
    by_cases objectsDifferent : firstObject ≠ secondObject
    · exact heap.reflectWriteObjectSlot_distinct_objects_commutes_total
        program objectsDifferent firstSlot secondSlot firstValue secondValue
    · have objectsEqual : firstObject = secondObject :=
        Decidable.not_not.mp objectsDifferent
      subst secondObject
      have slotsDifferent : firstSlot ≠ secondSlot := by
        rcases compatibleObjectSlotCommands_separate_locations compatible with
          impossible | separated
        · exact False.elim (impossible rfl)
        · exact separated
      exact heap.reflectWriteObjectSlot_same_object_distinct_slots_commutes_total
        program firstObject slotsDifferent firstValue secondValue

theorem Heap.writeObjectSlot_preserves_containsObjectId
    {heap updated : Heap} (object : ObjectId) (slot : SlotId)
    (value : ObjRef) (query : ObjectId)
    (result : heap.writeObjectSlot object slot value = some updated) :
    updated.containsObjectId query = heap.containsObjectId query := by
  unfold Heap.writeObjectSlot at result
  cases objectResult : heap.objects object with
  | none => simp [objectResult] at result
  | some definition =>
      cases slotResult : definition.slots slot with
      | none => simp [objectResult, slotResult] at result
      | some oldValue =>
          simp [objectResult, slotResult] at result
          subst updated
          by_cases atObject : query = object
          · subst query
            simp [Heap.containsObjectId, objectResult]
          · simp [Heap.containsObjectId, Heap.installObject, atObject]

theorem Heap.reflectWriteObjectSlot_preserves_containsObjectId
    (program : Program) {heap updated : Heap} (object : ObjectId)
    (slot : SlotId) (value : ObjRef) (query : ObjectId)
    (result : heap.reflectWriteObjectSlot program object slot value =
      some updated) :
    updated.containsObjectId query = heap.containsObjectId query := by
  unfold Heap.reflectWriteObjectSlot at result
  cases objectResult : heap.objects object with
  | none => simp [objectResult] at result
  | some definition =>
      cases layoutResult : program.instanceLayout? heap definition.classId with
      | none => simp [objectResult, layoutResult] at result
      | some layout =>
          cases contained : Program.containsSlot layout slot with
          | false => simp [objectResult, layoutResult, contained] at result
          | true =>
              simp [objectResult, layoutResult, contained] at result
              exact heap.writeObjectSlot_preserves_containsObjectId object slot
                value query result

theorem applyReflectiveObjectSlotCommand_preserves_containsObjectId
    (program : Program) (command : ReflectionCommand) (query : ObjectId)
    {heap updated : Heap}
    (result : applyReflectiveObjectSlotCommand program heap command =
      some updated) :
    updated.containsObjectId query = heap.containsObjectId query := by
  cases command <;> simp only [applyReflectiveObjectSlotCommand] at result
  all_goals try contradiction
  case objectSlotWrite mirror object slot value =>
    exact heap.reflectWriteObjectSlot_preserves_containsObjectId program object
      slot value query result

theorem changeActivationCurrentClassCommands_commuteAt
    (heap : Heap) {firstMirror secondMirror : MirrorId}
    {first second : ActivationId} {firstClass secondClass : Option ClassId}
    {firstDefinition secondDefinition : ActivationDef}
    (compatible : ReflectionCommandsCompatible
      (.changeActivationCurrentClass firstMirror first firstClass)
      (.changeActivationCurrentClass secondMirror second secondClass))
    (firstPresent : heap.activations first = some firstDefinition)
    (secondPresent : heap.activations second = some secondDefinition) :
    ActivationCommandsCommuteAt heap
      (.changeActivationCurrentClass firstMirror first firstClass)
      (.changeActivationCurrentClass secondMirror second secondClass) := by
  simpa [ActivationCommandsCommuteAt, applyActivationCommand,
    Heap.reflectChangeActivationCurrentClass, Heap.applyActivationRecordEdit,
    Heap.currentClassRecordEdit, Heap.transformExistingActivation] using
    heap.transformExistingActivation_distinct_commutes
      (compatibleCurrentClassCommands_have_distinct_activations compatible)
      (Heap.reflectedCurrentClassTransform firstClass)
      (Heap.reflectedCurrentClassTransform secondClass)
      firstPresent secondPresent

theorem changeActivationContinuationCommands_commuteAt
    (heap : Heap) {firstMirror secondMirror : MirrorId}
    {first second : ActivationId}
    {firstContinuation secondContinuation : Option ActivationId}
    {firstDefinition secondDefinition : ActivationDef}
    (compatible : ReflectionCommandsCompatible
      (.changeActivationContinuation firstMirror first firstContinuation)
      (.changeActivationContinuation secondMirror second secondContinuation))
    (firstPresent : heap.activations first = some firstDefinition)
    (secondPresent : heap.activations second = some secondDefinition) :
    ActivationCommandsCommuteAt heap
      (.changeActivationContinuation firstMirror first firstContinuation)
      (.changeActivationContinuation secondMirror second secondContinuation) := by
  simpa [ActivationCommandsCommuteAt, applyActivationCommand,
    Heap.reflectChangeActivationContinuation, Heap.applyActivationRecordEdit,
    Heap.continuationRecordEdit, Heap.transformExistingActivation] using
    heap.transformExistingActivation_distinct_commutes
      (compatibleContinuationCommands_have_distinct_activations compatible)
      (Heap.reflectedContinuationTransform firstContinuation)
      (Heap.reflectedContinuationTransform secondContinuation)
      firstPresent secondPresent

theorem changeActivationCurrentClassAndContinuationCommands_commuteAt
    (heap : Heap) {currentClassMirror continuationMirror : MirrorId}
    (currentClassActivation continuationActivation : ActivationId)
    (classId : Option ClassId) (continuation : Option ActivationId)
    {currentClassDefinition continuationDefinition : ActivationDef}
    (currentClassPresent :
      heap.activations currentClassActivation = some currentClassDefinition)
    (continuationPresent :
      heap.activations continuationActivation = some continuationDefinition) :
    ActivationCommandsCommuteAt heap
      (.changeActivationCurrentClass currentClassMirror currentClassActivation
        classId)
      (.changeActivationContinuation continuationMirror continuationActivation
        continuation) := by
  simpa [ActivationCommandsCommuteAt, applyActivationCommand] using
    heap.currentClassAndContinuationChanges_commute currentClassActivation
      continuationActivation classId continuation currentClassPresent
      continuationPresent

theorem compatibleActivationCommands_commute
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute applyActivationCommand first second := by
  cases first <;> cases second
  case activationParameterWrite.activationParameterWrite firstMirror
      firstActivation firstParameter firstValue secondMirror secondActivation
      secondParameter secondValue =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro equal
    subst secondActivation
    have parametersDifferent : firstParameter ≠ secondParameter := by
      intro parametersEqual
      subst secondParameter
      exact compatibleCommands_cannot_share_location compatible
        (location := .activationField firstActivation
          (.parameter firstParameter)) (by simp [ReflectionCommand.writes])
        (by simp [ReflectionCommand.writes])
    exact parameterRecordEdits_commuteStatically parametersDifferent
      firstValue secondValue
  case activationParameterWrite.activationLocalWrite firstMirror
      firstActivation parameter parameterValue secondMirror secondActivation
      slot localValue =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact parameterAndLocalRecordEdits_commuteStatically parameter
      parameterValue slot localValue
  case activationParameterWrite.changeActivationCurrentClass firstMirror
      firstActivation parameter value secondMirror secondActivation classId =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact parameterAndCurrentClassRecordEdits_commuteStatically parameter value
      classId
  case activationParameterWrite.changeActivationContinuation firstMirror
      firstActivation parameter value secondMirror secondActivation
      continuation =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact parameterAndContinuationRecordEdits_commuteStatically parameter value
      continuation
  case activationLocalWrite.activationParameterWrite firstMirror
      firstActivation slot localValue secondMirror secondActivation parameter
      parameterValue =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact (parameterAndLocalRecordEdits_commuteStatically parameter
      parameterValue slot localValue).symmetric
  case activationLocalWrite.activationLocalWrite firstMirror firstActivation
      firstSlot firstValue secondMirror secondActivation secondSlot secondValue =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro equal
    subst secondActivation
    have slotsDifferent : firstSlot ≠ secondSlot := by
      intro slotsEqual
      subst secondSlot
      exact compatibleCommands_cannot_share_location compatible
        (location := .activationField firstActivation (.local firstSlot))
        (by simp [ReflectionCommand.writes])
        (by simp [ReflectionCommand.writes])
    exact localRecordEdits_commuteStatically slotsDifferent firstValue
      secondValue
  case activationLocalWrite.changeActivationCurrentClass firstMirror
      firstActivation slot value secondMirror secondActivation classId =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact localAndCurrentClassRecordEdits_commuteStatically slot value classId
  case activationLocalWrite.changeActivationContinuation firstMirror
      firstActivation slot value secondMirror secondActivation continuation =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact localAndContinuationRecordEdits_commuteStatically slot value
      continuation
  case changeActivationCurrentClass.activationParameterWrite firstMirror
      firstActivation classId secondMirror secondActivation parameter value =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact (parameterAndCurrentClassRecordEdits_commuteStatically parameter value
      classId).symmetric
  case changeActivationCurrentClass.activationLocalWrite firstMirror
      firstActivation classId secondMirror secondActivation slot value =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact (localAndCurrentClassRecordEdits_commuteStatically slot value
      classId).symmetric
  case changeActivationCurrentClass.changeActivationCurrentClass firstMirror
      firstActivation firstClass secondMirror secondActivation secondClass =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro equal
    subst secondActivation
    exact False.elim (compatibleCommands_cannot_share_location compatible
      (location := .activationField firstActivation .currentClass)
      (by simp [ReflectionCommand.writes])
      (by simp [ReflectionCommand.writes]))
  case changeActivationCurrentClass.changeActivationContinuation firstMirror
      firstActivation classId secondMirror secondActivation continuation =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact currentClassAndContinuationRecordEdits_commuteStatically classId
      continuation
  case changeActivationContinuation.activationParameterWrite firstMirror
      firstActivation continuation secondMirror secondActivation parameter
      value =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact (parameterAndContinuationRecordEdits_commuteStatically parameter
      value continuation).symmetric
  case changeActivationContinuation.activationLocalWrite firstMirror
      firstActivation continuation secondMirror secondActivation slot value =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact (localAndContinuationRecordEdits_commuteStatically slot value
      continuation).symmetric
  case changeActivationContinuation.changeActivationCurrentClass firstMirror
      firstActivation continuation secondMirror secondActivation classId =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro _
    exact (currentClassAndContinuationRecordEdits_commuteStatically classId
      continuation).symmetric
  case changeActivationContinuation.changeActivationContinuation firstMirror
      firstActivation firstContinuation secondMirror secondActivation
      secondContinuation =>
    apply ordinaryActivationCommands_commute_of_sameActivationStatic rfl rfl
    intro equal
    subst secondActivation
    exact False.elim (compatibleCommands_cannot_share_location compatible
      (location := .activationField firstActivation .continuation)
      (by simp [ReflectionCommand.writes])
      (by simp [ReflectionCommand.writes]))
  all_goals
    first
    | exact OptionalCommandsCommute.of_left_failure (by intro; rfl)
    | exact OptionalCommandsCommute.of_right_failure (by intro; rfl)
    | exfalso; exact activationRetirementAndActivationCommand_incompatible
        (by rfl) compatible
    | exfalso; exact activationRetirementAndActivationCommand_incompatible
        (by rfl) compatible.symmetric

theorem Heap.reflectMakeActivationUncontinuable_preserves_containsActivationId
    {heap updated : Heap} (activation query : ActivationId)
    (result : heap.reflectMakeActivationUncontinuable activation =
      some updated) :
    updated.containsActivationId query = heap.containsActivationId query := by
  classical
  unfold Heap.reflectMakeActivationUncontinuable at result
  cases present : heap.activations activation with
  | none => simp [present] at result
  | some definition =>
      simp [present] at result
      subst updated
      cases queryResult : heap.activations query <;>
        simp [Heap.containsActivationId, Heap.markUncontinuable,
          FiniteStore.mapValues, queryResult]

theorem applyActivationCommand_preserves_containsActivationId
    (command : ReflectionCommand) (query : ActivationId)
    {heap updated : Heap}
    (result : applyActivationCommand heap command = some updated) :
    updated.containsActivationId query = heap.containsActivationId query := by
  cases command <;> simp only [applyActivationCommand] at result
  all_goals try contradiction
  case activationParameterWrite mirror activation parameter value =>
    exact heap.applyActivationRecordEdit_preserves_containsActivationId
      activation query (Heap.parameterRecordEdit parameter value) result
  case activationLocalWrite mirror activation slot value =>
    exact heap.applyActivationRecordEdit_preserves_containsActivationId
      activation query (Heap.localRecordEdit slot value) result
  case changeActivationCurrentClass mirror activation classId =>
    exact heap.applyActivationRecordEdit_preserves_containsActivationId
      activation query (Heap.currentClassRecordEdit classId) result
  case changeActivationContinuation mirror activation continuation =>
    exact heap.applyActivationRecordEdit_preserves_containsActivationId
      activation query (Heap.continuationRecordEdit continuation) result
  case makeActivationUncontinuable mirror activation =>
    exact heap.reflectMakeActivationUncontinuable_preserves_containsActivationId
      activation query result

theorem applyCohortClassGraphCommand_preserves_locateClassId
    (command : ReflectionCommand) (query : ClassId) {world updated : ActorWorld}
    (result : applyCohortClassGraphCommand world command = some updated) :
    updated.locateClassId query = world.locateClassId query := by
  cases command <;> simp only [applyCohortClassGraphCommand,
    classGraphCommandClass?] at result
  all_goals try contradiction
  case changeSuperclass mirror classId superclass =>
    cases locationResult : world.locateClassId classId with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateClassId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsClassId query) location
            (fun heap => applyClassGraphCommand heap
              (.changeSuperclass mirror classId superclass))
            (fun before after updateResult =>
              applyClassGraphCommand_preserves_containsClassId
                (.changeSuperclass mirror classId superclass) query
                updateResult)
            result
  case changeClassEnclosingObject mirror classId enclosingObject =>
    cases locationResult : world.locateClassId classId with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateClassId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsClassId query) location
            (fun heap => applyClassGraphCommand heap
              (.changeClassEnclosingObject mirror classId enclosingObject))
            (fun before after updateResult =>
              applyClassGraphCommand_preserves_containsClassId
                (.changeClassEnclosingObject mirror classId enclosingObject)
                query updateResult)
            result

theorem applyCohortObjectClassCommand_preserves_locateObjectId
    (command : ReflectionCommand) (query : ObjectId)
    {world updated : ActorWorld}
    (result : applyCohortObjectClassCommand world command = some updated) :
    updated.locateObjectId query = world.locateObjectId query := by
  cases command <;> simp only [applyCohortObjectClassCommand,
    objectClassCommandObject?] at result
  all_goals try contradiction
  case changeObjectClass mirror object classId =>
    cases locationResult : world.locateObjectId object with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateObjectId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsObjectId query) location
            (fun heap => applyObjectClassCommand heap
              (.changeObjectClass mirror object classId))
            (fun before after updateResult =>
              applyObjectClassCommand_preserves_containsObjectId
                (.changeObjectClass mirror object classId) query updateResult)
            result

theorem applyCohortObjectSlotCommand_preserves_locateObjectId
    (program : Program) (command : ReflectionCommand) (query : ObjectId)
    {world updated : ActorWorld}
    (result : applyCohortObjectSlotCommand program world command =
      some updated) :
    updated.locateObjectId query = world.locateObjectId query := by
  cases command <;> simp only [applyCohortObjectSlotCommand,
    objectSlotCommandObject?] at result
  all_goals try contradiction
  case objectSlotWrite mirror object slot value =>
    cases locationResult : world.locateObjectId object with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateObjectId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsObjectId query) location
            (fun heap => applyReflectiveObjectSlotCommand program heap
              (.objectSlotWrite mirror object slot value))
            (fun before after updateResult =>
              applyReflectiveObjectSlotCommand_preserves_containsObjectId
                program (.objectSlotWrite mirror object slot value) query
                updateResult)
            result

theorem applyCohortActivationCommand_preserves_locateActivationId
    (command : ReflectionCommand) (query : ActivationId)
    {world updated : ActorWorld}
    (result : applyCohortActivationCommand world command = some updated) :
    updated.locateActivationId query = world.locateActivationId query := by
  cases command <;> simp only [applyCohortActivationCommand,
    activationCommandActivation?] at result
  all_goals try contradiction
  case activationParameterWrite mirror activation parameter value =>
    cases locationResult : world.locateActivationId activation with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateActivationId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsActivationId query) location
            (fun heap => applyActivationCommand heap
              (.activationParameterWrite mirror activation parameter value))
            (fun before after updateResult =>
              applyActivationCommand_preserves_containsActivationId
                (.activationParameterWrite mirror activation parameter value)
                query updateResult)
            result
  case activationLocalWrite mirror activation slot value =>
    cases locationResult : world.locateActivationId activation with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateActivationId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsActivationId query) location
            (fun heap => applyActivationCommand heap
              (.activationLocalWrite mirror activation slot value))
            (fun before after updateResult =>
              applyActivationCommand_preserves_containsActivationId
                (.activationLocalWrite mirror activation slot value) query
                updateResult)
            result
  case changeActivationCurrentClass mirror activation classId =>
    cases locationResult : world.locateActivationId activation with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateActivationId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsActivationId query) location
            (fun heap => applyActivationCommand heap
              (.changeActivationCurrentClass mirror activation classId))
            (fun before after updateResult =>
              applyActivationCommand_preserves_containsActivationId
                (.changeActivationCurrentClass mirror activation classId)
                query updateResult)
            result
  case changeActivationContinuation mirror activation continuation =>
    cases locationResult : world.locateActivationId activation with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateActivationId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsActivationId query) location
            (fun heap => applyActivationCommand heap
              (.changeActivationContinuation mirror activation continuation))
            (fun before after updateResult =>
              applyActivationCommand_preserves_containsActivationId
                (.changeActivationContinuation mirror activation continuation)
                query updateResult)
            result
  case makeActivationUncontinuable mirror activation =>
    cases locationResult : world.locateActivationId activation with
    | none => simp [locationResult] at result
    | some location =>
        simp [locationResult] at result
        simpa [ActorWorld.locateActivationId] using
          ActorWorld.locateHeapSatisfying_updateHeapAt
            (fun heap => heap.containsActivationId query) location
            (fun heap => applyActivationCommand heap
              (.makeActivationUncontinuable mirror activation))
            (fun before after updateResult =>
              applyActivationCommand_preserves_containsActivationId
                (.makeActivationUncontinuable mirror activation) query
                updateResult)
            result

theorem applyCohortClassGraphCommand_eq_located
    {command : ReflectionCommand} {classId : ClassId}
    (decoded : classGraphCommandClass? command = some classId)
    (world : ActorWorld) :
    applyCohortClassGraphCommand world command =
      applyLocatedHeapUpdate world (fun heap => heap.containsClassId classId)
        (fun heap => applyClassGraphCommand heap command) := by
  simp [applyCohortClassGraphCommand, applyLocatedHeapUpdate,
    ActorWorld.locateClassId, decoded]

theorem applyCohortObjectClassCommand_eq_located
    {command : ReflectionCommand} {object : ObjectId}
    (decoded : objectClassCommandObject? command = some object)
    (world : ActorWorld) :
    applyCohortObjectClassCommand world command =
      applyLocatedHeapUpdate world (fun heap => heap.containsObjectId object)
        (fun heap => applyObjectClassCommand heap command) := by
  simp [applyCohortObjectClassCommand, applyLocatedHeapUpdate,
    ActorWorld.locateObjectId, decoded]

theorem applyCohortObjectSlotCommand_eq_located
    (program : Program) {command : ReflectionCommand} {object : ObjectId}
    (decoded : objectSlotCommandObject? command = some object)
    (world : ActorWorld) :
    applyCohortObjectSlotCommand program world command =
      applyLocatedHeapUpdate world (fun heap => heap.containsObjectId object)
        (fun heap => applyReflectiveObjectSlotCommand program heap command) := by
  simp [applyCohortObjectSlotCommand, applyLocatedHeapUpdate,
    ActorWorld.locateObjectId, decoded]

theorem applyCohortActivationCommand_eq_located
    {command : ReflectionCommand} {activation : ActivationId}
    (decoded : activationCommandActivation? command = some activation)
    (world : ActorWorld) :
    applyCohortActivationCommand world command =
      applyLocatedHeapUpdate world
        (fun heap => heap.containsActivationId activation)
        (fun heap => applyActivationCommand heap command) := by
  simp [applyCohortActivationCommand, applyLocatedHeapUpdate,
    ActorWorld.locateActivationId, decoded]

theorem compatibleCohortClassGraphCommands_commute
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute applyCohortClassGraphCommand first second := by
  cases firstDecoded : classGraphCommandClass? first with
  | none =>
      exact OptionalCommandsCommute.of_left_failure fun world => by
        simp [applyCohortClassGraphCommand, firstDecoded]
  | some firstClass =>
      cases secondDecoded : classGraphCommandClass? second with
      | none =>
          exact OptionalCommandsCommute.of_right_failure fun world => by
            simp [applyCohortClassGraphCommand, secondDecoded]
      | some secondClass =>
          intro world
          simp only [applyCohortClassGraphCommand_eq_located firstDecoded,
            applyCohortClassGraphCommand_eq_located secondDecoded]
          exact applyLocatedHeapUpdates_commute world
            (fun heap => heap.containsClassId firstClass)
            (fun heap => heap.containsClassId secondClass)
            (fun heap => applyClassGraphCommand heap first)
            (fun heap => applyClassGraphCommand heap second)
            (fun before after result =>
              applyClassGraphCommand_preserves_containsClassId first
                secondClass result)
            (fun before after result =>
              applyClassGraphCommand_preserves_containsClassId second
                firstClass result)
            (compatibleClassGraphCommands_commute compatible)

theorem compatibleCohortObjectClassCommands_commute
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute applyCohortObjectClassCommand first second := by
  cases firstDecoded : objectClassCommandObject? first with
  | none =>
      exact OptionalCommandsCommute.of_left_failure fun world => by
        simp [applyCohortObjectClassCommand, firstDecoded]
  | some firstObject =>
      cases secondDecoded : objectClassCommandObject? second with
      | none =>
          exact OptionalCommandsCommute.of_right_failure fun world => by
            simp [applyCohortObjectClassCommand, secondDecoded]
      | some secondObject =>
          intro world
          simp only [applyCohortObjectClassCommand_eq_located firstDecoded,
            applyCohortObjectClassCommand_eq_located secondDecoded]
          exact applyLocatedHeapUpdates_commute world
            (fun heap => heap.containsObjectId firstObject)
            (fun heap => heap.containsObjectId secondObject)
            (fun heap => applyObjectClassCommand heap first)
            (fun heap => applyObjectClassCommand heap second)
            (fun before after result =>
              applyObjectClassCommand_preserves_containsObjectId first
                secondObject result)
            (fun before after result =>
              applyObjectClassCommand_preserves_containsObjectId second
                firstObject result)
            (compatibleObjectClassCommands_commute compatible)

theorem compatibleCohortObjectSlotCommands_commute
    (program : Program) {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute (applyCohortObjectSlotCommand program)
      first second := by
  cases firstDecoded : objectSlotCommandObject? first with
  | none =>
      exact OptionalCommandsCommute.of_left_failure fun world => by
        simp [applyCohortObjectSlotCommand, firstDecoded]
  | some firstObject =>
      cases secondDecoded : objectSlotCommandObject? second with
      | none =>
          exact OptionalCommandsCommute.of_right_failure fun world => by
            simp [applyCohortObjectSlotCommand, secondDecoded]
      | some secondObject =>
          intro world
          simp only [applyCohortObjectSlotCommand_eq_located program
              firstDecoded,
            applyCohortObjectSlotCommand_eq_located program secondDecoded]
          exact applyLocatedHeapUpdates_commute world
            (fun heap => heap.containsObjectId firstObject)
            (fun heap => heap.containsObjectId secondObject)
            (fun heap => applyReflectiveObjectSlotCommand program heap first)
            (fun heap => applyReflectiveObjectSlotCommand program heap second)
            (fun before after result =>
              applyReflectiveObjectSlotCommand_preserves_containsObjectId
                program first secondObject result)
            (fun before after result =>
              applyReflectiveObjectSlotCommand_preserves_containsObjectId
                program second firstObject result)
            (compatibleObjectSlotCommands_commute program compatible)

theorem compatibleCohortActivationCommands_commute
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommute applyCohortActivationCommand first second := by
  cases firstDecoded : activationCommandActivation? first with
  | none =>
      exact OptionalCommandsCommute.of_left_failure fun world => by
        simp [applyCohortActivationCommand, firstDecoded]
  | some firstActivation =>
      cases secondDecoded : activationCommandActivation? second with
      | none =>
          exact OptionalCommandsCommute.of_right_failure fun world => by
            simp [applyCohortActivationCommand, secondDecoded]
      | some secondActivation =>
          intro world
          simp only [applyCohortActivationCommand_eq_located firstDecoded,
            applyCohortActivationCommand_eq_located secondDecoded]
          exact applyLocatedHeapUpdates_commute world
            (fun heap => heap.containsActivationId firstActivation)
            (fun heap => heap.containsActivationId secondActivation)
            (fun heap => applyActivationCommand heap first)
            (fun heap => applyActivationCommand heap second)
            (fun before after result =>
              applyActivationCommand_preserves_containsActivationId first
                secondActivation result)
            (fun before after result =>
              applyActivationCommand_preserves_containsActivationId second
                firstActivation result)
            (compatibleActivationCommands_commute compatible)

theorem cohortClassGraphTransactionIndependent_of_nonconflicting
    {transaction : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting transaction) :
    CohortClassGraphTransactionIndependent transaction := by
  unfold CohortClassGraphTransactionIndependent classGraphCommands
  exact (nonconflicting.filter _).imp fun compatible =>
    compatibleCohortClassGraphCommands_commute compatible

theorem cohortObjectClassTransactionIndependent_of_nonconflicting
    {transaction : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting transaction) :
    CohortObjectClassTransactionIndependent transaction := by
  unfold CohortObjectClassTransactionIndependent objectClassCommands
  exact (nonconflicting.filter _).imp fun compatible =>
    compatibleCohortObjectClassCommands_commute compatible

theorem cohortObjectSlotTransactionIndependent_of_nonconflicting
    (program : Program) {transaction : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting transaction) :
    CohortObjectSlotTransactionIndependent program transaction := by
  unfold CohortObjectSlotTransactionIndependent objectSlotCommands
  exact (nonconflicting.filter _).imp fun compatible =>
    compatibleCohortObjectSlotCommands_commute program compatible

theorem cohortActivationTransactionIndependent_of_nonconflicting
    {transaction : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting transaction) :
    CohortActivationTransactionIndependent transaction := by
  unfold CohortActivationTransactionIndependent activationCommands
  exact (nonconflicting.filter _).imp fun compatible =>
    compatibleCohortActivationCommands_commute compatible

theorem reflectionRuntimePermutationCertificates_of_nonconflicting
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    {original permuted : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting original)
    (permutation : original.Perm permuted)
    (initialCoherent : ActorStoreDomainsCoherent before.world) :
    ReflectionRuntimePermutationCertificates before requester original
      permuted :=
  { classIndependent :=
      cohortClassGraphTransactionIndependent_of_nonconflicting nonconflicting
    objectClassIndependent :=
      cohortObjectClassTransactionIndependent_of_nonconflicting nonconflicting
    slotIndependent := fun program =>
      cohortObjectSlotTransactionIndependent_of_nonconflicting program
        nonconflicting
    activationIndependent :=
      cohortActivationTransactionIndependent_of_nonconflicting nonconflicting
    debuggerIndependent := fun program =>
      debuggerTransactionIndependent_of_nonconflicting materializeStackTemplate
        program requester nonconflicting
    nonconflicting := nonconflicting
    permutation := permutation
    initialCoherent := initialCoherent }

theorem compatibleSlotDeclarationCommands_have_distinct_mixins
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    {firstGroups secondGroups : List SlotDeclarationGroup}
    (compatible : ReflectionCommandsCompatible
      (.replaceSlotDeclarations firstMirror first firstGroups)
      (.replaceSlotDeclarations secondMirror second secondGroups)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.slotDeclarations first)
    (by simp [ReflectionCommand.writes]) (.slotDeclarations first)
    (by simp [ReflectionCommand.writes]) (.same (.slotDeclarations first))

theorem compatibleNestedDeclarationCommands_have_distinct_mixins
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    {firstDeclarations secondDeclarations : List ClassDeclId}
    (compatible : ReflectionCommandsCompatible
      (.replaceNestedDeclarations firstMirror first firstDeclarations)
      (.replaceNestedDeclarations secondMirror second secondDeclarations)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.nestedDeclarations first)
    (by simp [ReflectionCommand.writes]) (.nestedDeclarations first)
    (by simp [ReflectionCommand.writes]) (.same (.nestedDeclarations first))

theorem compatibleMixinInitializerCommands_have_distinct_mixins
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    {firstInitializer secondInitializer : MixinInitializerReplacement}
    (compatible : ReflectionCommandsCompatible
      (.replaceMixinInitializer firstMirror first firstInitializer)
      (.replaceMixinInitializer secondMirror second secondInitializer)) :
    first ≠ second := by
  intro equal
  subst second
  exact compatible (.mixinInitializer first)
    (by simp [ReflectionCommand.writes]) (.mixinInitializer first)
    (by simp [ReflectionCommand.writes]) (.same (.mixinInitializer first))

theorem replaceMethodBodyCommands_commuteAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId} {first second : MethodId}
    (firstBody secondBody : List Statement)
    {firstOwner secondOwner : MixinId}
    {oldFirstBody oldSecondBody : List Statement}
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodBody firstMirror first firstBody)
      (.replaceMethodBody secondMirror second secondBody))
    (firstOwnerPresent : source.methodMixins first = some firstOwner)
    (secondOwnerPresent : source.methodMixins second = some secondOwner)
    (firstBodyPresent : source.methodBodies first = some oldFirstBody)
    (secondBodyPresent : source.methodBodies second = some oldSecondBody) :
    SourceCodeCommandsCommuteAt source
      (.replaceMethodBody firstMirror first firstBody)
      (.replaceMethodBody secondMirror second secondBody) := by
  simpa [SourceCodeCommandsCommuteAt,
    IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceMethodBody_commutes
      (compatibleMethodBodyCommands_have_distinct_methods compatible)
      firstBody secondBody firstOwnerPresent secondOwnerPresent
      firstBodyPresent secondBodyPresent

theorem removeMethodDefinitionCommands_commuteAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    {firstSelector secondSelector : Selector}
    {firstMixinDefinition secondMixinDefinition : MixinDef}
    {firstMethodDefinition secondMethodDefinition : MethodDef}
    (compatible : ReflectionCommandsCompatible
      (.removeMethodDefinition firstMirror firstMixin firstMethod)
      (.removeMethodDefinition secondMirror secondMixin secondMethod))
    (firstOwnerPresent :
      source.methodMixins firstMethod = some firstMixin)
    (secondOwnerPresent :
      source.methodMixins secondMethod = some secondMixin)
    (firstSelectorPresent :
      source.methodSelectors firstMethod = some firstSelector)
    (secondSelectorPresent :
      source.methodSelectors secondMethod = some secondSelector)
    (firstMixinPresent :
      source.mixins firstMixin = some firstMixinDefinition)
    (secondMixinPresent :
      source.mixins secondMixin = some secondMixinDefinition)
    (firstDefinitionPresent :
      firstMixinDefinition.methods firstSelector = some firstMethodDefinition)
    (secondDefinitionPresent :
      secondMixinDefinition.methods secondSelector = some secondMethodDefinition)
    (firstIdentity : firstMethodDefinition.identity = firstMethod)
    (secondIdentity : secondMethodDefinition.identity = secondMethod) :
    SourceCodeCommandsCommuteAt source
      (.removeMethodDefinition firstMirror firstMixin firstMethod)
      (.removeMethodDefinition secondMirror secondMixin secondMethod) := by
  have distinct := compatibleRemoveMethodCommands_have_distinct_targets compatible
  simpa [SourceCodeCommandsCommuteAt,
    IdentifiedSourceImage.patchSourceCodeCommand] using
    source.removeSourceMethodDefinition_commutes distinct.1 distinct.2
      firstOwnerPresent secondOwnerPresent firstSelectorPresent
      secondSelectorPresent firstMixinPresent secondMixinPresent
      firstDefinitionPresent secondDefinitionPresent firstIdentity secondIdentity

theorem replaceMethodDefinitionCommands_commuteAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    {firstOldSelector secondOldSelector : Selector}
    {firstMixinDefinition secondMixinDefinition : MixinDef}
    {firstOldDefinition secondOldDefinition : MethodDef}
    {firstOldBody secondOldBody : List Statement}
    {firstOldLocals secondOldLocals : List LocalDeclarationGroup}
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodDefinition firstMirror firstMixin firstMethod
        firstDefinition firstLocals firstBody)
      (.replaceMethodDefinition secondMirror secondMixin secondMethod
        secondDefinition secondLocals secondBody))
    (firstIdentity : firstDefinition.identity = firstMethod)
    (secondIdentity : secondDefinition.identity = secondMethod)
    (firstOwnerPresent : source.methodMixins firstMethod = some firstMixin)
    (secondOwnerPresent : source.methodMixins secondMethod = some secondMixin)
    (firstSelectorPresent :
      source.methodSelectors firstMethod = some firstOldSelector)
    (secondSelectorPresent :
      source.methodSelectors secondMethod = some secondOldSelector)
    (firstMixinPresent :
      source.mixins firstMixin = some firstMixinDefinition)
    (secondMixinPresent :
      source.mixins secondMixin = some secondMixinDefinition)
    (firstOldPresent :
      firstMixinDefinition.methods firstOldSelector = some firstOldDefinition)
    (secondOldPresent :
      secondMixinDefinition.methods secondOldSelector = some secondOldDefinition)
    (firstOldIdentity : firstOldDefinition.identity = firstMethod)
    (secondOldIdentity : secondOldDefinition.identity = secondMethod)
    (firstNewOwner :
      firstDefinition.owner = firstMixinDefinition.declaration)
    (secondNewOwner :
      secondDefinition.owner = secondMixinDefinition.declaration)
    (firstNewSelectorAvailable :
      IdentifiedSourceImage.replacementSelectorAvailable firstMixinDefinition
        firstMethod firstDefinition.selector = true)
    (secondNewSelectorAvailable :
      IdentifiedSourceImage.replacementSelectorAvailable secondMixinDefinition
        secondMethod secondDefinition.selector = true)
    (firstBodyPresent : source.methodBodies firstMethod = some firstOldBody)
    (secondBodyPresent : source.methodBodies secondMethod = some secondOldBody)
    (firstLocalsPresent :
      source.methodLocals firstMethod = some firstOldLocals)
    (secondLocalsPresent :
      source.methodLocals secondMethod = some secondOldLocals) :
    SourceCodeCommandsCommuteAt source
      (.replaceMethodDefinition firstMirror firstMixin firstMethod
        firstDefinition firstLocals firstBody)
      (.replaceMethodDefinition secondMirror secondMixin secondMethod
        secondDefinition secondLocals secondBody) := by
  have distinct :=
    compatibleReplaceMethodDefinitionCommands_have_distinct_targets compatible
  simpa [SourceCodeCommandsCommuteAt,
    IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceMethodDefinition_commutes distinct.1 distinct.2
      firstDefinition secondDefinition firstLocals secondLocals firstBody
      secondBody firstIdentity secondIdentity firstOwnerPresent
      secondOwnerPresent firstSelectorPresent secondSelectorPresent
      firstMixinPresent secondMixinPresent firstOldPresent secondOldPresent
      firstOldIdentity secondOldIdentity firstNewOwner secondNewOwner
      firstNewSelectorAvailable secondNewSelectorAvailable firstBodyPresent
      secondBodyPresent firstLocalsPresent secondLocalsPresent

theorem addMethodDefinitionCommands_commuteExtensionallyAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId}
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    {firstMixinDefinition secondMixinDefinition : MixinDef}
    (compatible : ReflectionCommandsCompatible
      (.addMethodDefinition firstMirror firstMixin firstDefinition firstLocals
        firstBody)
      (.addMethodDefinition secondMirror secondMixin secondDefinition secondLocals
        secondBody))
    (firstMixinPresent :
      source.mixins firstMixin = some firstMixinDefinition)
    (secondMixinPresent :
      source.mixins secondMixin = some secondMixinDefinition)
    (firstMethodFresh :
      source.methodMixins firstDefinition.identity = none)
    (secondMethodFresh :
      source.methodMixins secondDefinition.identity = none)
    (firstSelectorFresh :
      source.methodSelectors firstDefinition.identity = none)
    (secondSelectorFresh :
      source.methodSelectors secondDefinition.identity = none)
    (firstBodyFresh : source.methodBodies firstDefinition.identity = none)
    (secondBodyFresh : source.methodBodies secondDefinition.identity = none)
    (firstLocalsFresh : source.methodLocals firstDefinition.identity = none)
    (secondLocalsFresh : source.methodLocals secondDefinition.identity = none)
    (firstDictionaryFresh :
      firstMixinDefinition.methods firstDefinition.selector = none)
    (secondDictionaryFresh :
      secondMixinDefinition.methods secondDefinition.selector = none)
    (firstOwner : firstDefinition.owner = firstMixinDefinition.declaration)
    (secondOwner : secondDefinition.owner = secondMixinDefinition.declaration) :
    OptionalResultsRelated IdentifiedSourceImage.LookupEquivalent
      (do
        let afterFirst ← source.patchSourceCodeCommand
          (.addMethodDefinition firstMirror firstMixin firstDefinition
            firstLocals firstBody)
        afterFirst.patchSourceCodeCommand
          (.addMethodDefinition secondMirror secondMixin secondDefinition
            secondLocals secondBody))
      (do
        let afterSecond ← source.patchSourceCodeCommand
          (.addMethodDefinition secondMirror secondMixin secondDefinition
            secondLocals secondBody)
        afterSecond.patchSourceCodeCommand
          (.addMethodDefinition firstMirror firstMixin firstDefinition
            firstLocals firstBody)) := by
  have distinct := compatibleAddMethodCommands_have_distinct_targets compatible
  simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
    source.addSourceMethodDefinition_commutes_extensionally distinct.1
      firstDefinition secondDefinition distinct.2 firstLocals secondLocals
      firstBody secondBody firstMixinPresent secondMixinPresent
      firstMethodFresh secondMethodFresh firstSelectorFresh secondSelectorFresh
      firstBodyFresh secondBodyFresh firstLocalsFresh secondLocalsFresh
      firstDictionaryFresh secondDictionaryFresh firstOwner secondOwner

theorem replaceSlotDeclarationCommands_commuteAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    (firstGroups secondGroups : List SlotDeclarationGroup)
    {firstDefinition secondDefinition : MixinDef}
    (compatible : ReflectionCommandsCompatible
      (.replaceSlotDeclarations firstMirror first firstGroups)
      (.replaceSlotDeclarations secondMirror second secondGroups))
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    SourceCodeCommandsCommuteAt source
      (.replaceSlotDeclarations firstMirror first firstGroups)
      (.replaceSlotDeclarations secondMirror second secondGroups) := by
  simpa [SourceCodeCommandsCommuteAt,
    IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceSlotDeclarations_commutes
      (compatibleSlotDeclarationCommands_have_distinct_mixins compatible)
      firstGroups secondGroups firstPresent secondPresent

theorem replaceNestedDeclarationCommands_commuteAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    (firstDeclarations secondDeclarations : List ClassDeclId)
    {firstDefinition secondDefinition : MixinDef}
    (compatible : ReflectionCommandsCompatible
      (.replaceNestedDeclarations firstMirror first firstDeclarations)
      (.replaceNestedDeclarations secondMirror second secondDeclarations))
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    SourceCodeCommandsCommuteAt source
      (.replaceNestedDeclarations firstMirror first firstDeclarations)
      (.replaceNestedDeclarations secondMirror second secondDeclarations) := by
  simpa [SourceCodeCommandsCommuteAt,
    IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceNestedDeclarations_commutes
      (compatibleNestedDeclarationCommands_have_distinct_mixins compatible)
      firstDeclarations secondDeclarations firstPresent secondPresent

theorem replaceMixinInitializerCommands_commuteAt
    (source : IdentifiedSourceImage)
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    (firstInitializer secondInitializer : MixinInitializerReplacement)
    {firstDefinition secondDefinition : MixinDef}
    (compatible : ReflectionCommandsCompatible
      (.replaceMixinInitializer firstMirror first firstInitializer)
      (.replaceMixinInitializer secondMirror second secondInitializer))
    (firstPresent : source.mixins first = some firstDefinition)
    (secondPresent : source.mixins second = some secondDefinition) :
    SourceCodeCommandsCommuteAt source
      (.replaceMixinInitializer firstMirror first firstInitializer)
      (.replaceMixinInitializer secondMirror second secondInitializer) := by
  simpa [SourceCodeCommandsCommuteAt,
    IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceMixinInitializer_commutes
      (compatibleMixinInitializerCommands_have_distinct_mixins compatible)
      firstInitializer secondInitializer firstPresent secondPresent

theorem compatibleReplaceMethodBodyCommands_commute
    {firstMirror secondMirror : MirrorId} {first second : MethodId}
    (firstBody secondBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodBody firstMirror first firstBody)
      (.replaceMethodBody secondMirror second secondBody)) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody firstMirror first firstBody)
      (.replaceMethodBody secondMirror second secondBody) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceMethodBody_distinct_commutes_total
      (compatibleMethodBodyCommands_have_distinct_methods compatible)
      firstBody secondBody

theorem replaceMethodBodyAndSlotDeclarationsCommands_commute
    {bodyMirror slotMirror : MirrorId} (method : MethodId)
    (body : List Statement) (mixin : MixinId)
    (groups : List SlotDeclarationGroup) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody bodyMirror method body)
      (.replaceSlotDeclarations slotMirror mixin groups) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand,
    IdentifiedSourceImage.replaceSourceSlotDeclarations] using
    source.replaceSourceMethodBody_and_mixinTransform_commute_total method body
      mixin (IdentifiedSourceImage.sourceSlotDeclarationTransform groups)

theorem replaceMethodBodyAndNestedDeclarationsCommands_commute
    {bodyMirror nestedMirror : MirrorId} (method : MethodId)
    (body : List Statement) (mixin : MixinId)
    (declarations : List ClassDeclId) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody bodyMirror method body)
      (.replaceNestedDeclarations nestedMirror mixin declarations) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand,
    IdentifiedSourceImage.replaceSourceNestedDeclarations] using
    source.replaceSourceMethodBody_and_mixinTransform_commute_total method body
      mixin (IdentifiedSourceImage.sourceNestedDeclarationTransform declarations)

theorem replaceMethodBodyAndMixinInitializerCommands_commute
    {bodyMirror initializerMirror : MirrorId} (method : MethodId)
    (body : List Statement) (mixin : MixinId)
    (initializer : MixinInitializerReplacement) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody bodyMirror method body)
      (.replaceMixinInitializer initializerMirror mixin initializer) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand,
    IdentifiedSourceImage.replaceSourceMixinInitializer] using
    source.replaceSourceMethodBody_and_mixinTransform_commute_total method body
      mixin (IdentifiedSourceImage.sourceMixinInitializerTransform initializer)

theorem compatibleReplaceSlotDeclarationsCommands_commute
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    (firstGroups secondGroups : List SlotDeclarationGroup)
    (compatible : ReflectionCommandsCompatible
      (.replaceSlotDeclarations firstMirror first firstGroups)
      (.replaceSlotDeclarations secondMirror second secondGroups)) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceSlotDeclarations firstMirror first firstGroups)
      (.replaceSlotDeclarations secondMirror second secondGroups) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand,
    IdentifiedSourceImage.replaceSourceSlotDeclarations] using
    source.transformExistingSourceMixin_distinct_commutes_total
      (compatibleSlotDeclarationCommands_have_distinct_mixins compatible) _ _

theorem compatibleReplaceNestedDeclarationsCommands_commute
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    (firstDeclarations secondDeclarations : List ClassDeclId)
    (compatible : ReflectionCommandsCompatible
      (.replaceNestedDeclarations firstMirror first firstDeclarations)
      (.replaceNestedDeclarations secondMirror second secondDeclarations)) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceNestedDeclarations firstMirror first firstDeclarations)
      (.replaceNestedDeclarations secondMirror second secondDeclarations) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand,
    IdentifiedSourceImage.replaceSourceNestedDeclarations] using
    source.transformExistingSourceMixin_distinct_commutes_total
      (compatibleNestedDeclarationCommands_have_distinct_mixins compatible) _ _

theorem compatibleReplaceMixinInitializerCommands_commute
    {firstMirror secondMirror : MirrorId} {first second : MixinId}
    (firstInitializer secondInitializer : MixinInitializerReplacement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMixinInitializer firstMirror first firstInitializer)
      (.replaceMixinInitializer secondMirror second secondInitializer)) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMixinInitializer firstMirror first firstInitializer)
      (.replaceMixinInitializer secondMirror second secondInitializer) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand,
    IdentifiedSourceImage.replaceSourceMixinInitializer] using
    source.transformExistingSourceMixin_distinct_commutes_total
      (compatibleMixinInitializerCommands_have_distinct_mixins compatible) _ _

theorem replaceSlotAndNestedDeclarationsCommands_commute
    {slotMirror nestedMirror : MirrorId} (slotMixin nestedMixin : MixinId)
    (groups : List SlotDeclarationGroup)
    (declarations : List ClassDeclId) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceSlotDeclarations slotMirror slotMixin groups)
      (.replaceNestedDeclarations nestedMirror nestedMixin declarations) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceSlotAndNested_commute_total slotMixin nestedMixin
      groups declarations

theorem replaceSlotAndMixinInitializerCommands_commute
    {slotMirror initializerMirror : MirrorId} (slotMixin initializerMixin : MixinId)
    (groups : List SlotDeclarationGroup)
    (initializer : MixinInitializerReplacement) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceSlotDeclarations slotMirror slotMixin groups)
      (.replaceMixinInitializer initializerMirror initializerMixin
        initializer) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceSlotAndInitializer_commute_total slotMixin
      initializerMixin groups initializer

theorem replaceNestedAndMixinInitializerCommands_commute
    {nestedMirror initializerMirror : MirrorId}
    (nestedMixin initializerMixin : MixinId)
    (declarations : List ClassDeclId)
    (initializer : MixinInitializerReplacement) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceNestedDeclarations nestedMirror nestedMixin declarations)
      (.replaceMixinInitializer initializerMirror initializerMixin
        initializer) := by
  intro source
  simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
    source.replaceSourceNestedAndInitializer_commute_total nestedMixin
      initializerMixin declarations initializer

theorem replaceSourceMethodBody_success_witnesses
    (source : IdentifiedSourceImage) (method : MethodId)
    (body : List Statement)
    (success : (source.replaceSourceMethodBody method body).isSome = true) :
    ∃ owner oldBody,
      source.methodMixins method = some owner ∧
      source.methodBodies method = some oldBody := by
  cases ownerPresent : source.methodMixins method with
  | none =>
      simp [IdentifiedSourceImage.replaceSourceMethodBody, ownerPresent] at success
  | some owner =>
      cases bodyPresent : source.methodBodies method with
      | none =>
          simp [IdentifiedSourceImage.replaceSourceMethodBody, ownerPresent,
            bodyPresent] at success
      | some oldBody => exact ⟨owner, oldBody, rfl, rfl⟩

theorem replaceSourceMethodBody_isSome_eq_true_iff
    (source : IdentifiedSourceImage) (method : MethodId)
    (body : List Statement) :
    (source.replaceSourceMethodBody method body).isSome = true ↔
      ∃ owner oldBody,
        source.methodMixins method = some owner ∧
        source.methodBodies method = some oldBody := by
  constructor
  · exact replaceSourceMethodBody_success_witnesses source method body
  · rintro ⟨owner, oldBody, ownerPresent, bodyPresent⟩
    simp [IdentifiedSourceImage.replaceSourceMethodBody, ownerPresent,
      bodyPresent]

theorem addSourceMethodDefinition_isSome_eq_true_iff
    (source : IdentifiedSourceImage) (mixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) :
    (source.addSourceMethodDefinition mixin definition locals body).isSome =
        true ↔
      source.methodMixins definition.identity = none ∧
      source.methodSelectors definition.identity = none ∧
      source.methodBodies definition.identity = none ∧
      source.methodLocals definition.identity = none ∧
      ∃ mixinDefinition,
        source.mixins mixin = some mixinDefinition ∧
        mixinDefinition.methods definition.selector = none ∧
        definition.owner = mixinDefinition.declaration := by
  cases mixinPresent : source.mixins mixin with
  | none =>
      simp [IdentifiedSourceImage.addSourceMethodDefinition, guard,
        Alternative.failure, Option.bind, mixinPresent]
      repeat split <;> simp_all
  | some mixinDefinition =>
      simp [IdentifiedSourceImage.addSourceMethodDefinition, guard,
        Alternative.failure, Option.bind, mixinPresent]
      repeat split <;> simp_all

theorem replaceSourceMethodDefinition_isSome_eq_true_iff
    (source : IdentifiedSourceImage) (mixin : MixinId) (method : MethodId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) :
    (source.replaceSourceMethodDefinition mixin method definition locals
        body).isSome = true ↔
      definition.identity = method ∧
      ∃ oldSelector mixinDefinition oldDefinition,
        source.methodMixins method = some mixin ∧
        source.methodSelectors method = some oldSelector ∧
        source.mixins mixin = some mixinDefinition ∧
        mixinDefinition.methods oldSelector = some oldDefinition ∧
        oldDefinition.identity = method ∧
        definition.owner = mixinDefinition.declaration ∧
        IdentifiedSourceImage.replacementSelectorAvailable mixinDefinition
          method definition.selector = true := by
  cases ownerPresent : source.methodMixins method with
  | none =>
      simp [IdentifiedSourceImage.replaceSourceMethodDefinition, guard,
        Alternative.failure, Option.bind, ownerPresent]
      repeat split <;> simp_all
  | some owner =>
      cases selectorPresent : source.methodSelectors method with
      | none =>
          simp [IdentifiedSourceImage.replaceSourceMethodDefinition, guard,
            Alternative.failure, Option.bind, ownerPresent, selectorPresent]
          repeat split <;> simp_all
      | some oldSelector =>
          cases mixinPresent : source.mixins mixin with
          | none =>
              simp [IdentifiedSourceImage.replaceSourceMethodDefinition,
                guard, Alternative.failure, Option.bind, ownerPresent,
                selectorPresent, mixinPresent]
              repeat split <;> simp_all
          | some mixinDefinition =>
              cases definitionPresent : mixinDefinition.methods oldSelector with
              | none =>
                  simp [IdentifiedSourceImage.replaceSourceMethodDefinition,
                    guard, Alternative.failure, Option.bind, ownerPresent,
                    selectorPresent, mixinPresent, definitionPresent]
                  repeat split <;> simp_all
              | some oldDefinition =>
                  simp [IdentifiedSourceImage.replaceSourceMethodDefinition,
                    guard, Alternative.failure, Option.bind, ownerPresent,
                    selectorPresent, mixinPresent, definitionPresent]
                  repeat split <;> simp_all

theorem transformExistingSourceMixin_isSome_eq_true_iff
    (source : IdentifiedSourceImage) (mixin : MixinId)
    (transform : MixinDef → MixinDef) :
    (source.transformExistingSourceMixin mixin transform).isSome = true ↔
      ∃ definition, source.mixins mixin = some definition := by
  cases present : source.mixins mixin with
  | none => simp [IdentifiedSourceImage.transformExistingSourceMixin, present]
  | some definition =>
      simp [IdentifiedSourceImage.transformExistingSourceMixin, present]
theorem removeSourceMethodDefinition_success_witnesses
    (source : IdentifiedSourceImage) (mixin : MixinId) (method : MethodId)
    (success : (source.removeSourceMethodDefinition mixin method).isSome =
      true) :
    ∃ selector mixinDefinition methodDefinition,
      source.methodMixins method = some mixin ∧
      source.methodSelectors method = some selector ∧
      source.mixins mixin = some mixinDefinition ∧
      mixinDefinition.methods selector = some methodDefinition ∧
      methodDefinition.identity = method := by
  cases ownerPresent : source.methodMixins method with
  | none =>
      simp [IdentifiedSourceImage.removeSourceMethodDefinition, ownerPresent] at success
  | some owner =>
      by_cases ownerEqual : owner = mixin
      · subst owner
        cases selectorPresent : source.methodSelectors method with
        | none =>
            simp [IdentifiedSourceImage.removeSourceMethodDefinition,
              ownerPresent, selectorPresent] at success
        | some selector =>
            cases mixinPresent : source.mixins mixin with
            | none =>
                simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                  ownerPresent, selectorPresent, mixinPresent] at success
            | some mixinDefinition =>
                cases definitionPresent : mixinDefinition.methods selector with
                | none =>
                    simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                      ownerPresent, selectorPresent, mixinPresent,
                      definitionPresent] at success
                | some methodDefinition =>
                    by_cases identity : methodDefinition.identity = method
                    · exact ⟨selector, mixinDefinition, methodDefinition,
                        rfl, rfl, rfl, definitionPresent, identity⟩
                    · simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                        ownerPresent, selectorPresent, mixinPresent,
                        definitionPresent, identity, guard,
                        Alternative.failure, instAlternativeOption,
                        Option.bind] at success
      · simp [IdentifiedSourceImage.removeSourceMethodDefinition,
          ownerPresent, ownerEqual, guard, Alternative.failure,
          instAlternativeOption, Option.bind] at success

theorem removeSourceMethodDefinition_isSome_eq_true_iff
    (source : IdentifiedSourceImage) (mixin : MixinId) (method : MethodId) :
    (source.removeSourceMethodDefinition mixin method).isSome = true ↔
      ∃ selector mixinDefinition methodDefinition,
        source.methodMixins method = some mixin ∧
        source.methodSelectors method = some selector ∧
        source.mixins mixin = some mixinDefinition ∧
        mixinDefinition.methods selector = some methodDefinition ∧
        methodDefinition.identity = method := by
  constructor
  · exact removeSourceMethodDefinition_success_witnesses source mixin method
  · rintro ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
        selectorPresent, mixinPresent, definitionPresent, identity⟩
    simp [IdentifiedSourceImage.removeSourceMethodDefinition, ownerPresent,
      selectorPresent, mixinPresent, definitionPresent, identity, guard]

theorem removeSourceMethodDefinition_applicability_preserved_by_remove
    {before after : IdentifiedSourceImage}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    (mixinsDifferent : firstMixin ≠ secondMixin)
    (methodsDifferent : firstMethod ≠ secondMethod)
    (firstRemoved :
      before.removeSourceMethodDefinition firstMixin firstMethod = some after) :
    (before.removeSourceMethodDefinition secondMixin secondMethod).isSome =
      (after.removeSourceMethodDefinition secondMixin secondMethod).isSome := by
  have firstSuccess :
      (before.removeSourceMethodDefinition firstMixin firstMethod).isSome =
        true := by simp [firstRemoved]
  obtain ⟨firstSelector, firstMixinDefinition, firstMethodDefinition,
      firstOwnerPresent, firstSelectorPresent, firstMixinPresent,
      firstDefinitionPresent, firstIdentity⟩ :=
    removeSourceMethodDefinition_success_witnesses before firstMixin
      firstMethod firstSuccess
  simp [IdentifiedSourceImage.removeSourceMethodDefinition,
    firstOwnerPresent, firstSelectorPresent, firstMixinPresent,
    firstDefinitionPresent, firstIdentity, guard] at firstRemoved
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [removeSourceMethodDefinition_isSome_eq_true_iff,
    removeSourceMethodDefinition_isSome_eq_true_iff]
  constructor
  · rintro ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
        selectorPresent, mixinPresent, definitionPresent, identity⟩
    exact ⟨selector, mixinDefinition, methodDefinition,
      by simpa [methodsDifferent.symm] using ownerPresent,
      by simpa [methodsDifferent.symm] using selectorPresent,
      by simpa [mixinsDifferent.symm] using mixinPresent,
      definitionPresent, identity⟩
  · rintro ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
        selectorPresent, mixinPresent, definitionPresent, identity⟩
    exact ⟨selector, mixinDefinition, methodDefinition,
      by simpa [methodsDifferent.symm] using ownerPresent,
      by simpa [methodsDifferent.symm] using selectorPresent,
      by simpa [mixinsDifferent.symm] using mixinPresent,
      definitionPresent, identity⟩

theorem replaceSourceMethodBody_applicability_preserved_by_add
    {before after : IdentifiedSourceImage} {bodyMethod : MethodId}
    (body : List Statement) (addedMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (addedBody : List Statement)
    (different : bodyMethod ≠ definition.identity)
    (added : before.addSourceMethodDefinition addedMixin definition locals
      addedBody = some after) :
    (before.replaceSourceMethodBody bodyMethod body).isSome =
      (after.replaceSourceMethodBody bodyMethod body).isSome := by
  have success :
      (before.addSourceMethodDefinition addedMixin definition locals
        addedBody).isSome = true := by simp [added]
  obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
      mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
    (addSourceMethodDefinition_isSome_eq_true_iff before addedMixin definition
      locals addedBody).mp success
  simp [IdentifiedSourceImage.addSourceMethodDefinition, methodFresh,
    selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
    owner, guard] at added
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodBody_isSome_eq_true_iff,
    replaceSourceMethodBody_isSome_eq_true_iff]
  constructor
  · rintro ⟨bodyOwner, oldBody, ownerPresent, bodyPresent⟩
    exact ⟨bodyOwner, oldBody,
      by simpa [different] using ownerPresent,
      by simpa [different] using bodyPresent⟩
  · rintro ⟨bodyOwner, oldBody, ownerPresent, bodyPresent⟩
    exact ⟨bodyOwner, oldBody,
      by simpa [different] using ownerPresent,
      by simpa [different] using bodyPresent⟩

theorem addSourceMethodDefinition_applicability_preserved_by_body
    {before after : IdentifiedSourceImage} (bodyMethod : MethodId)
    (body : List Statement) (addedMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (addedBody : List Statement)
    (different : bodyMethod ≠ definition.identity)
    (replaced : before.replaceSourceMethodBody bodyMethod body = some after) :
    (before.addSourceMethodDefinition addedMixin definition locals
        addedBody).isSome =
      (after.addSourceMethodDefinition addedMixin definition locals
        addedBody).isSome := by
  have success : (before.replaceSourceMethodBody bodyMethod body).isSome =
      true := by simp [replaced]
  obtain ⟨bodyOwner, oldBody, ownerPresent, bodyPresent⟩ :=
    replaceSourceMethodBody_success_witnesses before bodyMethod body success
  simp [IdentifiedSourceImage.replaceSourceMethodBody, ownerPresent,
    bodyPresent] at replaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [addSourceMethodDefinition_isSome_eq_true_iff,
    addSourceMethodDefinition_isSome_eq_true_iff]
  simp [different.symm]

theorem addSourceMethodDefinition_applicability_preserved_by_add
    {before after : IdentifiedSourceImage}
    {firstMixin secondMixin : MixinId}
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    (mixinsDifferent : firstMixin ≠ secondMixin)
    (methodsDifferent : firstDefinition.identity ≠ secondDefinition.identity)
    (firstAdded : before.addSourceMethodDefinition firstMixin firstDefinition
      firstLocals firstBody = some after) :
    (before.addSourceMethodDefinition secondMixin secondDefinition secondLocals
        secondBody).isSome =
      (after.addSourceMethodDefinition secondMixin secondDefinition secondLocals
        secondBody).isSome := by
  have success := congrArg Option.isSome firstAdded
  simp only [Option.isSome_some] at success
  obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
      mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
    (addSourceMethodDefinition_isSome_eq_true_iff before firstMixin
      firstDefinition firstLocals firstBody).mp success
  simp [IdentifiedSourceImage.addSourceMethodDefinition, methodFresh,
    selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
    owner, guard] at firstAdded
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [addSourceMethodDefinition_isSome_eq_true_iff,
    addSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem removeSourceMethodDefinition_applicability_preserved_by_add
    {before after : IdentifiedSourceImage} {addedMixin removedMixin : MixinId}
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (addedBody : List Statement) (removedMethod : MethodId)
    (mixinsDifferent : addedMixin ≠ removedMixin)
    (methodsDifferent : definition.identity ≠ removedMethod)
    (added : before.addSourceMethodDefinition addedMixin definition locals
      addedBody = some after) :
    (before.removeSourceMethodDefinition removedMixin removedMethod).isSome =
      (after.removeSourceMethodDefinition removedMixin removedMethod).isSome := by
  have success := congrArg Option.isSome added
  simp only [Option.isSome_some] at success
  obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
      mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
    (addSourceMethodDefinition_isSome_eq_true_iff before addedMixin definition
      locals addedBody).mp success
  simp [IdentifiedSourceImage.addSourceMethodDefinition, methodFresh,
    selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
    owner, guard] at added
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [removeSourceMethodDefinition_isSome_eq_true_iff,
    removeSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem addSourceMethodDefinition_applicability_preserved_by_remove
    {before after : IdentifiedSourceImage} {removedMixin addedMixin : MixinId}
    (removedMethod : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (addedBody : List Statement)
    (mixinsDifferent : removedMixin ≠ addedMixin)
    (methodsDifferent : removedMethod ≠ definition.identity)
    (removed : before.removeSourceMethodDefinition removedMixin removedMethod =
      some after) :
    (before.addSourceMethodDefinition addedMixin definition locals
        addedBody).isSome =
      (after.addSourceMethodDefinition addedMixin definition locals
        addedBody).isSome := by
  have success := congrArg Option.isSome removed
  simp only [Option.isSome_some] at success
  obtain ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
      selectorPresent, mixinPresent, definitionPresent, identity⟩ :=
    removeSourceMethodDefinition_success_witnesses before removedMixin
      removedMethod success
  simp [IdentifiedSourceImage.removeSourceMethodDefinition, ownerPresent,
    selectorPresent, mixinPresent, definitionPresent, identity, guard] at removed
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [addSourceMethodDefinition_isSome_eq_true_iff,
    addSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem replaceSourceMethodBody_applicability_preserved_by_definitionReplacement
    {before after : IdentifiedSourceImage} {bodyMethod replacedMethod : MethodId}
    (body : List Statement) (replacedMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (replacementBody : List Statement)
    (different : bodyMethod ≠ replacedMethod)
    (replaced : before.replaceSourceMethodDefinition replacedMixin
      replacedMethod definition locals replacementBody = some after) :
    (before.replaceSourceMethodBody bodyMethod body).isSome =
      (after.replaceSourceMethodBody bodyMethod body).isSome := by
  have success := congrArg Option.isSome replaced
  simp only [Option.isSome_some] at success
  obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
      ownerPresent, selectorPresent, mixinPresent, definitionPresent,
      oldIdentity, newOwner, selectorAvailable⟩ :=
    (replaceSourceMethodDefinition_isSome_eq_true_iff before replacedMixin
      replacedMethod definition locals replacementBody).mp success
  simp [IdentifiedSourceImage.replaceSourceMethodDefinition, identity,
    ownerPresent, selectorPresent, mixinPresent, definitionPresent,
    oldIdentity, newOwner, selectorAvailable, guard] at replaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodBody_isSome_eq_true_iff,
    replaceSourceMethodBody_isSome_eq_true_iff]
  constructor
  · rintro ⟨bodyOwner, oldBody, bodyOwnerPresent, bodyPresent⟩
    exact ⟨bodyOwner, oldBody, bodyOwnerPresent,
      by simpa [different] using bodyPresent⟩
  · rintro ⟨bodyOwner, oldBody, bodyOwnerPresent, bodyPresent⟩
    exact ⟨bodyOwner, oldBody, bodyOwnerPresent,
      by simpa [different] using bodyPresent⟩

theorem replaceSourceMethodDefinition_applicability_preserved_by_body
    {before after : IdentifiedSourceImage} (bodyMethod : MethodId)
    (body : List Statement) (replacedMixin : MixinId)
    (replacedMethod : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (replacementBody : List Statement)
    (replaced : before.replaceSourceMethodBody bodyMethod body = some after) :
    (before.replaceSourceMethodDefinition replacedMixin replacedMethod
        definition locals replacementBody).isSome =
      (after.replaceSourceMethodDefinition replacedMixin replacedMethod
        definition locals replacementBody).isSome := by
  have success := congrArg Option.isSome replaced
  simp only [Option.isSome_some] at success
  obtain ⟨bodyOwner, oldBody, ownerPresent, bodyPresent⟩ :=
    replaceSourceMethodBody_success_witnesses before bodyMethod body success
  simp [IdentifiedSourceImage.replaceSourceMethodBody, ownerPresent,
    bodyPresent] at replaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodDefinition_isSome_eq_true_iff,
    replaceSourceMethodDefinition_isSome_eq_true_iff]

theorem replaceSourceMethodDefinition_applicability_preserved_by_replacement
    {before after : IdentifiedSourceImage}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    (mixinsDifferent : firstMixin ≠ secondMixin)
    (methodsDifferent : firstMethod ≠ secondMethod)
    (firstReplaced : before.replaceSourceMethodDefinition firstMixin
      firstMethod firstDefinition firstLocals firstBody = some after) :
    (before.replaceSourceMethodDefinition secondMixin secondMethod
        secondDefinition secondLocals secondBody).isSome =
      (after.replaceSourceMethodDefinition secondMixin secondMethod
        secondDefinition secondLocals secondBody).isSome := by
  have success := congrArg Option.isSome firstReplaced
  simp only [Option.isSome_some] at success
  obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
      ownerPresent, selectorPresent, mixinPresent, definitionPresent,
      oldIdentity, newOwner, selectorAvailable⟩ :=
    (replaceSourceMethodDefinition_isSome_eq_true_iff before firstMixin
      firstMethod firstDefinition firstLocals firstBody).mp success
  simp [IdentifiedSourceImage.replaceSourceMethodDefinition, identity,
    ownerPresent, selectorPresent, mixinPresent, definitionPresent,
    oldIdentity, newOwner, selectorAvailable, guard] at firstReplaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodDefinition_isSome_eq_true_iff,
    replaceSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem removeSourceMethodDefinition_applicability_preserved_by_replacement
    {before after : IdentifiedSourceImage}
    {replacedMixin removedMixin : MixinId}
    {replacedMethod removedMethod : MethodId}
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (replacementBody : List Statement)
    (mixinsDifferent : replacedMixin ≠ removedMixin)
    (methodsDifferent : replacedMethod ≠ removedMethod)
    (replaced : before.replaceSourceMethodDefinition replacedMixin
      replacedMethod definition locals replacementBody = some after) :
    (before.removeSourceMethodDefinition removedMixin removedMethod).isSome =
      (after.removeSourceMethodDefinition removedMixin removedMethod).isSome := by
  have success := congrArg Option.isSome replaced
  simp only [Option.isSome_some] at success
  obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
      ownerPresent, selectorPresent, mixinPresent, definitionPresent,
      oldIdentity, newOwner, selectorAvailable⟩ :=
    (replaceSourceMethodDefinition_isSome_eq_true_iff before replacedMixin
      replacedMethod definition locals replacementBody).mp success
  simp [IdentifiedSourceImage.replaceSourceMethodDefinition, identity,
    ownerPresent, selectorPresent, mixinPresent, definitionPresent,
    oldIdentity, newOwner, selectorAvailable, guard] at replaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [removeSourceMethodDefinition_isSome_eq_true_iff,
    removeSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem replaceSourceMethodDefinition_applicability_preserved_by_remove
    {before after : IdentifiedSourceImage}
    {removedMixin replacedMixin : MixinId}
    {removedMethod replacedMethod : MethodId}
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (replacementBody : List Statement)
    (mixinsDifferent : removedMixin ≠ replacedMixin)
    (methodsDifferent : removedMethod ≠ replacedMethod)
    (removed : before.removeSourceMethodDefinition removedMixin removedMethod =
      some after) :
    (before.replaceSourceMethodDefinition replacedMixin replacedMethod
        definition locals replacementBody).isSome =
      (after.replaceSourceMethodDefinition replacedMixin replacedMethod
        definition locals replacementBody).isSome := by
  have success := congrArg Option.isSome removed
  simp only [Option.isSome_some] at success
  obtain ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
      selectorPresent, mixinPresent, definitionPresent, identity⟩ :=
    removeSourceMethodDefinition_success_witnesses before removedMixin
      removedMethod success
  simp [IdentifiedSourceImage.removeSourceMethodDefinition, ownerPresent,
    selectorPresent, mixinPresent, definitionPresent, identity, guard] at removed
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodDefinition_isSome_eq_true_iff,
    replaceSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem addSourceMethodDefinition_applicability_preserved_by_replacement
    {before after : IdentifiedSourceImage}
    {replacedMixin addedMixin : MixinId} {replacedMethod : MethodId}
    (replacementDefinition addedDefinition : MethodDef)
    (replacementLocals addedLocals : List LocalDeclarationGroup)
    (replacementBody addedBody : List Statement)
    (mixinsDifferent : replacedMixin ≠ addedMixin)
    (methodsDifferent : replacedMethod ≠ addedDefinition.identity)
    (replaced : before.replaceSourceMethodDefinition replacedMixin
      replacedMethod replacementDefinition replacementLocals replacementBody =
      some after) :
    (before.addSourceMethodDefinition addedMixin addedDefinition addedLocals
        addedBody).isSome =
      (after.addSourceMethodDefinition addedMixin addedDefinition addedLocals
        addedBody).isSome := by
  have success := congrArg Option.isSome replaced
  simp only [Option.isSome_some] at success
  obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
      ownerPresent, selectorPresent, mixinPresent, definitionPresent,
      oldIdentity, newOwner, selectorAvailable⟩ :=
    (replaceSourceMethodDefinition_isSome_eq_true_iff before replacedMixin
      replacedMethod replacementDefinition replacementLocals
      replacementBody).mp success
  simp [IdentifiedSourceImage.replaceSourceMethodDefinition, identity,
    ownerPresent, selectorPresent, mixinPresent, definitionPresent,
    oldIdentity, newOwner, selectorAvailable, guard] at replaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [addSourceMethodDefinition_isSome_eq_true_iff,
    addSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem replaceSourceMethodDefinition_applicability_preserved_by_add
    {before after : IdentifiedSourceImage}
    {addedMixin replacedMixin : MixinId} {replacedMethod : MethodId}
    (addedDefinition replacementDefinition : MethodDef)
    (addedLocals replacementLocals : List LocalDeclarationGroup)
    (addedBody replacementBody : List Statement)
    (mixinsDifferent : addedMixin ≠ replacedMixin)
    (methodsDifferent : addedDefinition.identity ≠ replacedMethod)
    (added : before.addSourceMethodDefinition addedMixin addedDefinition
      addedLocals addedBody = some after) :
    (before.replaceSourceMethodDefinition replacedMixin replacedMethod
        replacementDefinition replacementLocals replacementBody).isSome =
      (after.replaceSourceMethodDefinition replacedMixin replacedMethod
        replacementDefinition replacementLocals replacementBody).isSome := by
  have success := congrArg Option.isSome added
  simp only [Option.isSome_some] at success
  obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
      mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
    (addSourceMethodDefinition_isSome_eq_true_iff before addedMixin
      addedDefinition addedLocals addedBody).mp success
  simp [IdentifiedSourceImage.addSourceMethodDefinition, methodFresh,
    selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
    owner, guard] at added
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodDefinition_isSome_eq_true_iff,
    replaceSourceMethodDefinition_isSome_eq_true_iff]
  simp [mixinsDifferent.symm, methodsDifferent.symm]

theorem replaceSourceMethodDefinition_applicability_preserved_by_mixinTransform
    {before after : IdentifiedSourceImage} (methodMixin fieldMixin : MixinId)
    (method : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement)
    (transform : MixinDef → MixinDef)
    (preservesDeclaration : ∀ mixin,
      (transform mixin).declaration = mixin.declaration)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (transformed : before.transformExistingSourceMixin fieldMixin transform =
      some after) :
    (before.replaceSourceMethodDefinition methodMixin method definition locals
        body).isSome =
      (after.replaceSourceMethodDefinition methodMixin method definition locals
        body).isSome := by
  have success := congrArg Option.isSome transformed
  simp only [Option.isSome_some] at success
  obtain ⟨fieldDefinition, fieldPresent⟩ :=
    (transformExistingSourceMixin_isSome_eq_true_iff before fieldMixin
      transform).mp success
  simp [IdentifiedSourceImage.transformExistingSourceMixin, fieldPresent] at transformed
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [replaceSourceMethodDefinition_isSome_eq_true_iff,
    replaceSourceMethodDefinition_isSome_eq_true_iff]
  have availabilityPreserved : ∀ mixin selector,
      IdentifiedSourceImage.replacementSelectorAvailable (transform mixin)
          method selector =
        IdentifiedSourceImage.replacementSelectorAvailable mixin method
          selector := by
    intro mixin selector
    unfold IdentifiedSourceImage.replacementSelectorAvailable
    rw [preservesMethods]
  by_cases same : fieldMixin = methodMixin
  · subst fieldMixin
    simp [fieldPresent, preservesDeclaration, preservesMethods,
      availabilityPreserved]
  · simp [fieldPresent, same, Ne.symm same]

theorem transformExistingSourceMixin_applicability_preserved_by_replacement
    {before after : IdentifiedSourceImage} (methodMixin fieldMixin : MixinId)
    (method : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement)
    (transform : MixinDef → MixinDef)
    (replaced : before.replaceSourceMethodDefinition methodMixin method
      definition locals body = some after) :
    (before.transformExistingSourceMixin fieldMixin transform).isSome =
      (after.transformExistingSourceMixin fieldMixin transform).isSome := by
  have success := congrArg Option.isSome replaced
  simp only [Option.isSome_some] at success
  obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
      ownerPresent, selectorPresent, mixinPresent, definitionPresent,
      oldIdentity, newOwner, selectorAvailable⟩ :=
    (replaceSourceMethodDefinition_isSome_eq_true_iff before methodMixin
      method definition locals body).mp success
  simp [IdentifiedSourceImage.replaceSourceMethodDefinition, identity,
    ownerPresent, selectorPresent, mixinPresent, definitionPresent,
    oldIdentity, newOwner, selectorAvailable, guard] at replaced
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [transformExistingSourceMixin_isSome_eq_true_iff,
    transformExistingSourceMixin_isSome_eq_true_iff]
  by_cases same : methodMixin = fieldMixin
  · subst fieldMixin
    simp [mixinPresent]
  · simp [same, Ne.symm same]

theorem addSourceMethodDefinition_applicability_preserved_by_mixinTransform
    {before after : IdentifiedSourceImage} (methodMixin fieldMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (transform : MixinDef → MixinDef)
    (preservesDeclaration : ∀ mixin,
      (transform mixin).declaration = mixin.declaration)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (transformed : before.transformExistingSourceMixin fieldMixin transform =
      some after) :
    (before.addSourceMethodDefinition methodMixin definition locals body).isSome =
      (after.addSourceMethodDefinition methodMixin definition locals body).isSome := by
  have success := congrArg Option.isSome transformed
  simp only [Option.isSome_some] at success
  obtain ⟨fieldDefinition, fieldPresent⟩ :=
    (transformExistingSourceMixin_isSome_eq_true_iff before fieldMixin
      transform).mp success
  simp [IdentifiedSourceImage.transformExistingSourceMixin, fieldPresent] at transformed
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [addSourceMethodDefinition_isSome_eq_true_iff,
    addSourceMethodDefinition_isSome_eq_true_iff]
  by_cases same : fieldMixin = methodMixin
  · subst fieldMixin
    simp [fieldPresent, preservesDeclaration, preservesMethods]
  · simp [fieldPresent, same, Ne.symm same]

theorem transformExistingSourceMixin_applicability_preserved_by_add
    {before after : IdentifiedSourceImage} (methodMixin fieldMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (transform : MixinDef → MixinDef)
    (added : before.addSourceMethodDefinition methodMixin definition locals
      body = some after) :
    (before.transformExistingSourceMixin fieldMixin transform).isSome =
      (after.transformExistingSourceMixin fieldMixin transform).isSome := by
  have success := congrArg Option.isSome added
  simp only [Option.isSome_some] at success
  obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
      mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
    (addSourceMethodDefinition_isSome_eq_true_iff before methodMixin
      definition locals body).mp success
  simp [IdentifiedSourceImage.addSourceMethodDefinition, methodFresh,
    selectorFresh, bodyFresh, localsFresh, mixinPresent, dictionaryFresh,
    owner, guard] at added
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [transformExistingSourceMixin_isSome_eq_true_iff,
    transformExistingSourceMixin_isSome_eq_true_iff]
  by_cases same : methodMixin = fieldMixin
  · subst fieldMixin
    simp [mixinPresent]
  · simp [same, Ne.symm same]

theorem removeSourceMethodDefinition_applicability_preserved_by_mixinTransform
    {before after : IdentifiedSourceImage} (methodMixin fieldMixin : MixinId)
    (method : MethodId) (transform : MixinDef → MixinDef)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (transformed : before.transformExistingSourceMixin fieldMixin transform =
      some after) :
    (before.removeSourceMethodDefinition methodMixin method).isSome =
      (after.removeSourceMethodDefinition methodMixin method).isSome := by
  have success := congrArg Option.isSome transformed
  simp only [Option.isSome_some] at success
  obtain ⟨fieldDefinition, fieldPresent⟩ :=
    (transformExistingSourceMixin_isSome_eq_true_iff before fieldMixin
      transform).mp success
  simp [IdentifiedSourceImage.transformExistingSourceMixin, fieldPresent] at transformed
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [removeSourceMethodDefinition_isSome_eq_true_iff,
    removeSourceMethodDefinition_isSome_eq_true_iff]
  by_cases same : fieldMixin = methodMixin
  · subst fieldMixin
    simp [fieldPresent, preservesMethods]
  · simp [fieldPresent, same, Ne.symm same]

theorem transformExistingSourceMixin_applicability_preserved_by_remove
    {before after : IdentifiedSourceImage} (methodMixin fieldMixin : MixinId)
    (method : MethodId) (transform : MixinDef → MixinDef)
    (removed : before.removeSourceMethodDefinition methodMixin method =
      some after) :
    (before.transformExistingSourceMixin fieldMixin transform).isSome =
      (after.transformExistingSourceMixin fieldMixin transform).isSome := by
  have success := congrArg Option.isSome removed
  simp only [Option.isSome_some] at success
  obtain ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
      selectorPresent, mixinPresent, definitionPresent, identity⟩ :=
    removeSourceMethodDefinition_success_witnesses before methodMixin method
      success
  simp [IdentifiedSourceImage.removeSourceMethodDefinition, ownerPresent,
    selectorPresent, mixinPresent, definitionPresent, identity, guard] at removed
  subst after
  apply Bool.eq_iff_iff.mpr
  rw [transformExistingSourceMixin_isSome_eq_true_iff,
    transformExistingSourceMixin_isSome_eq_true_iff]
  by_cases same : methodMixin = fieldMixin
  · subst fieldMixin
    simp [mixinPresent]
  · simp [same, Ne.symm same]

theorem replaceSourceMethodBody_applicability_preserved_by_remove
    {before after : IdentifiedSourceImage} {bodyMethod removedMethod : MethodId}
    (different : bodyMethod ≠ removedMethod) (body : List Statement)
    (removedMixin : MixinId)
    (removed : before.removeSourceMethodDefinition removedMixin removedMethod =
      some after) :
    (before.replaceSourceMethodBody bodyMethod body).isSome =
      (after.replaceSourceMethodBody bodyMethod body).isSome := by
  have success :
      (before.removeSourceMethodDefinition removedMixin removedMethod).isSome =
        true := by
    simp [removed]
  obtain ⟨selector, mixinDefinition, methodDefinition,
      ownerPresent, selectorPresent, mixinPresent, definitionPresent,
      identity⟩ :=
    removeSourceMethodDefinition_success_witnesses before removedMixin
      removedMethod success
  simp [IdentifiedSourceImage.removeSourceMethodDefinition, ownerPresent,
    selectorPresent, mixinPresent, definitionPresent, identity, guard] at removed
  subst after
  cases owner : before.methodMixins bodyMethod with
  | none =>
      simp [IdentifiedSourceImage.replaceSourceMethodBody, owner, different]
  | some bodyOwner =>
      cases oldBody : before.methodBodies bodyMethod with
      | none =>
          simp [IdentifiedSourceImage.replaceSourceMethodBody, owner, oldBody,
            different]
      | some previousBody =>
          simp [IdentifiedSourceImage.replaceSourceMethodBody, owner, oldBody,
            different]

theorem removeSourceMethodDefinition_applicability_preserved_by_body
    {before after : IdentifiedSourceImage} (bodyMethod : MethodId)
    (body : List Statement) (removedMixin : MixinId)
    (removedMethod : MethodId)
    (replaced : before.replaceSourceMethodBody bodyMethod body = some after) :
    (before.removeSourceMethodDefinition removedMixin removedMethod).isSome =
      (after.removeSourceMethodDefinition removedMixin removedMethod).isSome := by
  have success : (before.replaceSourceMethodBody bodyMethod body).isSome =
      true := by
    simp [replaced]
  obtain ⟨owner, oldBody, ownerPresent, bodyPresent⟩ :=
    replaceSourceMethodBody_success_witnesses before bodyMethod body success
  simp [IdentifiedSourceImage.replaceSourceMethodBody, ownerPresent,
    bodyPresent] at replaced
  subst after
  cases removedOwnerPresent : before.methodMixins removedMethod with
  | none =>
      simp [IdentifiedSourceImage.removeSourceMethodDefinition,
        removedOwnerPresent]
  | some removedOwner =>
      by_cases ownerEqual : removedOwner = removedMixin
      · subst removedOwner
        cases selectorPresent : before.methodSelectors removedMethod with
        | none =>
            simp [IdentifiedSourceImage.removeSourceMethodDefinition,
              removedOwnerPresent, selectorPresent]
        | some selector =>
            cases mixinPresent : before.mixins removedMixin with
            | none =>
                simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                  removedOwnerPresent, selectorPresent, mixinPresent]
            | some mixinDefinition =>
                cases definitionPresent : mixinDefinition.methods selector with
                | none =>
                    simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                      removedOwnerPresent, selectorPresent, mixinPresent,
                      definitionPresent]
                | some methodDefinition =>
                    by_cases identity : methodDefinition.identity = removedMethod
                    · simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                        removedOwnerPresent, selectorPresent, mixinPresent,
                        definitionPresent, identity, guard]
                    · simp [IdentifiedSourceImage.removeSourceMethodDefinition,
                        removedOwnerPresent, selectorPresent, mixinPresent,
                        definitionPresent, identity, guard,
                        Alternative.failure, Option.bind]
      · simp [IdentifiedSourceImage.removeSourceMethodDefinition,
          removedOwnerPresent, ownerEqual, guard, Alternative.failure,
          Option.bind]

theorem replaceMethodBodyAndRemoveMethodDefinitionCommands_commute
    {bodyMirror removeMirror : MirrorId} {bodyMethod removedMethod : MethodId}
    (body : List Statement) (removedMixin : MixinId)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodBody bodyMirror bodyMethod body)
      (.removeMethodDefinition removeMirror removedMixin removedMethod)) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody bodyMirror bodyMethod body)
      (.removeMethodDefinition removeMirror removedMixin removedMethod) := by
  have different : bodyMethod ≠ removedMethod := by
    intro equal
    subst removedMethod
    exact compatible (.methodBody bodyMethod)
      (by simp [ReflectionCommand.writes]) (.methodBody bodyMethod)
      (by simp [ReflectionCommand.writes]) (.same (.methodBody bodyMethod))
  apply OptionalCommandsCommute.of_success_and_applicability
  · intro before after removed
    exact replaceSourceMethodBody_applicability_preserved_by_remove different
      body removedMixin (by
        simpa [IdentifiedSourceImage.patchSourceCodeCommand] using removed)
  · intro before after replaced
    exact removeSourceMethodDefinition_applicability_preserved_by_body
      bodyMethod body removedMixin removedMethod (by
        simpa [IdentifiedSourceImage.patchSourceCodeCommand] using replaced)
  · intro source bodySuccess removeSuccess
    obtain ⟨bodyOwner, oldBody, bodyOwnerPresent, bodyPresent⟩ :=
      replaceSourceMethodBody_success_witnesses source bodyMethod body
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using bodySuccess)
    obtain ⟨selector, mixinDefinition, methodDefinition,
        removedOwnerPresent, removedSelectorPresent, mixinPresent,
        definitionPresent, identity⟩ :=
      removeSourceMethodDefinition_success_witnesses source removedMixin
        removedMethod
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          removeSuccess)
    simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
      source.replaceSourceMethodBody_and_removeSourceMethodDefinition_commute
        different body removedMixin bodyOwnerPresent bodyPresent
        removedOwnerPresent removedSelectorPresent mixinPresent
        definitionPresent identity

theorem replaceMethodBodyAndAddMethodDefinitionCommands_commuteModulo
    {bodyMirror addMirror : MirrorId} {bodyMethod : MethodId}
    (body : List Statement) (addedMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (addedBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodBody bodyMirror bodyMethod body)
      (.addMethodDefinition addMirror addedMixin definition locals
        addedBody)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody bodyMirror bodyMethod body)
      (.addMethodDefinition addMirror addedMixin definition locals
        addedBody) := by
  have different : bodyMethod ≠ definition.identity := by
    intro equal
    subst bodyMethod
    exact compatible (.methodBody definition.identity)
      (by simp [ReflectionCommand.writes]) (.methodBody definition.identity)
      (by simp [ReflectionCommand.writes])
      (.same (.methodBody definition.identity))
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after added
    exact replaceSourceMethodBody_applicability_preserved_by_add body
      addedMixin definition locals addedBody different
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using added)
  · intro before after replaced
    exact addSourceMethodDefinition_applicability_preserved_by_body bodyMethod
      body addedMixin definition locals addedBody different
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using replaced)
  · intro source bodySuccess addSuccess
    obtain ⟨bodyOwner, oldBody, bodyOwnerPresent, bodyPresent⟩ :=
      replaceSourceMethodBody_success_witnesses source bodyMethod body
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          bodySuccess)
    obtain ⟨methodFresh, selectorFresh, addedBodyFresh, localsFresh,
        mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
      (addSourceMethodDefinition_isSome_eq_true_iff source addedMixin
        definition locals addedBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          addSuccess)
    simp [IdentifiedSourceImage.patchSourceCodeCommand,
      IdentifiedSourceImage.replaceSourceMethodBody,
      IdentifiedSourceImage.addSourceMethodDefinition, bodyOwnerPresent,
      bodyPresent, methodFresh, selectorFresh, addedBodyFresh, localsFresh,
      mixinPresent, dictionaryFresh, owner, guard, different,
      different.symm]
    exact .bothSucceeded
      { mixins := FiniteStore.LookupEquivalent.refl _
        methodBodies :=
          source.methodBodies.install_distinct_commute_lookup different
            body addedBody
        methodLocals := FiniteStore.LookupEquivalent.refl _
        methodMixins := FiniteStore.LookupEquivalent.refl _
        methodSelectors := FiniteStore.LookupEquivalent.refl _ }

theorem replaceMethodBodyAndReplaceMethodDefinitionCommands_commuteModulo
    {bodyMirror replaceMirror : MirrorId} {bodyMethod replacedMethod : MethodId}
    (body : List Statement) (replacedMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (replacementBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodBody bodyMirror bodyMethod body)
      (.replaceMethodDefinition replaceMirror replacedMixin replacedMethod
        definition locals replacementBody)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodBody bodyMirror bodyMethod body)
      (.replaceMethodDefinition replaceMirror replacedMixin replacedMethod
        definition locals replacementBody) := by
  have different : bodyMethod ≠ replacedMethod := by
    intro equal
    subst bodyMethod
    exact compatible (.methodBody replacedMethod)
      (by simp [ReflectionCommand.writes]) (.methodBody replacedMethod)
      (by simp [ReflectionCommand.writes]) (.same (.methodBody replacedMethod))
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after replaced
    exact
      replaceSourceMethodBody_applicability_preserved_by_definitionReplacement
        body replacedMixin definition locals replacementBody different
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using replaced)
  · intro before after bodyReplaced
    exact replaceSourceMethodDefinition_applicability_preserved_by_body
      bodyMethod body replacedMixin replacedMethod definition locals
      replacementBody
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
        bodyReplaced)
  · intro source bodySuccess replacementSuccess
    obtain ⟨bodyOwner, oldBody, bodyOwnerPresent, bodyPresent⟩ :=
      replaceSourceMethodBody_success_witnesses source bodyMethod body
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          bodySuccess)
    obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
        ownerPresent, selectorPresent, mixinPresent, definitionPresent,
        oldIdentity, newOwner, selectorAvailable⟩ :=
      (replaceSourceMethodDefinition_isSome_eq_true_iff source replacedMixin
        replacedMethod definition locals replacementBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          replacementSuccess)
    simp [IdentifiedSourceImage.patchSourceCodeCommand,
      IdentifiedSourceImage.replaceSourceMethodBody,
      IdentifiedSourceImage.replaceSourceMethodDefinition, bodyOwnerPresent,
      bodyPresent, identity, ownerPresent, selectorPresent, mixinPresent,
      definitionPresent, oldIdentity, newOwner, selectorAvailable, guard,
      different, different.symm]
    exact .bothSucceeded
      { mixins := FiniteStore.LookupEquivalent.refl _
        methodBodies :=
          source.methodBodies.install_distinct_commute_lookup different body
            replacementBody
        methodLocals := FiniteStore.LookupEquivalent.refl _
        methodMixins := FiniteStore.LookupEquivalent.refl _
        methodSelectors := FiniteStore.LookupEquivalent.refl _ }

theorem compatibleAddMethodDefinitionCommands_commuteModulo
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId}
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.addMethodDefinition firstMirror firstMixin firstDefinition firstLocals
        firstBody)
      (.addMethodDefinition secondMirror secondMixin secondDefinition
        secondLocals secondBody)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.addMethodDefinition firstMirror firstMixin firstDefinition firstLocals
        firstBody)
      (.addMethodDefinition secondMirror secondMixin secondDefinition
        secondLocals secondBody) := by
  obtain ⟨mixinsDifferent, methodsDifferent⟩ :=
    compatibleAddMethodCommands_have_distinct_targets compatible
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after secondAdded
    exact addSourceMethodDefinition_applicability_preserved_by_add
      secondDefinition firstDefinition secondLocals firstLocals secondBody
      firstBody mixinsDifferent.symm methodsDifferent.symm
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
        secondAdded)
  · intro before after firstAdded
    exact addSourceMethodDefinition_applicability_preserved_by_add
      firstDefinition secondDefinition firstLocals secondLocals firstBody
      secondBody mixinsDifferent methodsDifferent
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
        firstAdded)
  · intro source firstSuccess secondSuccess
    obtain ⟨firstMethodFresh, firstSelectorFresh, firstBodyFresh,
        firstLocalsFresh, firstMixinDefinition, firstMixinPresent,
        firstDictionaryFresh, firstOwner⟩ :=
      (addSourceMethodDefinition_isSome_eq_true_iff source firstMixin
        firstDefinition firstLocals firstBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          firstSuccess)
    obtain ⟨secondMethodFresh, secondSelectorFresh, secondBodyFresh,
        secondLocalsFresh, secondMixinDefinition, secondMixinPresent,
        secondDictionaryFresh, secondOwner⟩ :=
      (addSourceMethodDefinition_isSome_eq_true_iff source secondMixin
        secondDefinition secondLocals secondBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          secondSuccess)
    exact addMethodDefinitionCommands_commuteExtensionallyAt source
      firstDefinition secondDefinition firstLocals secondLocals firstBody
      secondBody compatible firstMixinPresent secondMixinPresent
      firstMethodFresh secondMethodFresh firstSelectorFresh
      secondSelectorFresh firstBodyFresh secondBodyFresh firstLocalsFresh
      secondLocalsFresh firstDictionaryFresh secondDictionaryFresh firstOwner
      secondOwner

theorem compatibleReplaceMethodDefinitionCommands_commuteModulo
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    (firstDefinition secondDefinition : MethodDef)
    (firstLocals secondLocals : List LocalDeclarationGroup)
    (firstBody secondBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodDefinition firstMirror firstMixin firstMethod
        firstDefinition firstLocals firstBody)
      (.replaceMethodDefinition secondMirror secondMixin secondMethod
        secondDefinition secondLocals secondBody)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition firstMirror firstMixin firstMethod
        firstDefinition firstLocals firstBody)
      (.replaceMethodDefinition secondMirror secondMixin secondMethod
        secondDefinition secondLocals secondBody) := by
  obtain ⟨mixinsDifferent, methodsDifferent⟩ :=
    compatibleReplaceMethodDefinitionCommands_have_distinct_targets compatible
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after secondReplaced
    exact
      replaceSourceMethodDefinition_applicability_preserved_by_replacement
        secondDefinition firstDefinition secondLocals firstLocals secondBody
        firstBody mixinsDifferent.symm methodsDifferent.symm
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          secondReplaced)
  · intro before after firstReplaced
    exact
      replaceSourceMethodDefinition_applicability_preserved_by_replacement
        firstDefinition secondDefinition firstLocals secondLocals firstBody
        secondBody mixinsDifferent methodsDifferent
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          firstReplaced)
  · intro source firstSuccess secondSuccess
    obtain ⟨firstIdentity, firstOldSelector, firstMixinDefinition,
        firstOldDefinition, firstOwnerPresent, firstSelectorPresent,
        firstMixinPresent, firstOldPresent, firstOldIdentity, firstNewOwner,
        firstSelectorAvailable⟩ :=
      (replaceSourceMethodDefinition_isSome_eq_true_iff source firstMixin
        firstMethod firstDefinition firstLocals firstBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          firstSuccess)
    obtain ⟨secondIdentity, secondOldSelector, secondMixinDefinition,
        secondOldDefinition, secondOwnerPresent, secondSelectorPresent,
        secondMixinPresent, secondOldPresent, secondOldIdentity,
        secondNewOwner, secondSelectorAvailable⟩ :=
      (replaceSourceMethodDefinition_isSome_eq_true_iff source secondMixin
        secondMethod secondDefinition secondLocals secondBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          secondSuccess)
    simp [IdentifiedSourceImage.patchSourceCodeCommand,
      IdentifiedSourceImage.replaceSourceMethodDefinition, firstIdentity,
      secondIdentity, firstOwnerPresent, secondOwnerPresent,
      firstSelectorPresent, secondSelectorPresent, firstMixinPresent,
      secondMixinPresent, firstOldPresent, secondOldPresent,
      firstOldIdentity, secondOldIdentity, firstNewOwner, secondNewOwner,
      firstSelectorAvailable, secondSelectorAvailable, guard,
      mixinsDifferent, mixinsDifferent.symm, methodsDifferent,
      methodsDifferent.symm]
    exact .bothSucceeded
      { mixins := source.mixins.install_distinct_commute_lookup
          mixinsDifferent _ _
        methodBodies := source.methodBodies.install_distinct_commute_lookup
          methodsDifferent firstBody secondBody
        methodLocals := source.methodLocals.install_distinct_commute_lookup
          methodsDifferent firstLocals secondLocals
        methodMixins := FiniteStore.LookupEquivalent.refl _
        methodSelectors :=
          source.methodSelectors.install_distinct_commute_lookup
            methodsDifferent firstDefinition.selector secondDefinition.selector }

theorem addAndRemoveMethodDefinitionCommands_commuteModulo
    {addMirror removeMirror : MirrorId} {addedMixin removedMixin : MixinId}
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (addedBody : List Statement) (removedMethod : MethodId)
    (compatible : ReflectionCommandsCompatible
      (.addMethodDefinition addMirror addedMixin definition locals addedBody)
      (.removeMethodDefinition removeMirror removedMixin removedMethod)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.addMethodDefinition addMirror addedMixin definition locals addedBody)
      (.removeMethodDefinition removeMirror removedMixin removedMethod) := by
  have mixinsDifferent : addedMixin ≠ removedMixin := by
    intro equal
    subst removedMixin
    exact compatible (.methodDictionary addedMixin)
      (by simp [ReflectionCommand.writes]) (.methodDictionary addedMixin)
      (by simp [ReflectionCommand.writes])
      (.same (.methodDictionary addedMixin))
  have methodsDifferent : definition.identity ≠ removedMethod := by
    intro equal
    subst removedMethod
    exact compatible (.methodDefinition definition.identity)
      (by simp [ReflectionCommand.writes])
      (.methodDefinition definition.identity)
      (by simp [ReflectionCommand.writes])
      (.same (.methodDefinition definition.identity))
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after removed
    exact addSourceMethodDefinition_applicability_preserved_by_remove
      removedMethod definition locals addedBody mixinsDifferent.symm
      methodsDifferent.symm
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using removed)
  · intro before after added
    exact removeSourceMethodDefinition_applicability_preserved_by_add
      definition locals addedBody removedMethod mixinsDifferent
      methodsDifferent
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using added)
  · intro source addSuccess removeSuccess
    obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
        addedMixinDefinition, addedMixinPresent, dictionaryFresh, owner⟩ :=
      (addSourceMethodDefinition_isSome_eq_true_iff source addedMixin
        definition locals addedBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          addSuccess)
    obtain ⟨removedSelector, removedMixinDefinition,
        removedMethodDefinition, removedOwnerPresent,
        removedSelectorPresent, removedMixinPresent,
        removedDefinitionPresent, removedIdentity⟩ :=
      removeSourceMethodDefinition_success_witnesses source removedMixin
        removedMethod
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          removeSuccess)
    simp [IdentifiedSourceImage.patchSourceCodeCommand,
      IdentifiedSourceImage.addSourceMethodDefinition,
      IdentifiedSourceImage.removeSourceMethodDefinition, methodFresh,
      selectorFresh, bodyFresh, localsFresh, addedMixinPresent,
      dictionaryFresh, owner, removedOwnerPresent, removedSelectorPresent,
      removedMixinPresent, removedDefinitionPresent, removedIdentity, guard,
      mixinsDifferent, mixinsDifferent.symm, methodsDifferent,
      methodsDifferent.symm]
    exact .bothSucceeded
      { mixins := source.mixins.install_distinct_commute_lookup
          mixinsDifferent _ _
        methodBodies :=
          source.methodBodies.install_erase_distinct_commute_lookup
            methodsDifferent addedBody
        methodLocals :=
          source.methodLocals.install_erase_distinct_commute_lookup
            methodsDifferent locals
        methodMixins :=
          source.methodMixins.install_erase_distinct_commute_lookup
            methodsDifferent addedMixin
        methodSelectors :=
          source.methodSelectors.install_erase_distinct_commute_lookup
            methodsDifferent definition.selector }

theorem replaceAndRemoveMethodDefinitionCommands_commuteModulo
    {replaceMirror removeMirror : MirrorId}
    {replacedMixin removedMixin : MixinId}
    {replacedMethod removedMethod : MethodId}
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (replacementBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodDefinition replaceMirror replacedMixin replacedMethod
        definition locals replacementBody)
      (.removeMethodDefinition removeMirror removedMixin removedMethod)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition replaceMirror replacedMixin replacedMethod
        definition locals replacementBody)
      (.removeMethodDefinition removeMirror removedMixin removedMethod) := by
  have mixinsDifferent : replacedMixin ≠ removedMixin := by
    intro equal
    subst removedMixin
    exact compatible (.methodDictionary replacedMixin)
      (by simp [ReflectionCommand.writes]) (.methodDictionary replacedMixin)
      (by simp [ReflectionCommand.writes])
      (.same (.methodDictionary replacedMixin))
  have methodsDifferent : replacedMethod ≠ removedMethod := by
    intro equal
    subst removedMethod
    exact compatible (.methodDefinition replacedMethod)
      (by simp [ReflectionCommand.writes]) (.methodDefinition replacedMethod)
      (by simp [ReflectionCommand.writes])
      (.same (.methodDefinition replacedMethod))
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after removed
    exact replaceSourceMethodDefinition_applicability_preserved_by_remove
      definition locals replacementBody mixinsDifferent.symm
      methodsDifferent.symm
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using removed)
  · intro before after replaced
    exact removeSourceMethodDefinition_applicability_preserved_by_replacement
      definition locals replacementBody mixinsDifferent methodsDifferent
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using replaced)
  · intro source replacementSuccess removeSuccess
    obtain ⟨replacementIdentity, oldSelector, replacedMixinDefinition,
        oldDefinition, replacedOwnerPresent, replacedSelectorPresent,
        replacedMixinPresent, oldDefinitionPresent, oldIdentity, newOwner,
        selectorAvailable⟩ :=
      (replaceSourceMethodDefinition_isSome_eq_true_iff source replacedMixin
        replacedMethod definition locals replacementBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          replacementSuccess)
    obtain ⟨removedSelector, removedMixinDefinition,
        removedMethodDefinition, removedOwnerPresent,
        removedSelectorPresent, removedMixinPresent,
        removedDefinitionPresent, removedIdentity⟩ :=
      removeSourceMethodDefinition_success_witnesses source removedMixin
        removedMethod
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          removeSuccess)
    simp [IdentifiedSourceImage.patchSourceCodeCommand,
      IdentifiedSourceImage.replaceSourceMethodDefinition,
      IdentifiedSourceImage.removeSourceMethodDefinition, replacementIdentity,
      replacedOwnerPresent, replacedSelectorPresent, replacedMixinPresent,
      oldDefinitionPresent, oldIdentity, newOwner, selectorAvailable,
      removedOwnerPresent, removedSelectorPresent, removedMixinPresent,
      removedDefinitionPresent, removedIdentity, guard, mixinsDifferent,
      mixinsDifferent.symm, methodsDifferent, methodsDifferent.symm]
    exact .bothSucceeded
      { mixins := source.mixins.install_distinct_commute_lookup
          mixinsDifferent _ _
        methodBodies :=
          source.methodBodies.install_erase_distinct_commute_lookup
            methodsDifferent replacementBody
        methodLocals :=
          source.methodLocals.install_erase_distinct_commute_lookup
            methodsDifferent locals
        methodMixins := FiniteStore.LookupEquivalent.refl _
        methodSelectors :=
          source.methodSelectors.install_erase_distinct_commute_lookup
            methodsDifferent definition.selector }

theorem replaceAndAddMethodDefinitionCommands_commuteModulo
    {replaceMirror addMirror : MirrorId}
    {replacedMixin addedMixin : MixinId} {replacedMethod : MethodId}
    (replacementDefinition addedDefinition : MethodDef)
    (replacementLocals addedLocals : List LocalDeclarationGroup)
    (replacementBody addedBody : List Statement)
    (compatible : ReflectionCommandsCompatible
      (.replaceMethodDefinition replaceMirror replacedMixin replacedMethod
        replacementDefinition replacementLocals replacementBody)
      (.addMethodDefinition addMirror addedMixin addedDefinition addedLocals
        addedBody)) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition replaceMirror replacedMixin replacedMethod
        replacementDefinition replacementLocals replacementBody)
      (.addMethodDefinition addMirror addedMixin addedDefinition addedLocals
        addedBody) := by
  have mixinsDifferent : replacedMixin ≠ addedMixin := by
    intro equal
    subst addedMixin
    exact compatible (.methodDictionary replacedMixin)
      (by simp [ReflectionCommand.writes]) (.methodDictionary replacedMixin)
      (by simp [ReflectionCommand.writes])
      (.same (.methodDictionary replacedMixin))
  have methodsDifferent : replacedMethod ≠ addedDefinition.identity := by
    intro equal
    subst replacedMethod
    exact compatible (.methodDefinition addedDefinition.identity)
      (by simp [ReflectionCommand.writes])
      (.methodDefinition addedDefinition.identity)
      (by simp [ReflectionCommand.writes])
      (.same (.methodDefinition addedDefinition.identity))
  apply OptionalCommandsCommuteModulo.of_success_and_applicability
  · intro before after added
    exact replaceSourceMethodDefinition_applicability_preserved_by_add
      addedDefinition replacementDefinition addedLocals replacementLocals
      addedBody replacementBody mixinsDifferent.symm methodsDifferent.symm
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using added)
  · intro before after replaced
    exact addSourceMethodDefinition_applicability_preserved_by_replacement
      replacementDefinition addedDefinition replacementLocals addedLocals
      replacementBody addedBody mixinsDifferent methodsDifferent
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using replaced)
  · intro source replacementSuccess addSuccess
    obtain ⟨replacementIdentity, oldSelector, replacedMixinDefinition,
        oldDefinition, replacedOwnerPresent, replacedSelectorPresent,
        replacedMixinPresent, oldDefinitionPresent, oldIdentity, newOwner,
        selectorAvailable⟩ :=
      (replaceSourceMethodDefinition_isSome_eq_true_iff source replacedMixin
        replacedMethod replacementDefinition replacementLocals
        replacementBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          replacementSuccess)
    obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
        addedMixinDefinition, addedMixinPresent, dictionaryFresh, addedOwner⟩ :=
      (addSourceMethodDefinition_isSome_eq_true_iff source addedMixin
        addedDefinition addedLocals addedBody).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          addSuccess)
    simp [IdentifiedSourceImage.patchSourceCodeCommand,
      IdentifiedSourceImage.replaceSourceMethodDefinition,
      IdentifiedSourceImage.addSourceMethodDefinition, replacementIdentity,
      replacedOwnerPresent, replacedSelectorPresent, replacedMixinPresent,
      oldDefinitionPresent, oldIdentity, newOwner, selectorAvailable,
      methodFresh, selectorFresh, bodyFresh, localsFresh, addedMixinPresent,
      dictionaryFresh, addedOwner, guard, mixinsDifferent,
      mixinsDifferent.symm, methodsDifferent, methodsDifferent.symm]
    exact .bothSucceeded
      { mixins := source.mixins.install_distinct_commute_lookup
          mixinsDifferent _ _
        methodBodies := source.methodBodies.install_distinct_commute_lookup
          methodsDifferent replacementBody addedBody
        methodLocals := source.methodLocals.install_distinct_commute_lookup
          methodsDifferent replacementLocals addedLocals
        methodMixins := FiniteStore.LookupEquivalent.refl _
        methodSelectors :=
          source.methodSelectors.install_distinct_commute_lookup
            methodsDifferent replacementDefinition.selector
            addedDefinition.selector }

theorem replaceMethodDefinitionAndMixinTransformCommand_commute
    {replaceMirror : MirrorId} (methodMixin : MixinId) (method : MethodId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (fieldCommand : ReflectionCommand)
    (fieldMixin : MixinId) (transform : MixinDef → MixinDef)
    (fieldEquation : ∀ (source : IdentifiedSourceImage),
      source.patchSourceCodeCommand fieldCommand =
        source.transformExistingSourceMixin fieldMixin transform)
    (preservesDeclaration : ∀ mixin,
      (transform mixin).declaration = mixin.declaration)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (commutesWithMethods : ∀ mixin methods,
      transform { mixin with methods := methods } =
        { transform mixin with methods := methods }) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition replaceMirror methodMixin method definition
        locals body)
      fieldCommand := by
  apply OptionalCommandsCommute.of_success_and_applicability
  · intro before after transformed
    exact
      replaceSourceMethodDefinition_applicability_preserved_by_mixinTransform
        methodMixin fieldMixin method definition locals body transform
        preservesDeclaration preservesMethods
        (by simpa only [fieldEquation before] using transformed)
  · intro before after replaced
    rw [fieldEquation before, fieldEquation after]
    exact transformExistingSourceMixin_applicability_preserved_by_replacement
      methodMixin fieldMixin method definition locals body transform
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using replaced)
  · intro source replacementSuccess fieldSuccess
    obtain ⟨identity, oldSelector, mixinDefinition, oldDefinition,
        ownerPresent, selectorPresent, mixinPresent, definitionPresent,
        oldIdentity, newOwner, selectorAvailable⟩ :=
      (replaceSourceMethodDefinition_isSome_eq_true_iff source methodMixin
        method definition locals body).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          replacementSuccess)
    have transformedSuccess :
        (source.transformExistingSourceMixin fieldMixin transform).isSome =
          true := by simpa only [fieldEquation source] using fieldSuccess
    obtain ⟨fieldDefinition, fieldPresent⟩ :=
      (transformExistingSourceMixin_isSome_eq_true_iff source fieldMixin
        transform).mp transformedSuccess
    have fieldFunction :
        (fun current : IdentifiedSourceImage =>
          current.patchSourceCodeCommand fieldCommand) =
        (fun current =>
          current.transformExistingSourceMixin fieldMixin transform) := by
      funext current
      exact fieldEquation current
    rw [fieldFunction]
    rw [fieldEquation source]
    simpa only [IdentifiedSourceImage.patchSourceCodeCommand] using
      source.replaceSourceMethodDefinition_and_mixinTransform_commute
        methodMixin fieldMixin method definition locals body transform
        preservesDeclaration preservesMethods commutesWithMethods identity
        ownerPresent selectorPresent mixinPresent definitionPresent
        oldIdentity newOwner selectorAvailable fieldPresent

theorem replaceMethodDefinitionAndSlotDeclarationsCommands_commute
    {replaceMirror slotMirror : MirrorId} (methodMixin : MixinId)
    (method : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement)
    (fieldMixin : MixinId) (groups : List SlotDeclarationGroup) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition replaceMirror methodMixin method definition
        locals body)
      (.replaceSlotDeclarations slotMirror fieldMixin groups) := by
  exact replaceMethodDefinitionAndMixinTransformCommand_commute methodMixin
    method definition locals body
    (.replaceSlotDeclarations slotMirror fieldMixin groups) fieldMixin
    (IdentifiedSourceImage.sourceSlotDeclarationTransform groups)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem replaceMethodDefinitionAndNestedDeclarationsCommands_commute
    {replaceMirror nestedMirror : MirrorId} (methodMixin : MixinId)
    (method : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement)
    (fieldMixin : MixinId) (declarations : List ClassDeclId) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition replaceMirror methodMixin method definition
        locals body)
      (.replaceNestedDeclarations nestedMirror fieldMixin declarations) := by
  exact replaceMethodDefinitionAndMixinTransformCommand_commute methodMixin
    method definition locals body
    (.replaceNestedDeclarations nestedMirror fieldMixin declarations)
    fieldMixin
    (IdentifiedSourceImage.sourceNestedDeclarationTransform declarations)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem replaceMethodDefinitionAndMixinInitializerCommands_commute
    {replaceMirror initializerMirror : MirrorId} (methodMixin : MixinId)
    (method : MethodId) (definition : MethodDef)
    (locals : List LocalDeclarationGroup) (body : List Statement)
    (fieldMixin : MixinId) (initializer : MixinInitializerReplacement) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.replaceMethodDefinition replaceMirror methodMixin method definition
        locals body)
      (.replaceMixinInitializer initializerMirror fieldMixin initializer) := by
  exact replaceMethodDefinitionAndMixinTransformCommand_commute methodMixin
    method definition locals body
    (.replaceMixinInitializer initializerMirror fieldMixin initializer)
    fieldMixin
    (IdentifiedSourceImage.sourceMixinInitializerTransform initializer)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem addMethodDefinitionAndMixinTransformCommand_commute
    {addMirror : MirrorId} (methodMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (fieldCommand : ReflectionCommand)
    (fieldMixin : MixinId) (transform : MixinDef → MixinDef)
    (fieldEquation : ∀ (source : IdentifiedSourceImage),
      source.patchSourceCodeCommand fieldCommand =
        source.transformExistingSourceMixin fieldMixin transform)
    (preservesDeclaration : ∀ mixin,
      (transform mixin).declaration = mixin.declaration)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (commutesWithMethods : ∀ mixin methods,
      transform { mixin with methods := methods } =
        { transform mixin with methods := methods }) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.addMethodDefinition addMirror methodMixin definition locals body)
      fieldCommand := by
  apply OptionalCommandsCommute.of_success_and_applicability
  · intro before after transformed
    exact addSourceMethodDefinition_applicability_preserved_by_mixinTransform
      methodMixin fieldMixin definition locals body transform
      preservesDeclaration preservesMethods
      (by simpa only [fieldEquation before] using transformed)
  · intro before after added
    rw [fieldEquation before, fieldEquation after]
    exact transformExistingSourceMixin_applicability_preserved_by_add
      methodMixin fieldMixin definition locals body transform
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using added)
  · intro source addSuccess fieldSuccess
    obtain ⟨methodFresh, selectorFresh, bodyFresh, localsFresh,
        mixinDefinition, mixinPresent, dictionaryFresh, owner⟩ :=
      (addSourceMethodDefinition_isSome_eq_true_iff source methodMixin
        definition locals body).mp
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          addSuccess)
    have transformedSuccess :
        (source.transformExistingSourceMixin fieldMixin transform).isSome =
          true := by simpa only [fieldEquation source] using fieldSuccess
    obtain ⟨fieldDefinition, fieldPresent⟩ :=
      (transformExistingSourceMixin_isSome_eq_true_iff source fieldMixin
        transform).mp transformedSuccess
    have fieldFunction :
        (fun current : IdentifiedSourceImage =>
          current.patchSourceCodeCommand fieldCommand) =
        (fun current =>
          current.transformExistingSourceMixin fieldMixin transform) := by
      funext current
      exact fieldEquation current
    rw [fieldFunction]
    rw [fieldEquation source]
    simpa only [IdentifiedSourceImage.patchSourceCodeCommand] using
      source.addSourceMethodDefinition_and_mixinTransform_commute
        methodMixin fieldMixin definition locals body transform
        preservesDeclaration preservesMethods commutesWithMethods methodFresh
        selectorFresh bodyFresh localsFresh mixinPresent dictionaryFresh owner
        fieldPresent

theorem addMethodDefinitionAndSlotDeclarationsCommands_commute
    {addMirror slotMirror : MirrorId} (methodMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (fieldMixin : MixinId)
    (groups : List SlotDeclarationGroup) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.addMethodDefinition addMirror methodMixin definition locals body)
      (.replaceSlotDeclarations slotMirror fieldMixin groups) := by
  exact addMethodDefinitionAndMixinTransformCommand_commute methodMixin
    definition locals body
    (.replaceSlotDeclarations slotMirror fieldMixin groups) fieldMixin
    (IdentifiedSourceImage.sourceSlotDeclarationTransform groups)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem addMethodDefinitionAndNestedDeclarationsCommands_commute
    {addMirror nestedMirror : MirrorId} (methodMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (fieldMixin : MixinId)
    (declarations : List ClassDeclId) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.addMethodDefinition addMirror methodMixin definition locals body)
      (.replaceNestedDeclarations nestedMirror fieldMixin declarations) := by
  exact addMethodDefinitionAndMixinTransformCommand_commute methodMixin
    definition locals body
    (.replaceNestedDeclarations nestedMirror fieldMixin declarations)
    fieldMixin
    (IdentifiedSourceImage.sourceNestedDeclarationTransform declarations)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem addMethodDefinitionAndMixinInitializerCommands_commute
    {addMirror initializerMirror : MirrorId} (methodMixin : MixinId)
    (definition : MethodDef) (locals : List LocalDeclarationGroup)
    (body : List Statement) (fieldMixin : MixinId)
    (initializer : MixinInitializerReplacement) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.addMethodDefinition addMirror methodMixin definition locals body)
      (.replaceMixinInitializer initializerMirror fieldMixin initializer) := by
  exact addMethodDefinitionAndMixinTransformCommand_commute methodMixin
    definition locals body
    (.replaceMixinInitializer initializerMirror fieldMixin initializer)
    fieldMixin
    (IdentifiedSourceImage.sourceMixinInitializerTransform initializer)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem removeMethodDefinitionAndMixinTransformCommand_commute
    {removeMirror : MirrorId} (methodMixin : MixinId) (method : MethodId)
    (fieldCommand : ReflectionCommand) (fieldMixin : MixinId)
    (transform : MixinDef → MixinDef)
    (fieldEquation : ∀ (source : IdentifiedSourceImage),
      source.patchSourceCodeCommand fieldCommand =
        source.transformExistingSourceMixin fieldMixin transform)
    (preservesMethods : ∀ mixin, (transform mixin).methods = mixin.methods)
    (commutesWithMethods : ∀ mixin methods,
      transform { mixin with methods := methods } =
        { transform mixin with methods := methods }) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.removeMethodDefinition removeMirror methodMixin method)
      fieldCommand := by
  apply OptionalCommandsCommute.of_success_and_applicability
  · intro before after transformed
    exact removeSourceMethodDefinition_applicability_preserved_by_mixinTransform
      methodMixin fieldMixin method transform preservesMethods
      (by simpa only [fieldEquation before] using transformed)
  · intro before after removed
    rw [fieldEquation before, fieldEquation after]
    exact transformExistingSourceMixin_applicability_preserved_by_remove
      methodMixin fieldMixin method transform
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using removed)
  · intro source removeSuccess fieldSuccess
    obtain ⟨selector, mixinDefinition, methodDefinition, ownerPresent,
        selectorPresent, mixinPresent, definitionPresent, identity⟩ :=
      removeSourceMethodDefinition_success_witnesses source methodMixin method
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          removeSuccess)
    have transformedSuccess :
        (source.transformExistingSourceMixin fieldMixin transform).isSome =
          true := by simpa only [fieldEquation source] using fieldSuccess
    obtain ⟨fieldDefinition, fieldPresent⟩ :=
      (transformExistingSourceMixin_isSome_eq_true_iff source fieldMixin
        transform).mp transformedSuccess
    have fieldFunction :
        (fun current : IdentifiedSourceImage =>
          current.patchSourceCodeCommand fieldCommand) =
        (fun current =>
          current.transformExistingSourceMixin fieldMixin transform) := by
      funext current
      exact fieldEquation current
    rw [fieldFunction]
    rw [fieldEquation source]
    simpa only [IdentifiedSourceImage.patchSourceCodeCommand] using
      source.removeSourceMethodDefinition_and_mixinTransform_commute
        methodMixin fieldMixin method transform preservesMethods
        commutesWithMethods ownerPresent selectorPresent mixinPresent
        definitionPresent identity fieldPresent

theorem removeMethodDefinitionAndSlotDeclarationsCommands_commute
    {removeMirror slotMirror : MirrorId} (methodMixin : MixinId)
    (method : MethodId) (fieldMixin : MixinId)
    (groups : List SlotDeclarationGroup) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.removeMethodDefinition removeMirror methodMixin method)
      (.replaceSlotDeclarations slotMirror fieldMixin groups) := by
  exact removeMethodDefinitionAndMixinTransformCommand_commute methodMixin
    method (.replaceSlotDeclarations slotMirror fieldMixin groups) fieldMixin
    (IdentifiedSourceImage.sourceSlotDeclarationTransform groups)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem removeMethodDefinitionAndNestedDeclarationsCommands_commute
    {removeMirror nestedMirror : MirrorId} (methodMixin : MixinId)
    (method : MethodId) (fieldMixin : MixinId)
    (declarations : List ClassDeclId) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.removeMethodDefinition removeMirror methodMixin method)
      (.replaceNestedDeclarations nestedMirror fieldMixin declarations) := by
  exact removeMethodDefinitionAndMixinTransformCommand_commute methodMixin
    method (.replaceNestedDeclarations nestedMirror fieldMixin declarations)
    fieldMixin
    (IdentifiedSourceImage.sourceNestedDeclarationTransform declarations)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem removeMethodDefinitionAndMixinInitializerCommands_commute
    {removeMirror initializerMirror : MirrorId} (methodMixin : MixinId)
    (method : MethodId) (fieldMixin : MixinId)
    (initializer : MixinInitializerReplacement) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.removeMethodDefinition removeMirror methodMixin method)
      (.replaceMixinInitializer initializerMirror fieldMixin initializer) := by
  exact removeMethodDefinitionAndMixinTransformCommand_commute methodMixin
    method (.replaceMixinInitializer initializerMirror fieldMixin initializer)
    fieldMixin
    (IdentifiedSourceImage.sourceMixinInitializerTransform initializer)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem compatibleRemoveMethodDefinitionCommands_commute
    {firstMirror secondMirror : MirrorId}
    {firstMixin secondMixin : MixinId} {firstMethod secondMethod : MethodId}
    (compatible : ReflectionCommandsCompatible
      (.removeMethodDefinition firstMirror firstMixin firstMethod)
      (.removeMethodDefinition secondMirror secondMixin secondMethod)) :
    OptionalCommandsCommute IdentifiedSourceImage.patchSourceCodeCommand
      (.removeMethodDefinition firstMirror firstMixin firstMethod)
      (.removeMethodDefinition secondMirror secondMixin secondMethod) := by
  obtain ⟨mixinsDifferent, methodsDifferent⟩ :=
    compatibleRemoveMethodCommands_have_distinct_targets compatible
  apply OptionalCommandsCommute.of_success_and_applicability
  · intro before after secondRemoved
    exact removeSourceMethodDefinition_applicability_preserved_by_remove
      mixinsDifferent.symm methodsDifferent.symm
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
        secondRemoved)
  · intro before after firstRemoved
    exact removeSourceMethodDefinition_applicability_preserved_by_remove
      mixinsDifferent methodsDifferent
      (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
        firstRemoved)
  · intro source firstSuccess secondSuccess
    obtain ⟨firstSelector, firstMixinDefinition, firstMethodDefinition,
        firstOwnerPresent, firstSelectorPresent, firstMixinPresent,
        firstDefinitionPresent, firstIdentity⟩ :=
      removeSourceMethodDefinition_success_witnesses source firstMixin
        firstMethod
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          firstSuccess)
    obtain ⟨secondSelector, secondMixinDefinition, secondMethodDefinition,
        secondOwnerPresent, secondSelectorPresent, secondMixinPresent,
        secondDefinitionPresent, secondIdentity⟩ :=
      removeSourceMethodDefinition_success_witnesses source secondMixin
        secondMethod
        (by simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
          secondSuccess)
    simpa [IdentifiedSourceImage.patchSourceCodeCommand] using
      source.removeSourceMethodDefinition_commutes mixinsDifferent
        methodsDifferent firstOwnerPresent secondOwnerPresent
        firstSelectorPresent secondSelectorPresent firstMixinPresent
        secondMixinPresent firstDefinitionPresent secondDefinitionPresent
        firstIdentity secondIdentity

set_option maxHeartbeats 1000000 in
/-- The seven source-edit constructors form a complete commutation matrix.
    Compatibility supplies every distinct-target premise; exact diamonds are
    embedded into lookup equivalence, while fresh store insertion uses the
    genuinely extensional diamonds proved above. -/
theorem compatibleSourceCodeCommands_commuteModulo
    {first second : ReflectionCommand}
    (firstKind : first.kind = .code) (secondKind : second.kind = .code)
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand first second := by
  cases first <;> cases second <;>
    simp [ReflectionCommand.kind] at firstKind secondKind
  all_goals first
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceMethodBodyCommands_commute _ _ compatible)
    | exact replaceMethodBodyAndReplaceMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ compatible
    | exact replaceMethodBodyAndAddMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ compatible
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndRemoveMethodDefinitionCommands_commute _ _
          compatible)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndSlotDeclarationsCommands_commute _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndNestedDeclarationsCommands_commute _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndMixinInitializerCommands_commute _ _ _ _)
    | exact (replaceMethodBodyAndReplaceMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact compatibleReplaceMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ _ compatible
    | exact replaceAndAddMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ _ compatible
    | exact replaceAndRemoveMethodDefinitionCommands_commuteModulo
        _ _ _ compatible
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndSlotDeclarationsCommands_commute
          _ _ _ _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndNestedDeclarationsCommands_commute
          _ _ _ _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndMixinInitializerCommands_commute
          _ _ _ _ _ _ _)
    | exact (replaceMethodBodyAndAddMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (replaceAndAddMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ _ compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact compatibleAddMethodDefinitionCommands_commuteModulo
        _ _ _ _ _ _ compatible
    | exact addAndRemoveMethodDefinitionCommands_commuteModulo
        _ _ _ _ compatible
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndSlotDeclarationsCommands_commute
          _ _ _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndNestedDeclarationsCommands_commute
          _ _ _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndMixinInitializerCommands_commute
          _ _ _ _ _ _)
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndRemoveMethodDefinitionCommands_commute
          _ _ compatible.symmetric)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (replaceAndRemoveMethodDefinitionCommands_commuteModulo
        _ _ _ compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (addAndRemoveMethodDefinitionCommands_commuteModulo
        _ _ _ _ compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleRemoveMethodDefinitionCommands_commute compatible)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndSlotDeclarationsCommands_commute _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndNestedDeclarationsCommands_commute _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndMixinInitializerCommands_commute _ _ _ _)
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndSlotDeclarationsCommands_commute _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndSlotDeclarationsCommands_commute
          _ _ _ _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndSlotDeclarationsCommands_commute
          _ _ _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndSlotDeclarationsCommands_commute
          _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceSlotDeclarationsCommands_commute _ _ compatible)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndNestedDeclarationsCommands_commute _ _ _ _)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndMixinInitializerCommands_commute _ _ _ _)
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndNestedDeclarationsCommands_commute
          _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndNestedDeclarationsCommands_commute
          _ _ _ _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndNestedDeclarationsCommands_commute
          _ _ _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndNestedDeclarationsCommands_commute
          _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndNestedDeclarationsCommands_commute _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceNestedDeclarationsCommands_commute _ _ compatible)
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceNestedAndMixinInitializerCommands_commute _ _ _ _)
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndMixinInitializerCommands_commute
          _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndMixinInitializerCommands_commute
          _ _ _ _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndMixinInitializerCommands_commute
          _ _ _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndMixinInitializerCommands_commute
          _ _ _ _)).symmetric IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndMixinInitializerCommands_commute _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceNestedAndMixinInitializerCommands_commute _ _ _ _)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
    | exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceMixinInitializerCommands_commute _ _ compatible)
  /-
  match first, second with
  | .replaceMethodBody _ firstMethod firstBody,
      .replaceMethodBody _ secondMethod secondBody =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceMethodBodyCommands_commute firstBody secondBody
          compatible)
  | .replaceMethodBody _ method body,
      .replaceMethodDefinition _ mixin replaced definition locals
        replacementBody =>
      exact replaceMethodBodyAndReplaceMethodDefinitionCommands_commuteModulo
        body mixin definition locals replacementBody compatible
  | .replaceMethodBody _ method body,
      .addMethodDefinition _ mixin definition locals addedBody =>
      exact replaceMethodBodyAndAddMethodDefinitionCommands_commuteModulo body
        mixin definition locals addedBody compatible
  | .replaceMethodBody _ method body,
      .removeMethodDefinition _ mixin removed =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndRemoveMethodDefinitionCommands_commute body mixin
          compatible)
  | .replaceMethodBody _ method body,
      .replaceSlotDeclarations _ mixin groups =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndSlotDeclarationsCommands_commute method body
          mixin groups)
  | .replaceMethodBody _ method body,
      .replaceNestedDeclarations _ mixin declarations =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndNestedDeclarationsCommands_commute method body
          mixin declarations)
  | .replaceMethodBody _ method body,
      .replaceMixinInitializer _ mixin initializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndMixinInitializerCommands_commute method body
          mixin initializer)
  | .replaceMethodDefinition _ mixin replaced definition locals replacementBody,
      .replaceMethodBody _ method body =>
      exact (replaceMethodBodyAndReplaceMethodDefinitionCommands_commuteModulo
        body mixin definition locals replacementBody compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMethodDefinition _ firstMixin firstMethod firstDefinition
        firstLocals firstBody,
      .replaceMethodDefinition _ secondMixin secondMethod secondDefinition
        secondLocals secondBody =>
      exact compatibleReplaceMethodDefinitionCommands_commuteModulo
        firstDefinition secondDefinition firstLocals secondLocals firstBody
        secondBody compatible
  | .replaceMethodDefinition _ mixin replaced replacementDefinition
        replacementLocals replacementBody,
      .addMethodDefinition _ addedMixin addedDefinition addedLocals addedBody =>
      exact replaceAndAddMethodDefinitionCommands_commuteModulo
        replacementDefinition addedDefinition replacementLocals addedLocals
        replacementBody addedBody compatible
  | .replaceMethodDefinition _ mixin replaced definition locals replacementBody,
      .removeMethodDefinition _ removedMixin removedMethod =>
      exact replaceAndRemoveMethodDefinitionCommands_commuteModulo definition
        locals replacementBody compatible
  | .replaceMethodDefinition _ mixin method definition locals body,
      .replaceSlotDeclarations _ fieldMixin groups =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndSlotDeclarationsCommands_commute mixin
          method definition locals body fieldMixin groups)
  | .replaceMethodDefinition _ mixin method definition locals body,
      .replaceNestedDeclarations _ fieldMixin declarations =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndNestedDeclarationsCommands_commute mixin
          method definition locals body fieldMixin declarations)
  | .replaceMethodDefinition _ mixin method definition locals body,
      .replaceMixinInitializer _ fieldMixin initializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndMixinInitializerCommands_commute mixin
          method definition locals body fieldMixin initializer)
  | .addMethodDefinition _ mixin definition locals addedBody,
      .replaceMethodBody _ method body =>
      exact (replaceMethodBodyAndAddMethodDefinitionCommands_commuteModulo body
        mixin definition locals addedBody compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .addMethodDefinition _ addedMixin addedDefinition addedLocals addedBody,
      .replaceMethodDefinition _ mixin replaced replacementDefinition
        replacementLocals replacementBody =>
      exact (replaceAndAddMethodDefinitionCommands_commuteModulo
        replacementDefinition addedDefinition replacementLocals addedLocals
        replacementBody addedBody compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .addMethodDefinition _ firstMixin firstDefinition firstLocals firstBody,
      .addMethodDefinition _ secondMixin secondDefinition secondLocals
        secondBody =>
      exact compatibleAddMethodDefinitionCommands_commuteModulo firstDefinition
        secondDefinition firstLocals secondLocals firstBody secondBody
        compatible
  | .addMethodDefinition _ mixin definition locals addedBody,
      .removeMethodDefinition _ removedMixin removedMethod =>
      exact addAndRemoveMethodDefinitionCommands_commuteModulo definition
        locals addedBody removedMethod compatible
  | .addMethodDefinition _ mixin definition locals body,
      .replaceSlotDeclarations _ fieldMixin groups =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndSlotDeclarationsCommands_commute mixin
          definition locals body fieldMixin groups)
  | .addMethodDefinition _ mixin definition locals body,
      .replaceNestedDeclarations _ fieldMixin declarations =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndNestedDeclarationsCommands_commute mixin
          definition locals body fieldMixin declarations)
  | .addMethodDefinition _ mixin definition locals body,
      .replaceMixinInitializer _ fieldMixin initializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndMixinInitializerCommands_commute mixin
          definition locals body fieldMixin initializer)
  | .removeMethodDefinition _ mixin removed,
      .replaceMethodBody _ method body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndRemoveMethodDefinitionCommands_commute body mixin
          compatible.symmetric)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .removeMethodDefinition _ removedMixin removedMethod,
      .replaceMethodDefinition _ mixin replaced definition locals
        replacementBody =>
      exact (replaceAndRemoveMethodDefinitionCommands_commuteModulo definition
        locals replacementBody compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .removeMethodDefinition _ removedMixin removedMethod,
      .addMethodDefinition _ mixin definition locals addedBody =>
      exact (addAndRemoveMethodDefinitionCommands_commuteModulo definition
        locals addedBody removedMethod compatible.symmetric).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .removeMethodDefinition _ firstMixin firstMethod,
      .removeMethodDefinition _ secondMixin secondMethod =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleRemoveMethodDefinitionCommands_commute compatible)
  | .removeMethodDefinition _ mixin method,
      .replaceSlotDeclarations _ fieldMixin groups =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndSlotDeclarationsCommands_commute mixin
          method fieldMixin groups)
  | .removeMethodDefinition _ mixin method,
      .replaceNestedDeclarations _ fieldMixin declarations =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndNestedDeclarationsCommands_commute mixin
          method fieldMixin declarations)
  | .removeMethodDefinition _ mixin method,
      .replaceMixinInitializer _ fieldMixin initializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndMixinInitializerCommands_commute mixin
          method fieldMixin initializer)
  | .replaceSlotDeclarations _ fieldMixin groups,
      .replaceMethodBody _ method body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndSlotDeclarationsCommands_commute method body
          fieldMixin groups)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceSlotDeclarations _ fieldMixin groups,
      .replaceMethodDefinition _ mixin method definition locals body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndSlotDeclarationsCommands_commute mixin
          method definition locals body fieldMixin groups)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceSlotDeclarations _ fieldMixin groups,
      .addMethodDefinition _ mixin definition locals body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndSlotDeclarationsCommands_commute mixin
          definition locals body fieldMixin groups)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceSlotDeclarations _ fieldMixin groups,
      .removeMethodDefinition _ mixin method =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndSlotDeclarationsCommands_commute mixin
          method fieldMixin groups)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceSlotDeclarations _ firstMixin firstGroups,
      .replaceSlotDeclarations _ secondMixin secondGroups =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceSlotDeclarationsCommands_commute firstGroups
          secondGroups compatible)
  | .replaceSlotDeclarations _ slotMixin groups,
      .replaceNestedDeclarations _ nestedMixin declarations =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndNestedDeclarationsCommands_commute slotMixin nestedMixin
          groups declarations)
  | .replaceSlotDeclarations _ slotMixin groups,
      .replaceMixinInitializer _ initializerMixin initializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndMixinInitializerCommands_commute slotMixin
          initializerMixin groups initializer)
  | .replaceNestedDeclarations _ fieldMixin declarations,
      .replaceMethodBody _ method body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndNestedDeclarationsCommands_commute method body
          fieldMixin declarations)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceNestedDeclarations _ fieldMixin declarations,
      .replaceMethodDefinition _ mixin method definition locals body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndNestedDeclarationsCommands_commute mixin
          method definition locals body fieldMixin declarations)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceNestedDeclarations _ fieldMixin declarations,
      .addMethodDefinition _ mixin definition locals body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndNestedDeclarationsCommands_commute mixin
          definition locals body fieldMixin declarations)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceNestedDeclarations _ fieldMixin declarations,
      .removeMethodDefinition _ mixin method =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndNestedDeclarationsCommands_commute mixin
          method fieldMixin declarations)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceNestedDeclarations _ nestedMixin declarations,
      .replaceSlotDeclarations _ slotMixin groups =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndNestedDeclarationsCommands_commute slotMixin nestedMixin
          groups declarations)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceNestedDeclarations _ firstMixin firstDeclarations,
      .replaceNestedDeclarations _ secondMixin secondDeclarations =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceNestedDeclarationsCommands_commute firstDeclarations
          secondDeclarations compatible)
  | .replaceNestedDeclarations _ nestedMixin declarations,
      .replaceMixinInitializer _ initializerMixin initializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceNestedAndMixinInitializerCommands_commute nestedMixin
          initializerMixin declarations initializer)
  | .replaceMixinInitializer _ fieldMixin initializer,
      .replaceMethodBody _ method body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodBodyAndMixinInitializerCommands_commute method body
          fieldMixin initializer)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMixinInitializer _ fieldMixin initializer,
      .replaceMethodDefinition _ mixin method definition locals body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceMethodDefinitionAndMixinInitializerCommands_commute mixin
          method definition locals body fieldMixin initializer)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMixinInitializer _ fieldMixin initializer,
      .addMethodDefinition _ mixin definition locals body =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (addMethodDefinitionAndMixinInitializerCommands_commute mixin
          definition locals body fieldMixin initializer)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMixinInitializer _ fieldMixin initializer,
      .removeMethodDefinition _ mixin method =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (removeMethodDefinitionAndMixinInitializerCommands_commute mixin
          method fieldMixin initializer)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMixinInitializer _ initializerMixin initializer,
      .replaceSlotDeclarations _ slotMixin groups =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceSlotAndMixinInitializerCommands_commute slotMixin
          initializerMixin groups initializer)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMixinInitializer _ initializerMixin initializer,
      .replaceNestedDeclarations _ nestedMixin declarations =>
      exact (OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (replaceNestedAndMixinInitializerCommands_commute nestedMixin
          initializerMixin declarations initializer)).symmetric
          IdentifiedSourceImage.LookupEquivalent.symm
  | .replaceMixinInitializer _ firstMixin firstInitializer,
      .replaceMixinInitializer _ secondMixin secondInitializer =>
      exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (compatibleReplaceMixinInitializerCommands_commute firstInitializer
          secondInitializer compatible)
  | otherFirst, otherSecond =>
      cases otherFirst <;> cases otherSecond <;>
        simp [ReflectionCommand.kind] at firstKind secondKind
  -/

theorem IdentifiedSourceImage.patchSourceCodeCommand_eq_none_of_kind_ne_code
    (source : IdentifiedSourceImage) (command : ReflectionCommand)
    (notCode : command.kind ≠ .code) :
    source.patchSourceCodeCommand command = none := by
  cases command <;>
    simp [ReflectionCommand.kind,
      IdentifiedSourceImage.patchSourceCodeCommand] at notCode ⊢

/-- Compatibility suffices for the source patch phase on arbitrary reflection
    commands.  If either command is not a source edit, that side is rejected by
    the phase dispatcher; otherwise the exhaustive seven-by-seven matrix
    applies. -/
theorem compatibleCommands_sourcePatch_commuteModulo
    {first second : ReflectionCommand}
    (compatible : ReflectionCommandsCompatible first second) :
    OptionalCommandsCommuteModulo IdentifiedSourceImage.LookupEquivalent
      IdentifiedSourceImage.patchSourceCodeCommand first second := by
  by_cases firstCode : first.kind = .code
  · by_cases secondCode : second.kind = .code
    · exact compatibleSourceCodeCommands_commuteModulo firstCode secondCode
        compatible
    · exact OptionalCommandsCommute.to_modulo
        IdentifiedSourceImage.LookupEquivalent.refl
        (OptionalCommandsCommute.of_right_failure fun source =>
          source.patchSourceCodeCommand_eq_none_of_kind_ne_code second
            secondCode)
  · exact OptionalCommandsCommute.to_modulo
      IdentifiedSourceImage.LookupEquivalent.refl
      (OptionalCommandsCommute.of_left_failure fun source =>
        source.patchSourceCodeCommand_eq_none_of_kind_ne_code first firstCode)

theorem sourceTransactionIndependentModulo_of_nonconflicting
    {transaction : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting transaction) :
    SourceTransactionIndependentModulo transaction := by
  unfold SourceTransactionIndependentModulo codeCommands
  exact (nonconflicting.filter _).imp fun compatible =>
    compatibleCommands_sourcePatch_commuteModulo compatible

/-- Pairwise nonconflict now generates every certificate required by the
    complete reflection pipeline: source edits, re-elaboration, runtime phases,
    and atomic installation are invariant under transaction permutation. -/
theorem prepareReflection_permutation_of_nonconflicting
    (before : ReflectiveVM IdentifiedSourceImage) (requester : ActorId)
    {original permuted : List ReflectionCommand}
    (nonconflicting : ReflectionTransactionNonconflicting original)
    (permutation : original.Perm permuted)
    (initialCoherent : ActorStoreDomainsCoherent before.world) :
    OptionalResultsRelated ReflectiveVM.LookupEquivalent
      (prepareReflection identifiedSourceReflectionFrontEnd
        prepareReflectionRuntime before requester original)
      (prepareReflection identifiedSourceReflectionFrontEnd
        prepareReflectionRuntime before requester permuted) :=
  prepareReflection_permutation_of_certificates before requester
    (sourceTransactionIndependentModulo_of_nonconflicting nonconflicting)
    (reflectionRuntimePermutationCertificates_of_nonconflicting before
      requester nonconflicting permutation initialCoherent)

end Newspeak
