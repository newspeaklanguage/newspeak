import Newspeak.ImplicitDispatch

namespace Newspeak

/-- The allocation-bearing fragment of sequential state.  Additional fresh
    supplies can be added independently as expression evaluation grows. -/
structure AllocationState where
  heap : Heap
  nextMirror : Nat
  nextActivation : Nat
  nextClosure : Nat
  nextObject : Nat
  nextClass : Nat

/-- Every identity at or above the supply frontier is absent from the mirror
    store. -/
def AllocationState.MirrorSupplyFresh (state : AllocationState) : Prop :=
  ∀ id : MirrorId, state.nextMirror ≤ id.index →
    state.heap.mirrors id = none

/-- Every identity at or above the activation-supply frontier is absent. -/
def AllocationState.ActivationSupplyFresh (state : AllocationState) : Prop :=
  ∀ id : ActivationId, state.nextActivation ≤ id.index →
    state.heap.activations id = none

def AllocationState.ClosureSupplyFresh (state : AllocationState) : Prop :=
  ∀ id : ClosureId, state.nextClosure ≤ id.index →
    state.heap.closures id = none

def AllocationState.ObjectSupplyFresh (state : AllocationState) : Prop :=
  ∀ id : ObjectId, state.nextObject ≤ id.index →
    state.heap.objects id = none

def AllocationState.ClassSupplyFresh (state : AllocationState) : Prop :=
  ∀ id : ClassId, state.nextClass ≤ id.index →
    state.heap.classes id = none

def AllocationState.SuppliesFresh (state : AllocationState) : Prop :=
  state.MirrorSupplyFresh ∧
    state.ActivationSupplyFresh ∧ state.ClosureSupplyFresh ∧
    state.ObjectSupplyFresh ∧ state.ClassSupplyFresh

def Program.messageMirrorDefinition (p : Program)
    (message : Message) : MirrorDef :=
  ⟨p.messageMirrorClass, .message message⟩

/-- Allocate and install the mirror that reifies one failed send. -/
def Program.allocateMessageMirror (p : Program) (state : AllocationState)
    (message : Message) : AllocationState × ObjRef :=
  let id : MirrorId := ⟨state.nextMirror⟩
  let mirror := p.messageMirrorDefinition message
  ({ state with heap := state.heap.installMirror id mirror
                nextMirror := state.nextMirror + 1 },
    .mirrorObject id)

namespace Program

@[simp] theorem allocateMessageMirror_reference (p : Program)
    (state : AllocationState) (message : Message) :
    (p.allocateMessageMirror state message).2 =
      .mirrorObject ⟨state.nextMirror⟩ := by
  rfl

@[simp] theorem allocateMessageMirror_installs (p : Program)
    (state : AllocationState) (message : Message) :
    (p.allocateMessageMirror state message).1.heap.mirrors
        ⟨state.nextMirror⟩ =
      some (p.messageMirrorDefinition message) := by
  simp [allocateMessageMirror]

theorem allocateMessageMirror_was_fresh (_p : Program)
    {state : AllocationState} (fresh : state.MirrorSupplyFresh)
    (_message : Message) :
    state.heap.mirrors ⟨state.nextMirror⟩ = none :=
  fresh ⟨state.nextMirror⟩ (Nat.le_refl _)

theorem allocateMessageMirror_preserves_freshness (p : Program)
    {state : AllocationState} (fresh : state.MirrorSupplyFresh)
    (message : Message) :
    (p.allocateMessageMirror state message).1.MirrorSupplyFresh := by
  intro id hid
  have hid' : state.nextMirror + 1 ≤ id.index := by
    simpa [allocateMessageMirror] using hid
  have hne : id ≠ (⟨state.nextMirror⟩ : MirrorId) := by
    intro heq
    have hindex : id.index = state.nextMirror := congrArg MirrorId.index heq
    omega
  rw [show (p.allocateMessageMirror state message).1.heap =
      state.heap.installMirror ⟨state.nextMirror⟩
        (p.messageMirrorDefinition message) by rfl]
  rw [Heap.installMirror_away state.heap
    (p.messageMirrorDefinition message) hne]
  apply fresh id
  omega

theorem allocateMessageMirror_preserves_activationFreshness (p : Program)
    {state : AllocationState} (fresh : state.ActivationSupplyFresh)
    (message : Message) :
    (p.allocateMessageMirror state message).1.ActivationSupplyFresh := by
  intro id hid
  apply fresh id
  simpa [allocateMessageMirror] using hid

theorem allocateMessageMirror_preserves_closureFreshness (p : Program)
    {state : AllocationState} (fresh : state.ClosureSupplyFresh)
    (message : Message) :
    (p.allocateMessageMirror state message).1.ClosureSupplyFresh := by
  intro id hid
  apply fresh id
  simpa [allocateMessageMirror] using hid

theorem allocateMessageMirror_preserves_supplies (p : Program)
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (message : Message) :
    (p.allocateMessageMirror state message).1.SuppliesFresh :=
  ⟨p.allocateMessageMirror_preserves_freshness fresh.1 message,
    p.allocateMessageMirror_preserves_activationFreshness fresh.2.1 message,
    p.allocateMessageMirror_preserves_closureFreshness fresh.2.2.1 message,
    by
      intro id bound
      exact fresh.2.2.2.1 id (by simpa [allocateMessageMirror] using bound),
    by
      intro id bound
      exact fresh.2.2.2.2 id (by simpa [allocateMessageMirror] using bound)⟩

/-- The state/result pair produced once DNU method selection has succeeded. -/
def finishDnu (p : Program) (state : AllocationState) (receiver : ObjRef)
    (original : Message) (lookup : LookupResult) :
    AllocationState × DispatchResult :=
  let allocation := p.allocateMessageMirror state original
  let dnuMessage : Message :=
    ⟨doesNotUnderstandSelector, [allocation.2]⟩
  (allocation.1,
    .invoke lookup.method receiver lookup.definingClass dnuMessage)

/-- Complete DNU fallback: select `doesNotUnderstand:` without access
    restriction, allocate a mirror of the original message, and invoke the
    selected method with that mirror as its sole argument. -/
inductive DnuFallback (p : Program) (state : AllocationState)
    (receiver : ObjRef) (lookupStart : ClassId) (original : Message) :
    AllocationState → DispatchResult → Prop where
  | apply {lookup : LookupResult}
      (selection : p.DnuSelection state.heap lookupStart lookup) :
      DnuFallback p state receiver lookupStart original
        (p.finishDnu state receiver original lookup).1
        (p.finishDnu state receiver original lookup).2

theorem dnuFallback_deterministic {p : Program} {state : AllocationState}
    {receiver : ObjRef} {lookupStart : ClassId} {original : Message}
    {state₁ state₂ : AllocationState} {result₁ result₂ : DispatchResult}
    (hasChain : ∃ chain, p.ClassChain state.heap lookupStart chain)
    (d₁ : p.DnuFallback state receiver lookupStart original state₁ result₁)
    (d₂ : p.DnuFallback state receiver lookupStart original state₂ result₂) :
    state₁ = state₂ ∧ result₁ = result₂ := by
  cases d₁ with
  | @apply lookup₁ selection₁ =>
      cases d₂ with
      | @apply lookup₂ selection₂ =>
          have hlookup := dnuSelection_deterministic hasChain selection₁ selection₂
          subst lookup₂
          exact ⟨rfl, rfl⟩

end Program
end Newspeak
