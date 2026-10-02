import Newspeak.Closures

namespace Newspeak

namespace Program

/-- Atomic literals and the direct physical-slot primitives of
    Equations (9.26), (9.35), and (10.4).  These rules are deliberately
    separate from sends: synthesized accessors reduce to these terms and can
    neither recurse through nor be intercepted by an override. -/
inductive ObjectSlotStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | atom {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {payload : AtomPayload} :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩, .evaluate (.atom payload)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object (p.atoms payload)⟩
  | read {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : SlotId} {value : ObjRef}
      (found : state.heap.readObjectSlot object slot = some value) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.readSlot object slot)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object value⟩
  | writeStart {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : SlotId} {expression : CoreExpr} :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.writeSlot object slot expression)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.slotWrite object slot)⟩, .evaluate expression⟩
  | writeCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : SlotId} {value : ObjRef} {heap : Heap}
      (written : state.heap.writeObjectSlot object slot value = some heap) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current,
          .push frames (.slotWrite object slot)⟩, .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .object value⟩
  | currentRead {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId}
      (currentActivation : state.heap.activations current = some activation)
      (receiver : activation.currentReceiver = .ordinaryObject object) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.currentRead slot)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.readSlot object slot)⟩
  | currentWrite {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {expression : CoreExpr}
      (currentActivation : state.heap.activations current = some activation)
      (receiver : activation.currentReceiver = .ordinaryObject object) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.currentWrite slot expression)⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.writeSlot object slot expression)⟩
  | lazyHit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {initializer : CoreExpr}
      {value : ObjRef}
      (currentActivation : state.heap.activations current = some activation)
      (receiver : activation.currentReceiver = .ordinaryObject object)
      (found : state.heap.readObjectSlot object slot = some value)
      (notNil : value ≠ p.nilObject) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.lazyRead slot initializer)⟩
        ⟨state, .push rest ⟨current, frames⟩, .object value⟩
  | lazyMiss {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {activation : ActivationDef}
      {object : ObjectId} {slot : SlotId} {initializer : CoreExpr}
      (currentActivation : state.heap.activations current = some activation)
      (receiver : activation.currentReceiver = .ordinaryObject object)
      (found : state.heap.readObjectSlot object slot = some p.nilObject) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current, frames⟩,
          .evaluate (.lazyRead slot initializer)⟩
        ⟨state, .push rest ⟨current,
          .push frames (.lazySlotStore object slot)⟩, .evaluate initializer⟩
  | lazyCommit {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {object : ObjectId}
      {slot : SlotId} {value : ObjRef} {heap : Heap}
      (written : state.heap.writeObjectSlot object slot value = some heap) :
      ObjectSlotStep p
        ⟨state, .push rest ⟨current,
          .push frames (.lazySlotStore object slot)⟩, .object value⟩
        ⟨{state with heap := heap}, .push rest ⟨current, frames⟩,
          .object value⟩

theorem objectSlotStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ObjectSlotStep before after₁)
    (step₂ : p.ObjectSlotStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | atom => cases step₂; rfl
  | read found₁ =>
      cases step₂ with
      | read found₂ =>
          have equal := Option.some.inj (found₁.symm.trans found₂)
          subst equal
          rfl

  | writeStart => cases step₂; rfl
  | writeCommit written₁ =>
      cases step₂ with
      | writeCommit written₂ =>
          have equal := Option.some.inj (written₁.symm.trans written₂)
          subst equal
          rfl
  | currentRead activation₁ receiver₁ =>
      cases step₂ with
      | currentRead activation₂ receiver₂ =>
          have equal := Option.some.inj (activation₁.symm.trans activation₂)
          subst equal
          cases receiver₁.symm.trans receiver₂
          rfl
  | currentWrite activation₁ receiver₁ =>
      cases step₂ with
      | currentWrite activation₂ receiver₂ =>
          have equal := Option.some.inj (activation₁.symm.trans activation₂)
          subst equal
          cases receiver₁.symm.trans receiver₂
          rfl
  | lazyHit activation₁ receiver₁ found₁ notNil₁ =>
      cases step₂ with
      | lazyHit activation₂ receiver₂ found₂ notNil₂ =>
          have activationEqual := Option.some.inj
            (activation₁.symm.trans activation₂)
          subst activationEqual
          have objectEqual := ObjRef.ordinaryObject.inj
            (receiver₁.symm.trans receiver₂)
          subst objectEqual
          have equal := Option.some.inj (found₁.symm.trans found₂)
          subst equal
          rfl
      | lazyMiss activation₂ receiver₂ found₂ =>
          have activationEqual := Option.some.inj
            (activation₁.symm.trans activation₂)
          subst activationEqual
          have objectEqual := ObjRef.ordinaryObject.inj
            (receiver₁.symm.trans receiver₂)
          subst objectEqual
          have equal := Option.some.inj (found₁.symm.trans found₂)
          exact (notNil₁ equal).elim
  | lazyMiss activation₁ receiver₁ found₁ =>
      cases step₂ with
      | lazyHit activation₂ receiver₂ found₂ notNil₂ =>
          have activationEqual := Option.some.inj
            (activation₁.symm.trans activation₂)
          subst activationEqual
          have objectEqual := ObjRef.ordinaryObject.inj
            (receiver₁.symm.trans receiver₂)
          subst objectEqual
          have equal := Option.some.inj (found₁.symm.trans found₂)
          exact (notNil₂ equal.symm).elim
      | lazyMiss activation₂ receiver₂ found₂ =>
          have activationEqual := Option.some.inj
            (activation₁.symm.trans activation₂)
          subst activationEqual
          have objectEqual := ObjRef.ordinaryObject.inj
            (receiver₁.symm.trans receiver₂)
          subst objectEqual
          rfl
  | lazyCommit written₁ =>
      cases step₂ with
      | lazyCommit written₂ =>
          have equal := Option.some.inj (written₁.symm.trans written₂)
          subst equal
          rfl

/-- The identity half of Equation (10.3): two atomic payloads mapped to the
    same object are the same exact payload.  The converse is congruence of the
    `atoms` function. -/
theorem atomPayload_of_sameObject {p : Program} {h : Heap}
    (wf : p.WellFormed h) {left right : AtomPayload}
    (same : p.atoms left = p.atoms right) : left = right :=
  wf.atomCanonical same

theorem atomObject_iff_payload {p : Program} {h : Heap}
    (wf : p.WellFormed h) (left right : AtomPayload) :
    p.atoms left = p.atoms right ↔ left = right := by
  constructor
  · exact atomPayload_of_sameObject wf
  · intro equal
    subst equal
    rfl

end Program
end Newspeak
