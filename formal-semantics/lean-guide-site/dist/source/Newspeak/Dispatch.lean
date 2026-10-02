import Newspeak.ClassApplications

namespace Newspeak

inductive DispatchResult where
  | invoke (method : MethodDef) (receiver : ObjRef)
      (definingClass : ClassId) (message : Message)
  | missing (receiver : ObjRef) (lookupStart : ClassId)
      (message : Message)
  | invalidSuper (currentClass : ClassId)
deriving Repr, DecidableEq, BEq

namespace Program

/-- Send-Public and Send-Missing. -/
inductive OrdinaryDispatch (p : Program) (h : Heap)
    (receiver : ObjRef) (message : Message) : DispatchResult → Prop where
  | hit {receiverClass definingClass : ClassId} {method : MethodDef} :
      h.classOf receiver = some receiverClass →
      p.PublicLookupRules h message.selector receiverClass
        (some ⟨method, definingClass⟩) →
      OrdinaryDispatch p h receiver message
        (.invoke method receiver definingClass message)
  | missing {receiverClass : ClassId} :
      h.classOf receiver = some receiverClass →
      p.PublicLookupRules h message.selector receiverClass none →
      OrdinaryDispatch p h receiver message
        (.missing receiver receiverClass message)

/-- Super-Hit, Super-Missing, and the two explicit invalid-super rules. -/
inductive SuperDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (message : Message) : DispatchResult → Prop where
  | hit {activation : ActivationDef} {currentClass lookupStart definingClass : ClassId}
      {method : MethodDef} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      currentClass ≠ p.object →
      currentClass ≠ p.top →
      p.superclass? h currentClass = some lookupStart →
      p.ProtectedLookupRules h message.selector lookupStart
        (some ⟨method, definingClass⟩) →
      SuperDispatch p h activationId message
        (.invoke method activation.currentReceiver definingClass message)
  | missing {activation : ActivationDef} {currentClass lookupStart : ClassId} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      currentClass ≠ p.object →
      currentClass ≠ p.top →
      p.superclass? h currentClass = some lookupStart →
      p.ProtectedLookupRules h message.selector lookupStart none →
      SuperDispatch p h activationId message
        (.missing activation.currentReceiver lookupStart message)
  | objectError {activation : ActivationDef} :
      h.activations activationId = some activation →
      activation.currentClass = some p.object →
      SuperDispatch p h activationId message (.invalidSuper p.object)
  | topError {activation : ActivationDef} :
      h.activations activationId = some activation →
      activation.currentClass = some p.top →
      SuperDispatch p h activationId message (.invalidSuper p.top)

def doesNotUnderstandSelector : Selector :=
  ⟨"doesNotUnderstand:"⟩

/-- The selection portion of DNU fallback.  Reification of the original
    message mirror is an allocation step of the sequential machine, so this
    judgment determines exactly the method/current-class pair to invoke. -/
inductive DnuSelection (p : Program) (h : Heap) (lookupStart : ClassId) :
    LookupResult → Prop where
  | found {result : LookupResult} :
      p.UnrestrictedLookupRules h doesNotUnderstandSelector lookupStart
        (some result) →
      DnuSelection p h lookupStart result

theorem ordinaryDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {receiver : ObjRef} {message : Message}
    {r₁ r₂ : DispatchResult}
    (d₁ : p.OrdinaryDispatch h receiver message r₁)
    (d₂ : p.OrdinaryDispatch h receiver message r₂) : r₁ = r₂ := by
  cases d₁ with
  | @hit receiverClass₁ definingClass₁ method₁ hc₁ hl₁ =>
      cases d₂ with
      | @hit receiverClass₂ definingClass₂ method₂ hc₂ hl₂ =>
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := publicRules_deterministic chain hl₁ hl₂
          have hresult := Option.some.inj hr
          cases hresult
          rfl
      | @missing receiverClass₂ hc₂ hl₂ =>
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := publicRules_deterministic chain hl₁ hl₂
          cases hr
  | @missing receiverClass₁ hc₁ hl₁ =>
      cases d₂ with
      | @hit receiverClass₂ definingClass₂ method₂ hc₂ hl₂ =>
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := publicRules_deterministic chain hl₁ hl₂
          cases hr
      | @missing receiverClass₂ hc₂ hl₂ =>
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          rfl

theorem superDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId} {message : Message}
    {r₁ r₂ : DispatchResult}
    (d₁ : p.SuperDispatch h activationId message r₁)
    (d₂ : p.SuperDispatch h activationId message r₂) : r₁ = r₂ := by
  cases d₁ with
  | @hit activation₁ current₁ start₁ defining₁ method₁ ha₁ hc₁ hobj₁ htop₁ hs₁ hl₁ =>
      cases d₂ with
      | @hit activation₂ current₂ start₂ defining₂ method₂ ha₂ hc₂ _ _ hs₂ hl₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : current₁ = current₂ :=
            Option.some.inj (hc₁.symm.trans hc₂)
          subst current₂
          have hstart : start₁ = start₂ := by
            rw [hs₁] at hs₂
            injection hs₂
          subst start₂
          have live := wf.superclassIsLive current₁ start₁ hs₁
          have chain := wf.chain_exists live
          have hr := protectedRules_deterministic chain hl₁ hl₂
          have hresult := Option.some.inj hr
          cases hresult
          rfl
      | @missing activation₂ current₂ start₂ ha₂ hc₂ _ _ hs₂ hl₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : current₁ = current₂ :=
            Option.some.inj (hc₁.symm.trans hc₂)
          subst current₂
          have hstart : start₁ = start₂ := by
            rw [hs₁] at hs₂
            injection hs₂
          subst start₂
          have live := wf.superclassIsLive current₁ start₁ hs₁
          have chain := wf.chain_exists live
          have hr := protectedRules_deterministic chain hl₁ hl₂
          cases hr
      | @objectError activation₂ ha₂ heq₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₁ = p.object :=
            Option.some.inj (hc₁.symm.trans heq₂)
          exact (hobj₁ this).elim
      | @topError activation₂ ha₂ heq₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₁ = p.top :=
            Option.some.inj (hc₁.symm.trans heq₂)
          exact (htop₁ this).elim
  | @missing activation₁ current₁ start₁ ha₁ hc₁ hobj₁ htop₁ hs₁ hl₁ =>
      cases d₂ with
      | @hit activation₂ current₂ start₂ defining₂ method₂ ha₂ hc₂ _ _ hs₂ hl₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : current₁ = current₂ :=
            Option.some.inj (hc₁.symm.trans hc₂)
          subst current₂
          have hstart : start₁ = start₂ := by
            rw [hs₁] at hs₂
            injection hs₂
          subst start₂
          have live := wf.superclassIsLive current₁ start₁ hs₁
          have chain := wf.chain_exists live
          have hr := protectedRules_deterministic chain hl₁ hl₂
          cases hr
      | @missing activation₂ current₂ start₂ ha₂ hc₂ _ _ hs₂ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : current₁ = current₂ :=
            Option.some.inj (hc₁.symm.trans hc₂)
          subst current₂
          have hstart : start₁ = start₂ := by
            rw [hs₁] at hs₂
            injection hs₂
          subst start₂
          rfl
      | @objectError activation₂ ha₂ heq₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₁ = p.object :=
            Option.some.inj (hc₁.symm.trans heq₂)
          exact (hobj₁ this).elim
      | @topError activation₂ ha₂ heq₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₁ = p.top :=
            Option.some.inj (hc₁.symm.trans heq₂)
          exact (htop₁ this).elim
  | @objectError activation₁ ha₁ heq₁ =>
      cases d₂ with
      | @hit activation₂ current₂ _ _ _ ha₂ hc₂ hobj₂ _ _ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₂ = p.object :=
            Option.some.inj (hc₂.symm.trans heq₁)
          exact (hobj₂ this).elim
      | @missing activation₂ current₂ _ ha₂ hc₂ hobj₂ _ _ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₂ = p.object :=
            Option.some.inj (hc₂.symm.trans heq₁)
          exact (hobj₂ this).elim
      | @objectError activation₂ ha₂ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          rfl
      | @topError activation₂ ha₂ heq₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : p.object = p.top := Option.some.inj (heq₁.symm.trans heq₂)
          exact (wf.objectIsNotTop this).elim
  | @topError activation₁ ha₁ heq₁ =>
      cases d₂ with
      | @hit activation₂ current₂ _ _ _ ha₂ hc₂ _ htop₂ _ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₂ = p.top :=
            Option.some.inj (hc₂.symm.trans heq₁)
          exact (htop₂ this).elim
      | @missing activation₂ current₂ _ ha₂ hc₂ _ htop₂ _ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : current₂ = p.top :=
            Option.some.inj (hc₂.symm.trans heq₁)
          exact (htop₂ this).elim
      | @objectError activation₂ ha₂ heq₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have : p.object = p.top := Option.some.inj (heq₂.symm.trans heq₁)
          exact (wf.objectIsNotTop this).elim
      | @topError activation₂ ha₂ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          rfl

theorem dnuSelection_deterministic {p : Program} {h : Heap}
    {lookupStart : ClassId} {r₁ r₂ : LookupResult}
    (hasChain : ∃ chain, p.ClassChain h lookupStart chain)
    (d₁ : p.DnuSelection h lookupStart r₁)
    (d₂ : p.DnuSelection h lookupStart r₂) : r₁ = r₂ := by
  cases d₁ with
  | found hl₁ =>
      cases d₂ with
      | found hl₂ =>
          have hr := unrestrictedRules_deterministic hasChain hl₁ hl₂
          exact Option.some.inj hr

end Program
end Newspeak
