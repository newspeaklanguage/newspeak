import Newspeak.Enclosing

namespace Newspeak
namespace Program

/-- Static private selection from Equation (6.1). -/
def privateMethod (p : Program) (target : ClassDeclId)
    (selector : Selector) : Option MethodDef := do
  let mixinId ← p.declMixin (.namedClass target)
  let mixinDef ← p.mixins mixinId
  let method ← mixinDef.methods selector
  if method.access = .privateAccess then some method else none

/-- Outer-Private, Outer-Protected, and the corresponding missing result. -/
inductive OuterDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (target immediate : ClassDeclId)
    (message : Message) : DispatchResult → Prop where
  | privateHit {activation : ActivationDef} {currentClass : ClassId} {depth : Nat}
      {receiver : ObjRef} {targetApplication : ClassId} {method : MethodDef} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      p.LexicalDepth target immediate (some depth) →
      p.EnclosingReceiver h activation.currentReceiver currentClass
        depth receiver →
      p.TargetApplication h receiver target (some targetApplication) →
      p.privateMethod target message.selector = some method →
      OuterDispatch p h activationId target immediate message
        (.invoke method receiver targetApplication message)
  | protectedHit {activation : ActivationDef} {currentClass : ClassId} {depth : Nat}
      {receiver : ObjRef} {receiverClass definingClass : ClassId}
      {method : MethodDef} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      p.LexicalDepth target immediate (some depth) →
      p.EnclosingReceiver h activation.currentReceiver currentClass
        depth receiver →
      p.privateMethod target message.selector = none →
      h.classOf receiver = some receiverClass →
      p.ProtectedLookupRules h message.selector receiverClass
        (some ⟨method, definingClass⟩) →
      OuterDispatch p h activationId target immediate message
        (.invoke method receiver definingClass message)
  | missing {activation : ActivationDef} {currentClass : ClassId} {depth : Nat}
      {receiver : ObjRef} {receiverClass : ClassId} :
      h.activations activationId = some activation →
      activation.currentClass = some currentClass →
      p.LexicalDepth target immediate (some depth) →
      p.EnclosingReceiver h activation.currentReceiver currentClass
        depth receiver →
      p.privateMethod target message.selector = none →
      h.classOf receiver = some receiverClass →
      p.ProtectedLookupRules h message.selector receiverClass none →
      OuterDispatch p h activationId target immediate message
        (.missing receiver receiverClass message)

def SelfDispatch (p : Program) (h : Heap) (activationId : ActivationId)
    (immediate : ClassDeclId) (message : Message)
    (result : DispatchResult) : Prop :=
  p.OuterDispatch h activationId immediate immediate message result

theorem privateMethod_unique {p : Program} {target : ClassDeclId}
    {selector : Selector} {m₁ m₂ : MethodDef}
    (h₁ : p.privateMethod target selector = some m₁)
    (h₂ : p.privateMethod target selector = some m₂) : m₁ = m₂ := by
  rw [h₁] at h₂
  injection h₂

theorem outerDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {target immediate : ClassDeclId} {message : Message}
    {r₁ r₂ : DispatchResult}
    (d₁ : p.OuterDispatch h activationId target immediate message r₁)
    (d₂ : p.OuterDispatch h activationId target immediate message r₂) : r₁ = r₂ := by
  cases d₁ with
  | @privateHit activation₁ currentClass₁ depth₁ receiver₁ app₁ method₁
      ha₁ hcc₁ hd₁ he₁ happ₁ hp₁ =>
      cases d₂ with
      | @privateHit activation₂ currentClass₂ depth₂ receiver₂ app₂
          method₂ ha₂ hcc₂ hd₂ he₂ happ₂ hp₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          have happId := Option.some.inj
            (targetApplication_deterministic happ₁ happ₂)
          subst app₂
          have hmethod := privateMethod_unique hp₁ hp₂
          subst method₂
          rfl
      | @protectedHit activation₂ currentClass₂ depth₂ receiver₂ _ _ _
          ha₂ hcc₂ hd₂ he₂ hp₂ _ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          rw [hp₁] at hp₂
          contradiction
      | @missing activation₂ currentClass₂ depth₂ receiver₂ _ ha₂ hcc₂
          hd₂ he₂ hp₂ _ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          rw [hp₁] at hp₂
          contradiction
  | @protectedHit activation₁ currentClass₁ depth₁ receiver₁ receiverClass₁
      defining₁ method₁ ha₁ hcc₁ hd₁ he₁ hp₁ hc₁ hl₁ =>
      cases d₂ with
      | @privateHit activation₂ currentClass₂ depth₂ receiver₂ _ _ ha₂ hcc₂
          hd₂ he₂ _ hp₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          rw [hp₁] at hp₂
          contradiction
      | @protectedHit activation₂ currentClass₂ depth₂ receiver₂ receiverClass₂
          defining₂ method₂ ha₂ hcc₂ hd₂ he₂ _ hc₂ hl₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver₁ receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := protectedRules_deterministic chain hl₁ hl₂
          have hresult := Option.some.inj hr
          cases hresult
          rfl
      | @missing activation₂ currentClass₂ depth₂ receiver₂ receiverClass₂
          ha₂ hcc₂ hd₂ he₂ _ hc₂ hl₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver₁ receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := protectedRules_deterministic chain hl₁ hl₂
          cases hr
  | @missing activation₁ currentClass₁ depth₁ receiver₁ receiverClass₁
      ha₁ hcc₁ hd₁ he₁ hp₁ hc₁ hl₁ =>
      cases d₂ with
      | @privateHit activation₂ currentClass₂ depth₂ receiver₂ _ _ ha₂ hcc₂
          hd₂ he₂ _ hp₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          rw [hp₁] at hp₂
          contradiction
      | @protectedHit activation₂ currentClass₂ depth₂ receiver₂ receiverClass₂ _ _
          ha₂ hcc₂ hd₂ he₂ _ hc₂ hl₂ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver₁ receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := protectedRules_deterministic chain hl₁ hl₂
          cases hr
      | @missing activation₂ currentClass₂ depth₂ receiver₂ receiverClass₂
          ha₂ hcc₂ hd₂ he₂ _ hc₂ _ =>
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hcurrent : currentClass₁ = currentClass₂ :=
            Option.some.inj (hcc₁.symm.trans hcc₂)
          subst currentClass₂
          have hdepth := Option.some.inj (lexicalDepth_deterministic hd₁ hd₂)
          subst depth₂
          have hreceiver := enclosingReceiver_deterministic he₁ he₂
          subst receiver₂
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          rfl

theorem selfDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {immediate : ClassDeclId} {message : Message} {r₁ r₂ : DispatchResult}
    (d₁ : p.SelfDispatch h activationId immediate message r₁)
    (d₂ : p.SelfDispatch h activationId immediate message r₂) : r₁ = r₂ :=
  outerDispatch_deterministic wf d₁ d₂

end Program
end Newspeak
