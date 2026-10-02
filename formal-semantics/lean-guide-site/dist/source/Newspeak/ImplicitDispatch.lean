import Newspeak.ImplicitClassDispatch

namespace Newspeak
namespace Program

/-- Complete annotated implicit dispatch from Equation (6.6).  The annotation
    is produced by elaboration: `none` denotes the self-send fallback. -/
inductive ImplicitDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (immediate : Option ClassDeclId)
    (annotation : Option ScopeDecl) (message : Message) :
    DispatchResult → Prop where
  | classScope {target currentClass : ClassDeclId} {result : DispatchResult} :
      annotation = some (.classDecl target) →
      immediate = some currentClass →
      p.OuterDispatch h activationId target currentClass message result →
      ImplicitDispatch p h activationId immediate annotation message result
  | objectLiteralScope {activation : ActivationDef}
      {declaration : ObjectLiteralDeclId} {receiver : ObjRef}
      {receiverClass definingClass : ClassId} {method : MethodDef} :
      annotation = some (.objectLiteralDecl declaration) →
      h.activations activationId = some activation →
      activation.objectLiteralScopes declaration = some receiver →
      h.classOf receiver = some receiverClass →
      p.UnrestrictedLookupRules h message.selector receiverClass
        (some ⟨method, definingClass⟩) →
      p.classBodyDeclaration? h definingClass =
        some (.objectLiteral declaration) →
      ImplicitDispatch p h activationId immediate annotation message
        (.invoke method receiver definingClass message)
  | activationScope {activation : ActivationDef}
      {declaration : ActivationDeclId} {targetActivation : ActivationId}
      {result : DispatchResult} :
      annotation = some (.activationDecl declaration) →
      h.activations activationId = some activation →
      activation.activationScopes declaration = some targetActivation →
      p.OrdinaryDispatch h (.activationObject targetActivation) message result →
      ImplicitDispatch p h activationId immediate annotation message result
  | self {currentClass : ClassDeclId} {result : DispatchResult} :
      annotation = none →
      immediate = some currentClass →
      p.SelfDispatch h activationId currentClass message result →
      ImplicitDispatch p h activationId immediate annotation message result

theorem implicitDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {immediate : Option ClassDeclId} {annotation : Option ScopeDecl}
    {message : Message} {r₁ r₂ : DispatchResult}
    (d₁ : p.ImplicitDispatch h activationId immediate annotation message r₁)
    (d₂ : p.ImplicitDispatch h activationId immediate annotation message r₂) :
    r₁ = r₂ := by
  cases d₁ with
  | @classScope target₁ current₁ _ hann₁ immediate₁ outer₁ =>
      cases d₂ with
      | @classScope target₂ current₂ _ hann₂ immediate₂ outer₂ =>
          have htarget : target₁ = target₂ := by
            have heq := hann₁.symm.trans hann₂
            exact ScopeDecl.classDecl.inj (Option.some.inj heq)
          subst target₂
          have hcurrent : current₁ = current₂ := by
            exact Option.some.inj (immediate₁.symm.trans immediate₂)
          subst current₂
          exact outerDispatch_deterministic wf outer₁ outer₂
      | objectLiteralScope hann₂ _ _ _ _ _ =>
          have heq := hann₁.symm.trans hann₂
          simp at heq
      | activationScope hann₂ _ _ _ =>
          have heq := hann₁.symm.trans hann₂
          simp at heq
      | self hann₂ _ _ =>
          rw [hann₁] at hann₂
          contradiction
  | @objectLiteralScope activation₁ declaration₁ receiver₁ receiverClass₁
      definingClass₁ method₁ hann₁ ha₁ hs₁ hc₁ hl₁ _ =>
      cases d₂ with
      | classScope hann₂ _ _ =>
          have heq := hann₁.symm.trans hann₂
          simp at heq
      | @objectLiteralScope activation₂ declaration₂ receiver₂ receiverClass₂
          definingClass₂ method₂ hann₂ ha₂ hs₂ hc₂ hl₂ _ =>
          have hdecl : declaration₁ = declaration₂ := by
            have heq := hann₁.symm.trans hann₂
            exact ScopeDecl.objectLiteralDecl.inj (Option.some.inj heq)
          subst declaration₂
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have hreceiver : receiver₁ = receiver₂ := by
            rw [hs₁] at hs₂
            injection hs₂
          subst receiver₂
          have hclass : receiverClass₁ = receiverClass₂ := by
            rw [hc₁] at hc₂
            injection hc₂
          subst receiverClass₂
          have live := wf.objectClassesAreLive receiver₁ receiverClass₁ hc₁
          have chain := wf.chain_exists live
          have hr := unrestrictedRules_deterministic chain hl₁ hl₂
          have hresult := Option.some.inj hr
          cases hresult
          rfl
      | activationScope hann₂ _ _ _ =>
          have heq := hann₁.symm.trans hann₂
          simp at heq
      | self hann₂ _ _ =>
          rw [hann₁] at hann₂
          contradiction
  | @activationScope activation₁ declaration₁ target₁ _ hann₁ ha₁ hs₁ ordinary₁ =>
      cases d₂ with
      | classScope hann₂ _ _ =>
          have heq := hann₁.symm.trans hann₂
          simp at heq
      | objectLiteralScope hann₂ _ _ _ _ _ =>
          have heq := hann₁.symm.trans hann₂
          simp at heq
      | @activationScope activation₂ declaration₂ target₂ _ hann₂ ha₂ hs₂ ordinary₂ =>
          have hdecl : declaration₁ = declaration₂ := by
            have heq := hann₁.symm.trans hann₂
            exact ScopeDecl.activationDecl.inj (Option.some.inj heq)
          subst declaration₂
          have hactivation : activation₁ = activation₂ := by
            rw [ha₁] at ha₂
            injection ha₂
          subst activation₂
          have htarget : target₁ = target₂ := by
            rw [hs₁] at hs₂
            injection hs₂
          subst target₂
          exact ordinaryDispatch_deterministic wf ordinary₁ ordinary₂
      | self hann₂ _ _ =>
          rw [hann₁] at hann₂
          contradiction
  | @self current₁ _ hann₁ immediate₁ self₁ =>
      cases d₂ with
      | classScope hann₂ _ _ =>
          rw [hann₁] at hann₂
          contradiction
      | objectLiteralScope hann₂ _ _ _ _ _ =>
          rw [hann₁] at hann₂
          contradiction
      | activationScope hann₂ _ _ _ =>
          rw [hann₁] at hann₂
          contradiction
      | @self current₂ _ _ immediate₂ self₂ =>
          have hcurrent : current₁ = current₂ := by
            exact Option.some.inj (immediate₁.symm.trans immediate₂)
          subst current₂
          exact selfDispatch_deterministic wf self₁ self₂

end Program
end Newspeak
