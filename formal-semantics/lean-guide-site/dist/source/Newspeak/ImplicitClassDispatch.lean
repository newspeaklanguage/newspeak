import Newspeak.OuterDispatch

namespace Newspeak
namespace Program

/-- Class-scope portion of elaborated implicit dispatch after nearer activation
    and object-literal scopes have been ruled out. -/
inductive ElaboratedClassDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (site : SiteId) (immediate : ClassDeclId)
    (message : Message) : DispatchResult → Prop where
  | bound {target : ClassDeclId} {result : DispatchResult} :
      p.bindClass? site message.selector = some target →
      p.OuterDispatch h activationId target immediate message result →
      ElaboratedClassDispatch p h activationId site immediate message result
  | self {result : DispatchResult} :
      p.bindClass? site message.selector = none →
      p.SelfDispatch h activationId immediate message result →
      ElaboratedClassDispatch p h activationId site immediate message result

/-- ECOOP-style presentation of the same class-scope dispatch. -/
inductive ScannedClassDispatch (p : Program) (h : Heap)
    (activationId : ActivationId) (site : SiteId) (immediate : ClassDeclId)
    (message : Message) : DispatchResult → Prop where
  | bound {target : ClassDeclId} {result : DispatchResult} :
      p.ClassScan immediate message.selector (some target) →
      p.OuterDispatch h activationId target immediate message result →
      ScannedClassDispatch p h activationId site immediate message result
  | self {result : DispatchResult} :
      p.ClassScan immediate message.selector none →
      p.SelfDispatch h activationId immediate message result →
      ScannedClassDispatch p h activationId site immediate message result

/-- Full dynamic consequence of Equation (6.9) for the class-only portion of
    implicit dispatch: both presentations derive exactly the same result. -/
theorem implicitClassDispatch_equivalence {p : Program} {h : Heap}
    {activationId : ActivationId} {site : SiteId} {immediate : ClassDeclId}
    {message : Message} {result : DispatchResult}
    (context : p.ClassBindingContext site message.selector immediate) :
    p.ElaboratedClassDispatch h activationId site immediate message result ↔
      p.ScannedClassDispatch h activationId site immediate message result := by
  constructor
  · intro dispatch
    cases dispatch with
    | bound hbind outer =>
        exact .bound ((binding_equivalence_result context).mp hbind) outer
    | self hbind selfDispatch =>
        exact .self ((binding_equivalence_result context).mp hbind) selfDispatch
  · intro dispatch
    cases dispatch with
    | bound hscan outer =>
        exact .bound ((binding_equivalence_result context).mpr hscan) outer
    | self hscan selfDispatch =>
        exact .self ((binding_equivalence_result context).mpr hscan) selfDispatch

theorem elaboratedClassDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId} {site : SiteId}
    {immediate : ClassDeclId} {message : Message} {r₁ r₂ : DispatchResult}
    (d₁ : p.ElaboratedClassDispatch h activationId site immediate message r₁)
    (d₂ : p.ElaboratedClassDispatch h activationId site immediate message r₂) :
    r₁ = r₂ := by
  cases d₁ with
  | @bound target₁ _ hbind₁ outer₁ =>
      cases d₂ with
      | @bound target₂ _ hbind₂ outer₂ =>
          have htarget : target₁ = target₂ := by
            rw [hbind₁] at hbind₂
            injection hbind₂
          subst target₂
          exact outerDispatch_deterministic wf outer₁ outer₂
      | self hnone _ =>
          rw [hbind₁] at hnone
          contradiction
  | self hnone₁ self₁ =>
      cases d₂ with
      | bound hbind₂ _ =>
          rw [hnone₁] at hbind₂
          contradiction
      | self _ self₂ =>
          exact selfDispatch_deterministic wf self₁ self₂

theorem scannedClassDispatch_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId} {site : SiteId}
    {immediate : ClassDeclId} {message : Message} {r₁ r₂ : DispatchResult}
    (context : p.ClassBindingContext site message.selector immediate)
    (d₁ : p.ScannedClassDispatch h activationId site immediate message r₁)
    (d₂ : p.ScannedClassDispatch h activationId site immediate message r₂) :
    r₁ = r₂ :=
  elaboratedClassDispatch_deterministic wf
    ((implicitClassDispatch_equivalence context).mpr d₁)
    ((implicitClassDispatch_equivalence context).mpr d₂)

end Program
end Newspeak
