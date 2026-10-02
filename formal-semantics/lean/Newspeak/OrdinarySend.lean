import Newspeak.DnuFallback

namespace Newspeak
namespace Program

/-- An ordinary send either invokes its selected method immediately, or its
    single `missing` result is consumed by exactly one DNU fallback. -/
inductive OrdinarySend (p : Program) (state : AllocationState)
    (receiver : ObjRef) (message : Message) :
    AllocationState → DispatchResult → Prop where
  | invoke {method : MethodDef} {definingClass : ClassId}
      (dispatch : p.OrdinaryDispatch state.heap receiver message
        (.invoke method receiver definingClass message)) :
      OrdinarySend p state receiver message state
        (.invoke method receiver definingClass message)
  | dnu {lookupStart : ClassId} {nextState : AllocationState}
      {result : DispatchResult}
      (dispatch : p.OrdinaryDispatch state.heap receiver message
        (.missing receiver lookupStart message))
      (fallback : p.DnuFallback state receiver lookupStart message
        nextState result) :
      OrdinarySend p state receiver message nextState result

theorem ordinaryMissing_hasChain {p : Program} {state : AllocationState}
    (wf : p.WellFormed state.heap) {receiver : ObjRef} {message : Message}
    {lookupStart : ClassId}
    (dispatch : p.OrdinaryDispatch state.heap receiver message
      (.missing receiver lookupStart message)) :
    ∃ chain, p.ClassChain state.heap lookupStart chain := by
  cases dispatch with
  | missing hclass _ =>
      exact wf.chain_exists
        (wf.objectClassesAreLive receiver lookupStart hclass)

theorem ordinarySend_deterministic {p : Program} {state : AllocationState}
    (wf : p.WellFormed state.heap) {receiver : ObjRef} {message : Message}
    {state₁ state₂ : AllocationState} {result₁ result₂ : DispatchResult}
    (send₁ : p.OrdinarySend state receiver message state₁ result₁)
    (send₂ : p.OrdinarySend state receiver message state₂ result₂) :
    state₁ = state₂ ∧ result₁ = result₂ := by
  cases send₁ with
  | invoke dispatch₁ =>
      cases send₂ with
      | invoke dispatch₂ =>
          exact ⟨rfl, ordinaryDispatch_deterministic wf dispatch₁ dispatch₂⟩
      | dnu dispatch₂ _ =>
          have impossible := ordinaryDispatch_deterministic wf dispatch₁ dispatch₂
          contradiction
  | dnu dispatch₁ fallback₁ =>
      cases send₂ with
      | invoke dispatch₂ =>
          have impossible := ordinaryDispatch_deterministic wf dispatch₁ dispatch₂
          contradiction
      | dnu dispatch₂ fallback₂ =>
          have hmissing := ordinaryDispatch_deterministic wf dispatch₁ dispatch₂
          have hstart : _ := DispatchResult.missing.inj hmissing
          rcases hstart with ⟨_, hlookupStart, _⟩
          subst hlookupStart
          exact dnuFallback_deterministic
            (ordinaryMissing_hasChain wf dispatch₁) fallback₁ fallback₂

end Program
end Newspeak
