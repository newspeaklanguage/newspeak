import Newspeak.OrdinarySend

namespace Newspeak

/-- Dispatch authority after an ordinary receiver (if any) has been evaluated.
    The fields are precisely the annotations retained by elaboration. -/
inductive SendRequest where
  | ordinary (receiver : ObjRef)
  | eventual (receiver : ObjRef)
  | implicit (annotation : Option ScopeDecl) (immediate : Option ClassDeclId)
  | outer (target immediate : ClassDeclId)
  | self (immediate : ClassDeclId)
  | super
deriving Repr, DecidableEq, BEq

/-- Selector used by a closure with the given number of parameters. -/
def valueSelector : Nat → Selector
  | 0 => ⟨"value"⟩
  | n + 1 => ⟨String.join (List.replicate (n + 1) "value:")⟩

/-- The ordinary-request exception for direct closure invocation. -/
def Heap.ClosureCall (h : Heap) (receiver : ObjRef)
    (message : Message) : Prop :=
  ∃ id closure,
    receiver = .closureObject id ∧
    h.closures id = some closure ∧
    message.selector = valueSelector closure.parameters.length ∧
    message.arguments.length = closure.parameters.length

namespace Program

/-- Relational form of request resolution (Equation 8.6 in the prose
    semantics).  Closure-value requests are deliberately excluded from the
    ordinary branch and have their own machine transition. -/
inductive ResolveRequest (p : Program) (h : Heap)
    (activationId : ActivationId) :
    SendRequest → Message → DispatchResult → Prop where
  | ordinary {receiver : ObjRef} {message : Message} {result : DispatchResult} :
      ¬h.ClosureCall receiver message →
      p.OrdinaryDispatch h receiver message result →
      ResolveRequest p h activationId (.ordinary receiver) message result
  | implicit {annotation : Option ScopeDecl} {immediate : Option ClassDeclId}
      {message : Message} {result : DispatchResult} :
      p.ImplicitDispatch h activationId immediate annotation message result →
      ResolveRequest p h activationId (.implicit annotation immediate)
        message result
  | outer {target immediate : ClassDeclId} {message : Message}
      {result : DispatchResult} :
      p.OuterDispatch h activationId target immediate message result →
      ResolveRequest p h activationId (.outer target immediate) message result
  | self {immediate : ClassDeclId} {message : Message}
      {result : DispatchResult} :
      p.SelfDispatch h activationId immediate message result →
      ResolveRequest p h activationId (.self immediate) message result
  | super {message : Message} {result : DispatchResult} :
      p.SuperDispatch h activationId message result →
      ResolveRequest p h activationId .super message result

theorem resolveOrdinary_notClosureCall {p : Program} {h : Heap}
    {activationId : ActivationId} {receiver : ObjRef} {message : Message}
    {result : DispatchResult}
    (resolution : p.ResolveRequest h activationId (.ordinary receiver)
      message result) :
    ¬h.ClosureCall receiver message := by
  cases resolution with
  | ordinary notClosure _ => exact notClosure

theorem resolveRequest_deterministic {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {request : SendRequest} {message : Message} {result₁ result₂ : DispatchResult}
    (resolution₁ : p.ResolveRequest h activationId request message result₁)
    (resolution₂ : p.ResolveRequest h activationId request message result₂) :
    result₁ = result₂ := by
  cases resolution₁ with
  | ordinary _ dispatch₁ =>
      cases resolution₂ with
      | ordinary _ dispatch₂ =>
          exact ordinaryDispatch_deterministic wf dispatch₁ dispatch₂
  | implicit dispatch₁ =>
      cases resolution₂ with
      | implicit dispatch₂ =>
          exact implicitDispatch_deterministic wf dispatch₁ dispatch₂
  | outer dispatch₁ =>
      cases resolution₂ with
      | outer dispatch₂ =>
          exact outerDispatch_deterministic wf dispatch₁ dispatch₂
  | self dispatch₁ =>
      cases resolution₂ with
      | self dispatch₂ =>
          exact selfDispatch_deterministic wf dispatch₁ dispatch₂
  | super dispatch₁ =>
      cases resolution₂ with
      | super dispatch₂ =>
          exact superDispatch_deterministic wf dispatch₁ dispatch₂

/-- Request resolution followed by the unique DNU fallback when, and only
    when, resolution produced `missing`.  This relation contains exactly one
    DNU premise in its sole missing constructor. -/
inductive CompleteRequest (p : Program) (state : AllocationState)
    (activationId : ActivationId) (request : SendRequest) (message : Message) :
    AllocationState → DispatchResult → Prop where
  | invoke {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
      (resolution : p.ResolveRequest state.heap activationId request message
        (.invoke method receiver definingClass message)) :
      CompleteRequest p state activationId request message state
        (.invoke method receiver definingClass message)
  | invalidSuper {currentClass : ClassId}
      (resolution : p.ResolveRequest state.heap activationId request message
        (.invalidSuper currentClass)) :
      CompleteRequest p state activationId request message state
        (.invalidSuper currentClass)
  | dnu {receiver : ObjRef} {lookupStart : ClassId}
      {nextState : AllocationState} {result : DispatchResult}
      (resolution : p.ResolveRequest state.heap activationId request message
        (.missing receiver lookupStart message))
      (hasChain : ∃ chain, p.ClassChain state.heap lookupStart chain)
      (fallback : p.DnuFallback state receiver lookupStart message
        nextState result) :
      CompleteRequest p state activationId request message nextState result

theorem completeOrdinary_notClosureCall {p : Program}
    {state : AllocationState} {activationId : ActivationId}
    {receiver : ObjRef} {message : Message} {nextState : AllocationState}
    {result : DispatchResult}
    (completion : p.CompleteRequest state activationId (.ordinary receiver)
      message nextState result) :
    ¬state.heap.ClosureCall receiver message := by
  cases completion with
  | invoke resolution => exact resolveOrdinary_notClosureCall resolution
  | invalidSuper resolution => exact resolveOrdinary_notClosureCall resolution
  | dnu resolution _ _ => exact resolveOrdinary_notClosureCall resolution

theorem completeRequest_deterministic {p : Program} {state : AllocationState}
    (wf : p.WellFormed state.heap) {activationId : ActivationId}
    {request : SendRequest} {message : Message}
    {state₁ state₂ : AllocationState} {result₁ result₂ : DispatchResult}
    (completion₁ : p.CompleteRequest state activationId request message
      state₁ result₁)
    (completion₂ : p.CompleteRequest state activationId request message
      state₂ result₂) :
    state₁ = state₂ ∧ result₁ = result₂ := by
  cases completion₁ with
  | invoke resolution₁ =>
      cases completion₂ with
      | invoke resolution₂ =>
          exact ⟨rfl, resolveRequest_deterministic wf resolution₁ resolution₂⟩
      | invalidSuper resolution₂ =>
          have impossible := resolveRequest_deterministic wf resolution₁ resolution₂
          contradiction
      | dnu resolution₂ _ _ =>
          have impossible := resolveRequest_deterministic wf resolution₁ resolution₂
          contradiction
  | invalidSuper resolution₁ =>
      cases completion₂ with
      | invoke resolution₂ =>
          have impossible := resolveRequest_deterministic wf resolution₁ resolution₂
          contradiction
      | invalidSuper resolution₂ =>
          exact ⟨rfl, resolveRequest_deterministic wf resolution₁ resolution₂⟩
      | dnu resolution₂ _ _ =>
          have impossible := resolveRequest_deterministic wf resolution₁ resolution₂
          contradiction
  | dnu resolution₁ hasChain₁ fallback₁ =>
      cases completion₂ with
      | invoke resolution₂ =>
          have impossible := resolveRequest_deterministic wf resolution₁ resolution₂
          contradiction
      | invalidSuper resolution₂ =>
          have impossible := resolveRequest_deterministic wf resolution₁ resolution₂
          contradiction
      | dnu resolution₂ _ fallback₂ =>
          have hmissing := resolveRequest_deterministic wf resolution₁ resolution₂
          have hparts := DispatchResult.missing.inj hmissing
          rcases hparts with ⟨hreceiver, hstart, _⟩
          subst hreceiver
          subst hstart
          exact dnuFallback_deterministic hasChain₁ fallback₁ fallback₂

end Program
end Newspeak
