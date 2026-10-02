import Newspeak.ObjectLiteralsAndNestedClasses

namespace Newspeak

def signalSelector : Selector := ⟨"signal"⟩

def signalMessage : Message := ⟨signalSelector, []⟩

/-- Pointwise extension of every currently modeled heap store.  Error
    reification may allocate exception and diagnostic records, but cannot
    replace a record that already existed at the failure point. -/
structure HeapExtension (before after : Heap) : Prop where
  classes : ∀ id value, before.classes id = some value →
    after.classes id = some value
  objects : ∀ id value, before.objects id = some value →
    after.objects id = some value
  mixinObjects : ∀ id value, before.mixinObjects id = some value →
    after.mixinObjects id = some value
  activations : ∀ id value, before.activations id = some value →
    after.activations id = some value
  closures : ∀ id value, before.closures id = some value →
    after.closures id = some value
  mirrors : ∀ id value, before.mirrors id = some value →
    after.mirrors id = some value
  actors : ∀ id value, before.actors id = some value →
    after.actors id = some value

/-- The VM/platform part of the exception-library boundary.  It is a total,
    deterministic meta-level allocation operation, not a user-code callback.
    Its laws state the obligations imposed by Section 8.6: old records remain
    unchanged, heap coherence and fresh supplies survive, and the resulting
    near object has an ordinary public `signal` method. -/
structure ErrorReifier (p : Program) where
  reify : AllocationState → RuntimeError → AllocationState × ObjRef
  heapExtension : ∀ state error,
    HeapExtension state.heap (reify state error).1.heap
  preservesWellFormed : ∀ state error, p.WellFormed state.heap →
    p.WellFormed (reify state error).1.heap
  preservesSupplies : ∀ state error, state.SuppliesFresh →
    (reify state error).1.SuppliesFresh
  signalDispatch : ∀ state error,
    ∃ method definingClass,
      p.OrdinaryDispatch (reify state error).1.heap (reify state error).2
        signalMessage
        (.invoke method (reify state error).2 definingClass signalMessage)

namespace Program

/-- Runtime failures and abrupt internal throws cross the same library
    boundary.  Reification leaves the activation and evaluation stacks
    untouched; subsequent handling, passing, returning, or resumption is
    therefore ordinary Newspeak/library execution. -/
inductive ExceptionBoundaryStep (p : Program) (reifier : ErrorReifier p) :
    SequentialConfig → SequentialConfig → Prop where
  | runtimeError {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {error : RuntimeError} :
      ExceptionBoundaryStep p reifier
        ⟨state, .push rest ⟨current, frames⟩, .runtimeError error⟩
        ⟨(reifier.reify state error).1, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary (reifier.reify state error).2) signalMessage⟩
  | thrown {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {error : RuntimeError} :
      ExceptionBoundaryStep p reifier
        ⟨state, .push rest ⟨current, frames⟩, .throw error⟩
        ⟨(reifier.reify state error).1, .push rest ⟨current, frames⟩,
          .dispatch (.ordinary (reifier.reify state error).2) signalMessage⟩

theorem exceptionBoundaryStep_deterministic {p : Program}
    {reifier : ErrorReifier p} {before after₁ after₂ : SequentialConfig}
    (step₁ : p.ExceptionBoundaryStep reifier before after₁)
    (step₂ : p.ExceptionBoundaryStep reifier before after₂) :
    after₁ = after₂ := by
  cases step₁ <;> cases step₂ <;> rfl

theorem exceptionBoundaryStep_preserves_wellFormed {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (wf : SequentialWellFormed p before)
    (step : p.ExceptionBoundaryStep reifier before after) :
    SequentialWellFormed p after := by
  cases step with
  | @runtimeError state rest current frames error =>
      exact ⟨reifier.preservesWellFormed state error wf.heap,
        reifier.preservesSupplies state error wf.supplies,
        stackLive_transport wf.stack (fun id activation live =>
          ⟨activation, reifier.heapExtension state error |>.activations id
            activation live⟩), trivial⟩
  | @thrown state rest current frames error =>
      exact ⟨reifier.preservesWellFormed state error wf.heap,
        reifier.preservesSupplies state error wf.supplies,
        stackLive_transport wf.stack (fun id activation live =>
          ⟨activation, reifier.heapExtension state error |>.activations id
            activation live⟩), trivial⟩

theorem exceptionBoundaryStep_preserves_stack {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (step : p.ExceptionBoundaryStep reifier before after) :
    after.stack = before.stack := by
  cases step <;> rfl

theorem exceptionBoundaryStep_has_public_signal_dispatch {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (step : p.ExceptionBoundaryStep reifier before after) :
    ∃ error exception method definingClass,
      after.allocation = (reifier.reify before.allocation error).1 ∧
      exception = (reifier.reify before.allocation error).2 ∧
      after.control = .dispatch (.ordinary exception) signalMessage ∧
      p.OrdinaryDispatch after.allocation.heap exception signalMessage
        (.invoke method exception definingClass signalMessage) := by
  cases step with
  | @runtimeError state rest current frames error =>
      rcases reifier.signalDispatch state error with ⟨method, classId, dispatch⟩
      exact ⟨error, (reifier.reify state error).2, method, classId,
        rfl, rfl, rfl, dispatch⟩
  | @thrown state rest current frames error =>
      rcases reifier.signalDispatch state error with ⟨method, classId, dispatch⟩
      exact ⟨error, (reifier.reify state error).2, method, classId,
        rfl, rfl, rfl, dispatch⟩

/-- Reification is observationally the same boundary for both internal error
    controls: only the input control constructor differs. -/
theorem runtimeError_and_throw_reify_identically (p : Program)
    (reifier : ErrorReifier p) (state : AllocationState)
    (error : RuntimeError) :
    let runtimeResult := reifier.reify state error
    let throwResult := reifier.reify state error
    runtimeResult = throwResult := by
  rfl

theorem sequentialStep_exceptionBoundary_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before sequentialAfter boundaryAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (boundary : p.ExceptionBoundaryStep reifier before boundaryAfter) : False := by
  cases boundary <;> cases sequential with
  | expression expression => cases expression
  | request request => cases request
  | invocation invocation => cases invocation
  | body body =>
      cases body with
      | graph next => simp [bodyMachineNext] at next
  | returns returns =>
      cases returns with
      | graph next => simp [returnMachineNext] at next
  | closure closure =>
      cases closure with
      | creation creation => cases creation
      | dispatch dispatch => cases dispatch
      | invocation invocation => cases invocation
  | objectSlots slots => cases slots
  | classes classes => cases classes
  | messages messages => cases messages

theorem instanceInitializationStep_exceptionBoundary_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before initializationAfter boundaryAfter : SequentialConfig}
    (initialization : p.InstanceInitializationStep before initializationAfter)
    (boundary : p.ExceptionBoundaryStep reifier before boundaryAfter) : False := by
  cases boundary <;> cases initialization with
  | factory factory => cases factory
  | coordinator coordinator =>
      cases coordinator with
      | graph next => simp [initializationCoordinatorNext] at next
  | slots slots =>
      cases slots with
      | graph next => simp [slotInitializationNext] at next

theorem objectAndNestedClassStep_exceptionBoundary_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before objectAfter boundaryAfter : SequentialConfig}
    (objects : p.ObjectAndNestedClassStep before objectAfter)
    (boundary : p.ExceptionBoundaryStep reifier before boundaryAfter) : False := by
  cases boundary <;> cases objects with
  | objectLiteral objectLiteral => cases objectLiteral
  | nestedClass nestedClass => cases nestedClass

theorem sequentialStepWithObjects_exceptionBoundary_disjoint {p : Program}
    {reifier : ErrorReifier p}
    {before sequentialAfter boundaryAfter : SequentialConfig}
    (sequential : p.SequentialStepWithObjects before sequentialAfter)
    (boundary : p.ExceptionBoundaryStep reifier before boundaryAfter) : False := by
  cases sequential with
  | prior prior =>
      cases prior with
      | prior sequential =>
          exact sequentialStep_exceptionBoundary_disjoint sequential boundary
      | initialization initialization =>
          exact instanceInitializationStep_exceptionBoundary_disjoint
            initialization boundary
  | objects objects =>
      exact objectAndNestedClassStep_exceptionBoundary_disjoint objects boundary

/-- Sequential execution through the exception-library boundary. -/
inductive SequentialStepWithExceptions (p : Program)
    (reifier : ErrorReifier p) : SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      p.SequentialStepWithObjects before after →
        p.SequentialStepWithExceptions reifier before after
  | exception {before after : SequentialConfig} :
      p.ExceptionBoundaryStep reifier before after →
        p.SequentialStepWithExceptions reifier before after

theorem sequentialStepWithExceptions_deterministic {p : Program}
    {reifier : ErrorReifier p} {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (step₁ : p.SequentialStepWithExceptions reifier before after₁)
    (step₂ : p.SequentialStepWithExceptions reifier before after₂) :
    after₁ = after₂ := by
  cases step₁ with
  | prior prior₁ =>
      cases step₂ with
      | prior prior₂ =>
          exact sequentialStepWithObjects_deterministic wf prior₁ prior₂
      | exception exception₂ =>
          exact (sequentialStepWithObjects_exceptionBoundary_disjoint
            prior₁ exception₂).elim
  | exception exception₁ =>
      cases step₂ with
      | prior prior₂ =>
          exact (sequentialStepWithObjects_exceptionBoundary_disjoint
            prior₂ exception₁).elim
      | exception exception₂ =>
          exact exceptionBoundaryStep_deterministic exception₁ exception₂

theorem sequentialStepWithExceptions_preserves_wellFormed {p : Program}
    {reifier : ErrorReifier p} {before after : SequentialConfig}
    (wf : SequentialWellFormed p before)
    (step : p.SequentialStepWithExceptions reifier before after) :
    SequentialWellFormed p after := by
  cases step with
  | prior prior => exact sequentialStepWithObjects_preserves_wellFormed wf prior
  | exception exception =>
      exact exceptionBoundaryStep_preserves_wellFormed wf exception

end Program
end Newspeak
