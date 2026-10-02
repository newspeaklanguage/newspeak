import Newspeak.RuntimeRoots

namespace Newspeak

/-- A collection transition whose roots are computed from its source state.
    Unlike `GarbageCollectionStep`, this is the closed machine operation: its
    caller supplies only opaque host/VM handles. -/
inductive RuntimeGarbageCollectionStep (p : Program)
    (externalRoots : List ObjRef) : SequentialConfig → SequentialConfig → Prop where
  | collect (before : SequentialConfig) :
      RuntimeGarbageCollectionStep p externalRoots before
        (before.collectGarbageFromRuntimeRoots p externalRoots)

theorem RuntimeGarbageCollectionStep.preserves_sequentialWellFormed
    {p : Program} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (wf : Program.SequentialWellFormed p before)
    (step : RuntimeGarbageCollectionStep p externalRoots before after) :
    Program.SequentialWellFormed p after := by
  cases step
  exact wf.collectGarbageFromRuntimeRoots_wellFormed externalRoots

theorem RuntimeGarbageCollectionStep.establishes_weakContainersWellFormed
    {p : Program} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (nilLive : before.allocation.heap.IsLiveObject p.nilObject)
    (step : RuntimeGarbageCollectionStep p externalRoots before after) :
    Heap.WeakContainersWellFormed after.allocation.heap := by
  cases step
  exact p.collectGarbageFromRuntimeRoots_weakContainersWellFormed
    nilLive externalRoots

theorem RuntimeGarbageCollectionStep.is_collectionStutter
    {p : Program} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (step : RuntimeGarbageCollectionStep p externalRoots before after) :
    CollectionStutter before after
      (sequentialRuntimeRootReferences p before externalRoots) := by
  cases step
  exact GarbageCollectionStep.is_collectionStutter (.collect before)

/-- The top-level sequential semantics with closed, state-derived collection
    safe points. -/
inductive SequentialStepWithRuntimeCollection (p : Program)
    (reifier : ErrorReifier p) (externalRoots : List ObjRef) :
    SequentialConfig → SequentialConfig → Prop where
  | ordinary {before after : SequentialConfig} :
      p.SequentialStepWithTopLevel reifier before after →
      SequentialStepWithRuntimeCollection p reifier externalRoots before after
  | collection {before after : SequentialConfig} :
      RuntimeGarbageCollectionStep p externalRoots before after →
      SequentialStepWithRuntimeCollection p reifier externalRoots before after

theorem SequentialStepWithRuntimeCollection.preserves_sequentialWellFormed
    {p : Program} {reifier : ErrorReifier p} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (wf : Program.SequentialWellFormed p before)
    (step : SequentialStepWithRuntimeCollection p reifier externalRoots
      before after) :
    Program.SequentialWellFormed p after := by
  cases step with
  | ordinary ordinary =>
      exact Program.sequentialStepWithTopLevel_preserves_wellFormed wf ordinary
  | collection collection =>
      exact collection.preserves_sequentialWellFormed wf

/-- Finite reflexive-transitive closure of the collecting machine. -/
inductive SequentialExecutionWithRuntimeCollection (p : Program)
    (reifier : ErrorReifier p) (externalRoots : List ObjRef) :
    SequentialConfig → SequentialConfig → Prop where
  | refl (config : SequentialConfig) :
      SequentialExecutionWithRuntimeCollection p reifier externalRoots
        config config
  | next {before middle after : SequentialConfig} :
      SequentialStepWithRuntimeCollection p reifier externalRoots
        before middle →
      SequentialExecutionWithRuntimeCollection p reifier externalRoots
        middle after →
      SequentialExecutionWithRuntimeCollection p reifier externalRoots
        before after

theorem SequentialExecutionWithRuntimeCollection.single
    {p : Program} {reifier : ErrorReifier p} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (step : SequentialStepWithRuntimeCollection p reifier externalRoots
      before after) :
    SequentialExecutionWithRuntimeCollection p reifier externalRoots
      before after :=
  .next step (.refl after)

theorem SequentialExecutionWithRuntimeCollection.trans
    {p : Program} {reifier : ErrorReifier p} {externalRoots : List ObjRef}
    {before middle after : SequentialConfig}
    (first : SequentialExecutionWithRuntimeCollection p reifier externalRoots
      before middle)
    (second : SequentialExecutionWithRuntimeCollection p reifier externalRoots
      middle after) :
    SequentialExecutionWithRuntimeCollection p reifier externalRoots
      before after := by
  induction first with
  | refl => exact second
  | next step remaining ih => exact .next step (ih second)

theorem SequentialExecutionWithRuntimeCollection.preserves_sequentialWellFormed
    {p : Program} {reifier : ErrorReifier p} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (wf : Program.SequentialWellFormed p before)
    (execution : SequentialExecutionWithRuntimeCollection p reifier
      externalRoots before after) :
    Program.SequentialWellFormed p after := by
  induction execution with
  | refl => exact wf
  | next step remaining ih =>
      exact ih (step.preserves_sequentialWellFormed wf)

/-- A finite trace after classifying every transition as either an exact base
    step or a GC stutter.  The roots recorded by a stutter are those extracted
    from that transition's source state, not a trace-global approximation. -/
inductive RuntimeCollectionSimulationTrace (p : Program)
    (reifier : ErrorReifier p) (externalRoots : List ObjRef) :
    SequentialConfig → SequentialConfig → Prop where
  | refl (config : SequentialConfig) :
      RuntimeCollectionSimulationTrace p reifier externalRoots config config
  | base {before middle after : SequentialConfig} :
      p.SequentialStepWithTopLevel reifier before middle →
      RuntimeCollectionSimulationTrace p reifier externalRoots middle after →
      RuntimeCollectionSimulationTrace p reifier externalRoots before after
  | stutter {before middle after : SequentialConfig} :
      CollectionStutter before middle
        (sequentialRuntimeRootReferences p before externalRoots) →
      RuntimeCollectionSimulationTrace p reifier externalRoots middle after →
      RuntimeCollectionSimulationTrace p reifier externalRoots before after

/-- M10, finite form: every finite execution of the machine with automatic
    collection has an equally long classification trace consisting solely of
    exact base transitions and state-derived collection stutters. -/
theorem SequentialExecutionWithRuntimeCollection.refines_base_with_stutters
    {p : Program} {reifier : ErrorReifier p} {externalRoots : List ObjRef}
    {before after : SequentialConfig}
    (execution : SequentialExecutionWithRuntimeCollection p reifier
      externalRoots before after) :
    RuntimeCollectionSimulationTrace p reifier externalRoots before after := by
  induction execution with
  | refl => exact .refl _
  | next step remaining ih =>
      cases step with
      | ordinary ordinary => exact .base ordinary ih
      | collection collection =>
          exact .stutter collection.is_collectionStutter ih

end Newspeak
