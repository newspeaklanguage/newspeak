import Newspeak.ReflectionDebuggerObservation
import Newspeak.PrologLookupCorrespondence

namespace Newspeak
namespace PrologBridge

inductive PrologSuspendedControlImage :
    ActivationStack → List ResolvedFrameImage → Prop where
  | empty : PrologSuspendedControlImage .empty []
  | push {rest frame images} :
      PrologSuspendedControlImage rest images →
      PrologSuspendedControlImage (.push rest frame)
        (images ++ [⟨frame.activation, .suspendedControl frame.frames⟩])

theorem prologSuspendedControlImage_iff {stack images} :
    PrologSuspendedControlImage stack images ↔
      stack.suspendedControlImage = images := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | push _ ih => simp [ActivationStack.suspendedControlImage, ih]
  · intro equality
    subst images
    induction stack with
    | empty => exact .empty
    | push rest frame ih => exact .push ih

inductive PrologControlImage : ActivationStack → ControlTerm →
    List ResolvedFrameImage → Prop where
  | nonempty {rest frame term images} :
      PrologSuspendedControlImage rest images →
      PrologControlImage (.push rest frame) term
        (images ++ [⟨frame.activation, .activeControl frame.frames term⟩])

theorem prologControlImage_iff {stack term images} :
    PrologControlImage stack term images ↔ stack.controlImage? term = some images := by
  constructor
  · rintro ⟨suspended⟩
    simp [ActivationStack.controlImage?, prologSuspendedControlImage_iff.mp suspended]
  · intro result
    cases stack with
    | empty => simp [ActivationStack.controlImage?] at result
    | push rest frame =>
        simp [ActivationStack.controlImage?] at result
        subst images
        exact .nonempty (prologSuspendedControlImage_iff.mpr rfl)

inductive PrologReifyDebugFrames (heap : Heap) :
    List ResolvedFrameImage → List DebugFrameImage → Prop where
  | empty : PrologReifyDebugFrames heap [] []
  | step {image remaining definition tail} :
      heap.activations image.activation = some definition →
      PrologReifyDebugFrames heap remaining tail →
      PrologReifyDebugFrames heap (image :: remaining)
        (⟨image.activation, definition, image.control⟩ :: tail)

theorem prologReifyDebugFrames_iff {heap images frames} :
    PrologReifyDebugFrames heap images frames ↔
      reifyDebugFrames heap images = some frames := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | step lookup _ ih => simp [reifyDebugFrames, lookup, ih]
  · intro result
    induction images generalizing frames with
    | nil =>
        simp [reifyDebugFrames] at result
        subst frames
        exact .empty
    | cons image remaining ih =>
        cases lookup : heap.activations image.activation with
        | none => simp [reifyDebugFrames, lookup] at result
        | some definition =>
            cases tailResult : reifyDebugFrames heap remaining with
            | none => simp [reifyDebugFrames, lookup, tailResult] at result
            | some tail =>
                simp [reifyDebugFrames, lookup, tailResult] at result
                subst frames
                exact .step lookup (ih tailResult)

inductive PrologActorStackSnapshot (world : ActorWorld) (actor : ActorId) :
    ActorStackSnapshot → Prop where
  | running {config reply event controls frames} :
      world.runStates actor = some (.runningTurn config reply event) →
      PrologControlImage config.stack config.control controls →
      PrologReifyDebugFrames config.allocation.heap controls frames →
      PrologActorStackSnapshot world actor ⟨.running, frames⟩
  | paused {config reply event token reason controls frames} :
      world.runStates actor = some (.pausedTurn config reply event token reason) →
      PrologControlImage config.stack config.control controls →
      PrologReifyDebugFrames config.allocation.heap controls frames →
      PrologActorStackSnapshot world actor ⟨.paused token reason, frames⟩

theorem prologActorStackSnapshot_iff {world actor snapshot} :
    PrologActorStackSnapshot world actor snapshot ↔
      world.actorStackSnapshot? actor = some snapshot := by
  constructor
  · intro derivation
    cases derivation with
    | running state controls frames | paused state controls frames =>
        simp [ActorWorld.actorStackSnapshot?, state,
          prologControlImage_iff.mp controls, prologReifyDebugFrames_iff.mp frames]
  · intro result
    unfold ActorWorld.actorStackSnapshot? at result
    cases stateResult : world.runStates actor with
    | none => simp [stateResult] at result
    | some state =>
        cases state with
        | idle => simp [stateResult] at result
        | runningTurn config reply event =>
            cases controlsResult : config.stack.controlImage? config.control with
            | none => simp [stateResult, controlsResult] at result
            | some controls =>
                cases framesResult : reifyDebugFrames config.allocation.heap controls with
                | none => simp [stateResult, controlsResult, framesResult] at result
                | some frames =>
                    simp [stateResult, controlsResult, framesResult] at result
                    subst snapshot
                    exact .running stateResult
                      (prologControlImage_iff.mpr controlsResult)
                      (prologReifyDebugFrames_iff.mpr framesResult)
        | pausedTurn config reply event token reason =>
            cases controlsResult : config.stack.controlImage? config.control with
            | none => simp [stateResult, controlsResult] at result
            | some controls =>
                cases framesResult : reifyDebugFrames config.allocation.heap controls with
                | none => simp [stateResult, controlsResult, framesResult] at result
                | some frames =>
                    simp [stateResult, controlsResult, framesResult] at result
                    subst snapshot
                    exact .paused stateResult
                      (prologControlImage_iff.mpr controlsResult)
                      (prologReifyDebugFrames_iff.mpr framesResult)

inductive PrologLiveActivationControl (world : ActorWorld)
    (activation : ActivationId) : FrameControl → Prop where
  | found {control} :
      world.liveActivationControl? activation = some control →
      PrologLiveActivationControl world activation control

theorem prologLiveActivationControl_iff {world activation control} :
    PrologLiveActivationControl world activation control ↔
      world.liveActivationControl? activation = some control := by
  constructor
  · rintro ⟨result⟩; exact result
  · exact .found

inductive PrologDebugActivationDescriptor (world : ActorWorld)
    (activation : ActivationId) : ActorWorld.DebugActivationDescriptor → Prop where
  | describe {location heap definition} :
      world.locateActivationId activation = some location →
      world.heapAt location = some heap →
      heap.activations activation = some definition →
      PrologDebugActivationDescriptor world activation
        ⟨⟨location, definition⟩, world.liveActivationControl? activation⟩

theorem prologDebugActivationDescriptor_iff {world activation descriptor} :
    PrologDebugActivationDescriptor world activation descriptor ↔
      world.describeDebugActivation? activation = some descriptor := by
  constructor
  · rintro ⟨location, heap, definition⟩
    simp [ActorWorld.describeDebugActivation?, location, heap, definition]
  · intro result
    unfold ActorWorld.describeDebugActivation? at result
    cases location : world.locateActivationId activation with
    | none => simp [location] at result
    | some place =>
        cases heapResult : world.heapAt place with
        | none => simp [location, heapResult] at result
        | some heap =>
            cases definitionResult : heap.activations activation with
            | none => simp [location, heapResult, definitionResult] at result
            | some definition =>
                simp [location, heapResult, definitionResult] at result
                subst descriptor
                exact .describe location heapResult definitionResult

end PrologBridge
end Newspeak
