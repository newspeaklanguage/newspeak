import Newspeak.ReflectionCurrentActivation
import Newspeak.ReflectionStackImages

/-! # Prolog correspondence for debugger observations

These relations are the direct Horn-clause readings of the debugger
observation equations.  The theorems show that the clauses neither add nor
omit any successful result of the executable Lean definitions.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologCurrentActorActivation (world : ActorWorld)
    (actor : ActorId) : ActivationId → Prop where
  | running {config : SequentialConfig} {reply : PromiseId} {event : EventId}
      {rest : ActivationStack} {frame : ActivationFrame} :
      world.runStates actor = some (.runningTurn config reply event) →
      config.stack = .push rest frame →
      PrologCurrentActorActivation world actor frame.activation
  | paused {config : SequentialConfig} {reply : PromiseId} {event : EventId}
      {token : PauseTokenId} {reason : DebuggerStopReason}
      {rest : ActivationStack} {frame : ActivationFrame} :
      world.runStates actor = some
        (.pausedTurn config reply event token reason) →
      config.stack = .push rest frame →
      PrologCurrentActorActivation world actor frame.activation

theorem prologCurrentActorActivation_iff {world : ActorWorld}
    {actor : ActorId} {activation : ActivationId} :
    PrologCurrentActorActivation world actor activation ↔
      world.currentActivation? actor = some activation := by
  constructor
  · intro derivation
    cases derivation with
    | running runState stack | paused runState stack =>
        simp [ActorWorld.currentActivation?, runState, stack,
          ActivationStack.currentActivation?]
  · intro result
    unfold ActorWorld.currentActivation? at result
    cases runStateResult : world.runStates actor with
    | none => simp [runStateResult] at result
    | some runState =>
        cases runState with
        | idle => simp [runStateResult] at result
        | runningTurn config reply event =>
            cases stackResult : config.stack with
            | empty =>
                simp [runStateResult, stackResult,
                  ActivationStack.currentActivation?] at result
            | push rest frame =>
                simp [runStateResult, stackResult,
                  ActivationStack.currentActivation?] at result
                subst activation
                exact .running runStateResult stackResult
        | pausedTurn config reply event token reason =>
            cases stackResult : config.stack with
            | empty =>
                simp [runStateResult, stackResult,
                  ActivationStack.currentActivation?] at result
            | push rest frame =>
                simp [runStateResult, stackResult,
                  ActivationStack.currentActivation?] at result
                subst activation
                exact .paused runStateResult stackResult

inductive PrologDecodeControlImageAux :
    ActivationStack → List ResolvedFrameImage →
      ActivationStack → ControlTerm → Prop where
  | activeTop {built : ActivationStack} {activation : ActivationId}
      {frames : EvalStack} {term : ControlTerm} :
      PrologDecodeControlImageAux built
        [⟨activation, .activeControl frames term⟩]
        (.push built ⟨activation, frames⟩) term
  | suspended {built : ActivationStack} {activation : ActivationId}
      {frames : EvalStack} {next : ResolvedFrameImage}
      {remaining : List ResolvedFrameImage} {stack : ActivationStack}
      {term : ControlTerm} :
      PrologDecodeControlImageAux (.push built ⟨activation, frames⟩)
        (next :: remaining) stack term →
      PrologDecodeControlImageAux built
        (⟨activation, .suspendedControl frames⟩ :: next :: remaining)
        stack term

theorem prologDecodeControlImageAux_iff {built stack : ActivationStack}
    {images : List ResolvedFrameImage} {term : ControlTerm} :
    PrologDecodeControlImageAux built images stack term ↔
      decodeControlImageAux built images = some (stack, term) := by
  constructor
  · intro derivation
    induction derivation with
    | activeTop => rfl
    | suspended _ ih => exact ih
  · intro result
    induction images generalizing built stack term with
    | nil => simp [decodeControlImageAux] at result
    | cons image remaining ih =>
        rcases image with ⟨activation, control⟩
        cases remaining with
        | nil =>
            cases controlResult : control with
            | activeControl frames activeTerm =>
                simp [decodeControlImageAux, controlResult] at result
                rcases result with ⟨rfl, rfl⟩
                exact .activeTop
            | suspendedControl frames =>
                simp [decodeControlImageAux, controlResult] at result
        | cons next later =>
            cases controlResult : control with
            | activeControl frames activeTerm =>
                simp [decodeControlImageAux, controlResult] at result
            | suspendedControl frames =>
                subst control
                exact .suspended (ih result)

inductive PrologDecodeControlImage (images : List ResolvedFrameImage) :
    ActivationStack → ControlTerm → Prop where
  | decode {stack : ActivationStack} {term : ControlTerm} :
      PrologDecodeControlImageAux .empty images stack term →
      PrologDecodeControlImage images stack term

theorem prologDecodeControlImage_iff {images : List ResolvedFrameImage}
    {stack : ActivationStack} {term : ControlTerm} :
    PrologDecodeControlImage images stack term ↔
      decodeControlImage images = some (stack, term) := by
  constructor
  · rintro ⟨derivation⟩
    exact prologDecodeControlImageAux_iff.mp derivation
  · intro result
    exact .decode (prologDecodeControlImageAux_iff.mpr result)

end PrologBridge
end Newspeak
