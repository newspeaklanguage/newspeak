import Newspeak.ReflectionQueries
import Newspeak.ReflectionFrameObservation

namespace Newspeak

inductive ActorStackMode where
  | running
  | paused (token : PauseTokenId) (reason : DebuggerStopReason)
deriving Repr

structure DebugFrameImage where
  activation : ActivationId
  definition : ActivationDef
  control : FrameControl

structure ActorStackSnapshot where
  mode : ActorStackMode
  frames : List DebugFrameImage

namespace ActivationStack

def suspendedControlImage : ActivationStack → List ResolvedFrameImage
  | .empty => []
  | .push rest frame =>
      suspendedControlImage rest ++
        [⟨frame.activation, .suspendedControl frame.frames⟩]

def controlImage? : ActivationStack → ControlTerm → Option (List ResolvedFrameImage)
  | .empty, _ => none
  | .push rest frame, term =>
      some (suspendedControlImage rest ++
        [⟨frame.activation, .activeControl frame.frames term⟩])

def findFrame? : ActivationStack → ActivationId → Option ActivationFrame
  | .empty, _ => none
  | .push rest frame, activation =>
      if frame.activation = activation then some frame
      else findFrame? rest activation

def liveControl? (stack : ActivationStack) (term : ControlTerm)
    (activation : ActivationId) : Option FrameControl :=
  match stack with
  | .empty => none
  | .push rest frame =>
      if frame.activation = activation then
        some (.activeControl frame.frames term)
      else
        (findFrame? rest activation).map fun found =>
          .suspendedControl found.frames

end ActivationStack

def reifyDebugFrames : Heap → List ResolvedFrameImage → Option (List DebugFrameImage)
  | _, [] => some []
  | heap, image :: remaining => do
      let definition ← heap.activations image.activation
      let tail ← reifyDebugFrames heap remaining
      some (⟨image.activation, definition, image.control⟩ :: tail)

namespace ActorRunState

def liveControl? (state : ActorRunState) (activation : ActivationId) :
    Option FrameControl :=
  match state with
  | .idle => none
  | .runningTurn config _ _ | .pausedTurn config _ _ _ _ =>
      config.stack.liveControl? config.control activation

end ActorRunState

namespace ActorWorld

def actorStackSnapshot? (world : ActorWorld) (actor : ActorId) :
    Option ActorStackSnapshot := do
  let state ← world.runStates actor
  match state with
  | .idle => none
  | .runningTurn config _ _ => do
      let controls ← config.stack.controlImage? config.control
      let frames ← reifyDebugFrames config.allocation.heap controls
      some ⟨.running, frames⟩
  | .pausedTurn config _ _ token reason => do
      let controls ← config.stack.controlImage? config.control
      let frames ← reifyDebugFrames config.allocation.heap controls
      some ⟨.paused token reason, frames⟩

def liveActivationControlFrom (world : ActorWorld) (activation : ActivationId) :
    List ActorId → Option FrameControl
  | [] => none
  | actor :: remaining =>
      match (world.runStates actor).bind fun state => state.liveControl? activation with
      | some control => some control
      | none => world.liveActivationControlFrom activation remaining

def liveActivationControl? (world : ActorWorld) (activation : ActivationId) :
    Option FrameControl :=
  world.liveActivationControlFrom activation world.runStates.domain

structure DebugActivationDescriptor where
  activation : ReflectedActivation
  liveControl : Option FrameControl

def describeDebugActivation? (world : ActorWorld) (activation : ActivationId) :
    Option DebugActivationDescriptor := do
  let location ← world.locateActivationId activation
  let heap ← world.heapAt location
  let definition ← heap.activations activation
  some ⟨⟨location, definition⟩, world.liveActivationControl? activation⟩

end ActorWorld
end Newspeak
