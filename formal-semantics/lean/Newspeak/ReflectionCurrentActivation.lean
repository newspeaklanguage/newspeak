import Newspeak.ActorSemantics

namespace Newspeak

namespace ActivationStack

/-- The activation identity at the top of a nonempty stack.  This is the
    executable projection used by Equation `current-activation`. -/
def currentActivation? : ActivationStack → Option ActivationId
  | .empty => none
  | .push _ frame => some frame.activation

end ActivationStack

namespace ActorWorld

/-- Equation `current-activation`: running and paused actors expose the top
    activation of their materialized sequential stack.  Missing and idle
    actors, and malformed empty running stacks, have no current activation. -/
def currentActivation? (world : ActorWorld) (actor : ActorId) :
    Option ActivationId := do
  let runState ← world.runStates actor
  match runState with
  | .idle => none
  | .runningTurn config _ _ | .pausedTurn config _ _ _ _ =>
      config.stack.currentActivation?

end ActorWorld

end Newspeak
