import Newspeak.ReflectionDebugger

namespace Newspeak

def ActorRunState.stackActivationIds : ActorRunState → List ActivationId
  | .idle => []
  | .runningTurn config _ _ | .pausedTurn config _ _ _ _ =>
      config.stack.activationIds

def ActorWorld.liveActivationIdsFrom (world : ActorWorld) :
    List ActorId → List ActivationId
  | [] => []
  | actor :: remaining =>
      let current := match world.runStates actor with
        | none => []
        | some state => state.stackActivationIds
      FiniteStore.deduplicated
        (current ++ world.liveActivationIdsFrom remaining)

def ActorWorld.liveActivationIds (world : ActorWorld) : List ActivationId :=
  world.liveActivationIdsFrom world.runStates.domain

inductive ListBefore {Element : Type} (first second : Element) :
    List Element → Prop where
  | here {remaining} : second ∈ remaining →
      ListBefore first second (first :: remaining)
  | later {head remaining} : ListBefore first second remaining →
      ListBefore first second (head :: remaining)

def ActorWorld.Below (world : ActorWorld) (actor : ActorId)
    (lower upper : ActivationId) : Prop :=
  ∃ state, world.runStates actor = some state ∧
    ListBefore lower upper state.stackActivationIds

end Newspeak
