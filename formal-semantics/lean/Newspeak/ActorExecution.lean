import Newspeak.ActorDeterminism

namespace Newspeak

/-- A scheduler choice.  Computation chooses one actor; communication chooses
    one concrete eligible packet.  Keeping the choice in the label isolates
    scheduler nondeterminism from transition nondeterminism. -/
inductive ActorAction where
  | compute (actor : ActorId)
  | deliver (packet : ActorPacket)
deriving Repr, DecidableEq

inductive ActorActionStep (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) :
    ActorAction → ActorWorld → ActorWorld → Prop where
  | compute {actor : ActorId} {before after : ActorWorld} :
      SelectedActorStep p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer actor before
        after →
      ActorActionStep p reifier materialize interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer (.compute actor) before after
  | deliver {packet : ActorPacket} {before : ActorWorld} :
      packet ∈ before.network →
      before.PacketEligible packet →
      ActorActionStep p reifier materialize interpretReference interpretMessage
        installPromiseHandle isValue valueTransfer (.deliver packet) before
        (before.acceptNetworkPacket packet)

def ActorSystemStep (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (before after : ActorWorld) : Prop :=
  ∃ action, ActorActionStep p reifier materialize interpretReference
    interpretMessage installPromiseHandle isValue valueTransfer action before
    after

def ActorActionEnabled (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (action : ActorAction)
    (world : ActorWorld) : Prop :=
  ∃ after, ActorActionStep p reifier materialize interpretReference
    interpretMessage installPromiseHandle isValue valueTransfer action world
    after

/-- A possibly infinite actor execution.  Fairness is deliberately a property
    of executions, not a premise of individual safety steps. -/
def IsActorExecution (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (execution : Nat → ActorWorld) : Prop :=
  ∀ index, ActorSystemStep p reifier materialize interpretReference
    interpretMessage installPromiseHandle isValue valueTransfer
    (execution index) (execution (index + 1))

def ContinuouslyEnabled (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (execution : Nat → ActorWorld)
    (action : ActorAction) (origin : Nat) : Prop :=
  ∀ index, origin ≤ index →
    ActorActionEnabled p reifier materialize interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer action (execution index)

def ActionTaken (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (execution : Nat → ActorWorld)
    (action : ActorAction) (index : Nat) : Prop :=
  ActorActionStep p reifier materialize interpretReference interpretMessage
    installPromiseHandle isValue valueTransfer action (execution index)
    (execution (index + 1))

/-- Weak fairness, matching Equation actor-fairness: every action that remains
    enabled from some point is eventually selected. -/
def WeaklyFairActorExecution (p : Program) (reifier : ErrorReifier p)
    (materialize : LocalMessageMaterialization)
    (interpretReference : LocalEventualReferenceInterpretation)
    (interpretMessage : LocalEventualMessageInterpretation)
    (installPromiseHandle : PromiseHandleInstallation)
    (isValue : ActorWorld → ActorId → ObjRef → Prop)
    (valueTransfer : ValueTransferRelation) (execution : Nat → ActorWorld) : Prop :=
  IsActorExecution p reifier materialize interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer execution ∧
    ∀ action origin,
      ContinuouslyEnabled p reifier materialize interpretReference
        interpretMessage installPromiseHandle isValue valueTransfer execution
        action origin →
      ∃ index, origin ≤ index ∧
        ActionTaken p reifier materialize interpretReference interpretMessage
          installPromiseHandle isValue valueTransfer execution action index

theorem ActorActionStep.deterministic
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (materializationDeterministic : MaterializationDeterministic materialize)
    (referenceDeterministic :
      ReferenceInterpretationDeterministic interpretReference)
    (messageDeterministic : MessageInterpretationDeterministic interpretMessage)
    (handleDeterministic :
      PromiseHandleInstallationDeterministic installPromiseHandle)
    (transferDeterministic : ValueTransferDeterministic valueTransfer)
    {action : ActorAction} {before after₁ after₂ : ActorWorld}
    (first : ActorActionStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer action before
      after₁)
    (second : ActorActionStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer action before
      after₂) : after₁ = after₂ := by
  cases first with
  | compute selected₁ =>
      cases second with
      | compute selected₂ =>
          exact selected₁.deterministic materializationDeterministic
            referenceDeterministic messageDeterministic handleDeterministic
            transferDeterministic selected₂
  | deliver member₁ eligible₁ =>
      cases second with
      | deliver member₂ eligible₂ => rfl

/-- A delivered packet cannot overtake a causal predecessor addressed to the
    same destination. -/
theorem ActorActionStep.delivery_respects_e_order
    {p : Program} {reifier : ErrorReifier p}
    {materialize interpretReference interpretMessage installPromiseHandle
      isValue valueTransfer packet before after predecessor record}
    (step : ActorActionStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer
      (.deliver packet) before after)
    (predecessorMember : predecessor ∈ packet.causalHistory)
    (ledger : before.eventLedger predecessor = some record)
    (sameDestination : record.destination = packet.destination) :
    predecessor ∈ before.deliveredTo packet.destination := by
  cases step with
  | deliver member eligible =>
      rcases eligible predecessor predecessorMember with
        ⟨record', ledger', delivered⟩
      have recordEqual := Option.some.inj (ledger.symm.trans ledger')
      subst record'
      exact delivered sameDestination

end Newspeak
