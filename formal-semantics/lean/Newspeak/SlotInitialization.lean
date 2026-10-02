import Newspeak.InitializationCoordinator

namespace Newspeak

def eagerSlotInitializer : SlotDeclaration →
    Option (SlotId × CoreExpr × ActivationDeclId)
  | .immutable slot initializer thunk => some (slot, initializer, thunk)
  | .mutableInitialized slot initializer thunk =>
      some (slot, initializer, thunk)
  | .mutableUninitialized _ => none

def Program.slotFutureInstallExpression (p : Program)
    (activation : ActivationId) (object : ObjectId) :
    SlotDeclaration → Option CoreExpr
  | .immutable slot _ thunk
  | .mutableInitialized slot _ thunk =>
      some (.writeSlot object slot
        (.ordinarySend (p.pastFutureExpression activation) computingSelector
          [.closureLiteral thunk]))
  | .mutableUninitialized _ => none

def slotFutureResolveExpression (object : ObjectId) :
    SlotDeclaration → Option CoreExpr
  | .immutable slot _ _
  | .mutableInitialized slot _ _ =>
      some (.ordinarySend (.readSlot object slot) resolveSelector [])
  | .mutableUninitialized _ => none

/-- Equation (9.25): every eager slot gets its future before any future is
    resolved; both subsequences retain declaration source order. -/
def Program.slotSimCode (p : Program) (activation : ActivationId)
    (object : ObjectId) (declarations : List SlotDeclaration) : List CoreExpr :=
  declarations.filterMap (p.slotFutureInstallExpression activation object) ++
    declarations.filterMap (slotFutureResolveExpression object)

theorem Program.slotSimCode_installationPrefix (p : Program)
    (activation : ActivationId) (object : ObjectId)
    (declarations : List SlotDeclaration) :
    let installations := declarations.filterMap
      (p.slotFutureInstallExpression activation object)
    (p.slotSimCode activation object declarations).take installations.length =
      installations := by
  simp [Program.slotSimCode]

namespace Program

def startSimultaneousSlots (p : Program) (state : AllocationState)
    (rest : ActivationStack) (current : ActivationId) (frames : EvalStack)
    (object : ObjectId) (declarations : List SlotDeclaration)
    (remainingGroups : List SlotDeclarationGroup) (body : List Statement) :
    SequentialConfig :=
  match p.slotSimCode current object declarations with
  | [] => ⟨state, .push rest ⟨current, frames⟩,
      .initializeSlotGroups object remainingGroups body⟩
  | first :: later =>
      ⟨state, .push rest ⟨current,
        .push frames (.simultaneousSlots later object remainingGroups body)⟩,
        .evaluate first⟩

/-- Equations (9.21)--(9.26): direct sequential initialization and the
    PastFuture-based expansion of simultaneous instance-slot groups. -/
def slotInitializationNext (p : Program)
    (config : SequentialConfig) : Option SequentialConfig := do
  let .push rest currentFrame := config.stack | none
  let state := config.allocation
  let current := currentFrame.activation
  let frames := currentFrame.frames
  match config.control with
  | .initializeSlotGroups object groups body =>
      match groups with
      | [] => some ⟨state, config.stack,
          .body (.methodBody (.ordinaryObject object)) body⟩
      | .sequential declarations :: remaining =>
          some ⟨state, config.stack,
            .initializeSequentialSlots object declarations remaining body⟩
      | .simultaneous declarations :: remaining =>
          some (p.startSimultaneousSlots state rest current frames object
            declarations remaining body)
  | .initializeSequentialSlots object declarations remainingGroups body =>
      match declarations with
      | [] => some ⟨state, config.stack,
          .initializeSlotGroups object remainingGroups body⟩
      | .mutableUninitialized _ :: later =>
          some ⟨state, config.stack,
            .initializeSequentialSlots object later remainingGroups body⟩
      | .immutable slot initializer _ :: later
      | .mutableInitialized slot initializer _ :: later =>
          some ⟨state, .push rest ⟨current,
            .push frames (.storeInitializedSlot object slot later
              remainingGroups body)⟩,
            .evaluate initializer⟩
  | .object value =>
      match frames with
      | .push below (.storeInitializedSlot object slot later remaining body) => do
          let heap ← state.heap.writeObjectSlot object slot value
          some ⟨{state with heap := heap}, .push rest ⟨current, below⟩,
            .initializeSequentialSlots object later remaining body⟩
      | .push below (.simultaneousSlots code object remaining body) =>
          match code with
          | [] => some ⟨state, .push rest ⟨current, below⟩,
              .initializeSlotGroups object remaining body⟩
          | first :: later =>
              some ⟨state, .push rest ⟨current,
                .push below (.simultaneousSlots later object remaining body)⟩,
                .evaluate first⟩
      | _ => none
  | _ => none

inductive SlotInitializationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | graph {before after : SequentialConfig}
      (next : p.slotInitializationNext before = some after) :
      p.SlotInitializationStep before after

theorem slotInitializationStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.SlotInitializationStep before after₁)
    (step₂ : p.SlotInitializationStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | graph next₁ =>
      cases step₂ with
      | graph next₂ => exact Option.some.inj (next₁.symm.trans next₂)

theorem slotInitializationStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.SlotInitializationStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | graph next =>
      rcases before with ⟨state, stack, control⟩
      cases stack with
      | empty => simp [slotInitializationNext] at next
      | push rest currentFrame =>
          rcases currentFrame with ⟨current, frames⟩
          cases control with
          | initializeSlotGroups object groups body =>
              cases groups with
              | nil =>
                  simp [slotInitializationNext] at next
                  subst after
                  exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
              | cons group remaining =>
                  cases group with
                  | sequential declarations =>
                      simp [slotInitializationNext] at next
                      subst after
                      exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
                  | simultaneous declarations =>
                      cases codeResult : p.slotSimCode current object declarations with
                      | nil =>
                          simp [slotInitializationNext, startSimultaneousSlots,
                            codeResult] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                      | cons first later =>
                          simp [slotInitializationNext, startSimultaneousSlots,
                            codeResult] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
          | initializeSequentialSlots object declarations remaining body =>
              cases declarations with
              | nil =>
                  simp [slotInitializationNext] at next
                  subst after
                  exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
              | cons declaration later =>
                  cases declaration with
                  | mutableUninitialized slot =>
                      simp [slotInitializationNext] at next
                      subst after
                      exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
                  | immutable slot initializer thunk =>
                      simp [slotInitializationNext] at next
                      subst after
                      exact ⟨wf.heap, wf.supplies, by
                        simpa [StackLive] using wf.stack, trivial⟩
                  | mutableInitialized slot initializer thunk =>
                      simp [slotInitializationNext] at next
                      subst after
                      exact ⟨wf.heap, wf.supplies, by
                        simpa [StackLive] using wf.stack, trivial⟩
          | object value =>
              cases frames with
              | empty => simp [slotInitializationNext] at next
              | push below topFrame =>
                  cases topFrame with
                  | storeInitializedSlot object slot declarations groups body =>
                      cases write : state.heap.writeObjectSlot object slot value with
                      | none =>
                          simp [slotInitializationNext, write] at next
                      | some heap =>
                          simp [slotInitializationNext, write] at next
                          subst after
                          refine ⟨wf.heap.writeObjectSlot_wellFormed write,
                            AllocationState.writeObjectSlot_preserves_supplies
                              wf.supplies write, ?_, trivial⟩
                          exact stackLive_transport (by
                            simpa [StackLive] using wf.stack)
                            (Heap.writeObjectSlot_retainsActivations write)
                  | simultaneousSlots code object groups body =>
                      cases code with
                      | nil =>
                          simp [slotInitializationNext] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                      | cons first later =>
                          simp [slotInitializationNext] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                  | receiver selector arguments =>
                      simp [slotInitializationNext] at next
                  | asyncReceiver selector arguments =>
                      simp [slotInitializationNext] at next
                  | arguments request selector values remaining =>
                      simp [slotInitializationNext] at next
                  | initializeLocal slot remaining body target =>
                      simp [slotInitializationNext] at next
                  | localWrite activation slot =>
                      simp [slotInitializationNext] at next
                  | slotWrite object slot => simp [slotInitializationNext] at next
                  | lazySlotStore object slot =>
                      simp [slotInitializationNext] at next
                  | makeClassBody descriptor enclosingObject =>
                      simp [slotInitializationNext] at next
                  | makeObjectLiteral descriptor enclosingObject =>
                      simp [slotInitializationNext] at next
                  | nestedClassStore object declaration =>
                      simp [slotInitializationNext] at next
                  | mixinSuperclass descriptor mixinSource =>
                      simp [slotInitializationNext] at next
                  | mixinSource descriptor superclass =>
                      simp [slotInitializationNext] at next
                  | messageArguments selector values remaining =>
                      simp [slotInitializationNext] at next
                  | superclassMessage classId object original =>
                      simp [slotInitializationNext] at next
                  | afterSuperclass classId object original =>
                      simp [slotInitializationNext] at next
                  | mixinMessage classId object =>
                      simp [slotInitializationNext] at next
                  | afterMixin classId object =>
                      simp [slotInitializationNext] at next
                  | simultaneousLocals code activation remaining body target =>
                      simp [slotInitializationNext] at next
                  | sequence target remaining =>
                      simp [slotInitializationNext] at next
                  | returnFrame => simp [slotInitializationNext] at next
          | evaluate expression => simp [slotInitializationNext] at next
          | evaluateMessage template => simp [slotInitializationNext] at next
          | messageValue message => simp [slotInitializationNext] at next
          | initClass classId object message => simp [slotInitializationNext] at next
          | ownInitialization classId object message =>
              simp [slotInitializationNext] at next
          | dispatch request message => simp [slotInitializationNext] at next
          | invoke method receiver definingClass message =>
              simp [slotInitializationNext] at next
          | invokeClosure closure message => simp [slotInitializationNext] at next
          | «initialize» activation groups body target =>
              simp [slotInitializationNext] at next
          | body target statements => simp [slotInitializationNext] at next
          | finish value => simp [slotInitializationNext] at next
          | transfer target value => simp [slotInitializationNext] at next
          | halt value => simp [slotInitializationNext] at next
          | abort exception => simp [slotInitializationNext] at next
          | throw error => simp [slotInitializationNext] at next
          | runtimeError error => simp [slotInitializationNext] at next

theorem factoryNew_initializationCoordinator_disjoint {p : Program}
    {before factoryAfter coordinatorAfter : SequentialConfig}
    (factory : p.FactoryNewStep before factoryAfter)
    (coordinator : p.InitializationCoordinatorStep before coordinatorAfter) :
    False := by
  cases factory
  cases coordinator with
  | graph next => simp [initializationCoordinatorNext] at next

theorem factoryNew_slotInitialization_disjoint {p : Program}
    {before factoryAfter slotAfter : SequentialConfig}
    (factory : p.FactoryNewStep before factoryAfter)
    (slots : p.SlotInitializationStep before slotAfter) : False := by
  cases factory
  cases slots with
  | graph next => simp [slotInitializationNext] at next

theorem initializationCoordinator_slotInitialization_disjoint {p : Program}
    {before coordinatorAfter slotAfter : SequentialConfig}
    (coordinator : p.InitializationCoordinatorStep before coordinatorAfter)
    (slots : p.SlotInitializationStep before slotAfter) : False := by
  cases coordinator with
  | graph coordinatorNext =>
      cases slots with
      | graph slotNext =>
          rcases before with ⟨state, stack, control⟩
          cases stack with
          | empty => simp [initializationCoordinatorNext] at coordinatorNext
          | push rest currentFrame =>
              rcases currentFrame with ⟨current, frames⟩
              cases control with
              | object value =>
                  cases value with
                  | ordinaryObject result =>
                      cases frames with
                      | empty =>
                          simp [initializationCoordinatorNext] at coordinatorNext
                      | push below topFrame =>
                          cases topFrame <;>
                            simp [initializationCoordinatorNext,
                              slotInitializationNext] at coordinatorNext slotNext
                  | classObject id =>
                      simp [initializationCoordinatorNext] at coordinatorNext
                  | mixinObject id =>
                      simp [initializationCoordinatorNext] at coordinatorNext
                  | activationObject id =>
                      simp [initializationCoordinatorNext] at coordinatorNext
                  | closureObject id =>
                      simp [initializationCoordinatorNext] at coordinatorNext
                  | mirrorObject id =>
                      simp [initializationCoordinatorNext] at coordinatorNext
                  | actorObject id =>
                      simp [initializationCoordinatorNext] at coordinatorNext
              | initClass classId object message =>
                  simp [slotInitializationNext] at slotNext
              | messageValue message => simp [slotInitializationNext] at slotNext
              | ownInitialization classId object message =>
                  simp [slotInitializationNext] at slotNext
              | initializeSlotGroups object groups body =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | initializeSequentialSlots object declarations groups body =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | evaluate expression =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | evaluateMessage template =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | dispatch request message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | invoke method receiver definingClass message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | invokeClosure closure message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | «initialize» activation groups body target =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | body target statements =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | finish value =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | transfer target value =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | halt value =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | abort exception =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | throw error =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | runtimeError error =>
                  simp [initializationCoordinatorNext] at coordinatorNext

/-- The complete instance-initialization fragment: initial allocation,
    superclass/mixin coordination, and physical slot-group execution. -/
inductive InstanceInitializationStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | factory {before after : SequentialConfig} :
      p.FactoryNewStep before after → p.InstanceInitializationStep before after
  | coordinator {before after : SequentialConfig} :
      p.InitializationCoordinatorStep before after →
        p.InstanceInitializationStep before after
  | slots {before after : SequentialConfig} :
      p.SlotInitializationStep before after →
        p.InstanceInitializationStep before after

theorem instanceInitializationStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (step₁ : p.InstanceInitializationStep before after₁)
    (step₂ : p.InstanceInitializationStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | factory factory₁ =>
      cases step₂ with
      | factory factory₂ => exact factoryNewStep_deterministic factory₁ factory₂
      | coordinator coordinator₂ =>
          exact (factoryNew_initializationCoordinator_disjoint
            factory₁ coordinator₂).elim
      | slots slots₂ =>
          exact (factoryNew_slotInitialization_disjoint factory₁ slots₂).elim
  | coordinator coordinator₁ =>
      cases step₂ with
      | factory factory₂ =>
          exact (factoryNew_initializationCoordinator_disjoint
            factory₂ coordinator₁).elim
      | coordinator coordinator₂ =>
          exact initializationCoordinatorStep_deterministic
            coordinator₁ coordinator₂
      | slots slots₂ =>
          exact (initializationCoordinator_slotInitialization_disjoint
            coordinator₁ slots₂).elim
  | slots slots₁ =>
      cases step₂ with
      | factory factory₂ =>
          exact (factoryNew_slotInitialization_disjoint factory₂ slots₁).elim
      | coordinator coordinator₂ =>
          exact (initializationCoordinator_slotInitialization_disjoint
            coordinator₂ slots₁).elim
      | slots slots₂ => exact slotInitializationStep_deterministic slots₁ slots₂

theorem instanceInitializationStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.InstanceInitializationStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | factory factory => exact factoryNewStep_preserves_wellFormed wf factory
  | coordinator coordinator =>
      exact initializationCoordinatorStep_preserves_wellFormed wf coordinator
  | slots slots => exact slotInitializationStep_preserves_wellFormed wf slots

end Program
end Newspeak
