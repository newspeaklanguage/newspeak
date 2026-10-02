import Newspeak.SlotInitialization

namespace Newspeak
namespace Program

@[simp] theorem initializationCoordinatorNext_receiverFrame_none (p : Program)
    (state : AllocationState) (rest : ActivationStack) (current : ActivationId)
    (frames : EvalStack) (value : ObjRef) (selector : Selector)
    (arguments : List CoreExpr) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current, .push frames (.receiver selector arguments)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_argumentsFrame_none (p : Program)
    (state : AllocationState) (rest : ActivationStack) (current : ActivationId)
    (frames : EvalStack) (value : ObjRef) (request : SendRequest)
    (selector : Selector) (values : List ObjRef) (remaining : List CoreExpr) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current,
        .push frames (.arguments request selector values remaining)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_slotWriteFrame_none (p : Program)
    (state : AllocationState) (rest : ActivationStack) (current : ActivationId)
    (frames : EvalStack) (value : ObjRef) (object : ObjectId) (slot : SlotId) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current, .push frames (.slotWrite object slot)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_lazySlotStoreFrame_none
    (p : Program) (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (value : ObjRef)
    (object : ObjectId) (slot : SlotId) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current, .push frames (.lazySlotStore object slot)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_makeClassBodyFrame_none
    (p : Program) (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (value : ObjRef)
    (descriptor : ClassBodyDescriptor) (enclosingObject : ObjRef) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current,
        .push frames (.makeClassBody descriptor enclosingObject)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_mixinSuperclassFrame_none
    (p : Program) (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (value : ObjRef)
    (descriptor : MixinApplicationDescriptor) (source : CoreExpr) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current,
        .push frames (.mixinSuperclass descriptor source)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_mixinSourceFrame_none
    (p : Program) (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (value : ObjRef)
    (descriptor : MixinApplicationDescriptor) (superclass : ClassId) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current,
        .push frames (.mixinSource descriptor superclass)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

@[simp] theorem initializationCoordinatorNext_messageArgumentsFrame_none
    (p : Program) (state : AllocationState) (rest : ActivationStack)
    (current : ActivationId) (frames : EvalStack) (value : ObjRef)
    (selector : Selector) (values : List ObjRef) (remaining : List CoreExpr) :
    p.initializationCoordinatorNext
      ⟨state, .push rest ⟨current,
        .push frames (.messageArguments selector values remaining)⟩,
        .object value⟩ = none := by
  cases value <;> rfl

theorem bodyMachine_initializationCoordinator_disjoint {p : Program}
    {before bodyAfter coordinatorAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (coordinator : p.InitializationCoordinatorStep before coordinatorAfter) :
    False := by
  cases body with
  | graph bodyNext =>
      cases coordinator with
      | graph coordinatorNext =>
          rcases before with ⟨state, stack, control⟩
          cases stack with
          | empty => simp [bodyMachineNext] at bodyNext
          | push rest frame =>
              rcases frame with ⟨current, frames⟩
              cases control with
              | object value =>
                  cases value with
                  | ordinaryObject object =>
                      cases frames with
                      | empty => simp [bodyMachineNext] at bodyNext
                      | push below top =>
                          cases top <;>
                            simp [bodyMachineNext, initializationCoordinatorNext]
                              at bodyNext coordinatorNext
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
                  simp [bodyMachineNext] at bodyNext
              | messageValue message => simp [bodyMachineNext] at bodyNext
              | ownInitialization classId object message =>
                  simp [bodyMachineNext] at bodyNext
              | evaluate expression =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | evaluateMessage template =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | initializeSlotGroups object groups statements =>
                  simp [bodyMachineNext] at bodyNext
              | initializeSequentialSlots object declarations groups statements =>
                  simp [bodyMachineNext] at bodyNext
              | dispatch request message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | invoke method receiver definingClass message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | invokeClosure closure message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | «initialize» activation groups statements target =>
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

theorem returnMachine_initializationCoordinator_disjoint {p : Program}
    {before returnAfter coordinatorAfter : SequentialConfig}
    (returns : p.ReturnMachineStep before returnAfter)
    (coordinator : p.InitializationCoordinatorStep before coordinatorAfter) :
    False := by
  cases returns with
  | graph returnNext =>
      cases coordinator with
      | graph coordinatorNext =>
          rcases before with ⟨state, stack, control⟩
          cases stack with
          | empty => simp [returnMachineNext] at returnNext
          | push rest frame =>
              rcases frame with ⟨current, frames⟩
              cases control with
              | object value =>
                  cases value with
                  | ordinaryObject object =>
                      cases frames with
                      | empty => simp [returnMachineNext] at returnNext
                      | push below top =>
                          cases top <;>
                            simp [returnMachineNext, initializationCoordinatorNext]
                              at returnNext coordinatorNext
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
              | transfer target value =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | initClass classId object message =>
                  simp [returnMachineNext] at returnNext
              | messageValue message => simp [returnMachineNext] at returnNext
              | ownInitialization classId object message =>
                  simp [returnMachineNext] at returnNext
              | evaluate expression =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | evaluateMessage template =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | initializeSlotGroups object groups statements =>
                  simp [returnMachineNext] at returnNext
              | initializeSequentialSlots object declarations groups statements =>
                  simp [returnMachineNext] at returnNext
              | dispatch request message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | invoke method receiver definingClass message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | invokeClosure closure message =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | «initialize» activation groups statements target =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | body target statements =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | finish value =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | halt value =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | abort exception =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | throw error =>
                  simp [initializationCoordinatorNext] at coordinatorNext
              | runtimeError error =>
                  simp [initializationCoordinatorNext] at coordinatorNext

theorem sequentialStep_initializationCoordinator_disjoint {p : Program}
    {before sequentialAfter coordinatorAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (coordinator : p.InitializationCoordinatorStep before coordinatorAfter) :
    False := by
  cases sequential with
  | expression expression =>
      cases coordinator with
      | graph next =>
          cases expression with
          | value => simp [initializationCoordinatorNext] at next
          | selfValue => simp [initializationCoordinatorNext] at next
          | ordinaryReceiver => simp [initializationCoordinatorNext] at next
          | eventualReceiver => simp [initializationCoordinatorNext] at next
          | nonOrdinary => simp [initializationCoordinatorNext] at next
          | receiverValue =>
              simp only [initializationCoordinatorNext_receiverFrame_none]
                at next
              cases next
          | @eventualReceiverValue state rest current frames receiver selector arguments =>
              cases receiver <;> cases arguments <;>
                simp [initializationCoordinatorNext] at next
          | argumentValue =>
              simp only [initializationCoordinatorNext_argumentsFrame_none]
                at next
              cases next
  | request request =>
      cases coordinator with
      | graph next => cases request <;>
          simp [initializationCoordinatorNext] at next
  | invocation invocation =>
      cases coordinator with
      | graph next => cases invocation <;>
          simp [initializationCoordinatorNext] at next
  | body body => exact bodyMachine_initializationCoordinator_disjoint body coordinator
  | returns returns =>
      exact returnMachine_initializationCoordinator_disjoint returns coordinator
  | closure closure =>
      cases coordinator with
      | graph next =>
          cases closure with
          | creation creation => cases creation <;>
              simp [initializationCoordinatorNext] at next
          | dispatch dispatch => cases dispatch <;>
              simp [initializationCoordinatorNext] at next
          | invocation invocation => cases invocation <;>
              simp [initializationCoordinatorNext] at next
  | objectSlots slots =>
      cases coordinator with
      | graph next =>
          cases slots with
          | atom => simp [initializationCoordinatorNext] at next
          | read => simp [initializationCoordinatorNext] at next
          | writeStart => simp [initializationCoordinatorNext] at next
          | writeCommit =>
              simp only [initializationCoordinatorNext_slotWriteFrame_none]
                at next
              cases next
          | currentRead => simp [initializationCoordinatorNext] at next
          | currentWrite => simp [initializationCoordinatorNext] at next
          | lazyHit => simp [initializationCoordinatorNext] at next
          | lazyMiss => simp [initializationCoordinatorNext] at next
          | lazyCommit =>
              simp only [initializationCoordinatorNext_lazySlotStoreFrame_none]
                at next
              cases next
  | classes classes =>
      cases coordinator with
      | graph next =>
          cases classes with
          | bodyStart => simp [initializationCoordinatorNext] at next
          | bodyCommit =>
              simp only [initializationCoordinatorNext_makeClassBodyFrame_none]
                at next
              cases next
          | bodyInheritanceError =>
              simp only [initializationCoordinatorNext_makeClassBodyFrame_none]
                at next
              cases next
          | bodyTopError =>
              simp only [initializationCoordinatorNext_makeClassBodyFrame_none]
                at next
              cases next
          | mixinStart => simp [initializationCoordinatorNext] at next
          | mixinSuperclassDone =>
              simp only [initializationCoordinatorNext_mixinSuperclassFrame_none]
                at next
              cases next
          | mixinCommit =>
              simp only [initializationCoordinatorNext_mixinSourceFrame_none]
                at next
              cases next
          | mixinSuperclassError =>
              simp only [initializationCoordinatorNext_mixinSuperclassFrame_none]
                at next
              cases next
          | mixinSourceError =>
              simp only [initializationCoordinatorNext_mixinSourceFrame_none]
                at next
              cases next
  | messages messages =>
      cases coordinator with
      | graph next =>
          cases messages with
          | start => simp [initializationCoordinatorNext] at next
          | argument =>
              simp only [initializationCoordinatorNext_messageArgumentsFrame_none]
                at next
              cases next

theorem bodyMachine_slotInitialization_disjoint {p : Program}
    {before bodyAfter slotAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (slots : p.SlotInitializationStep before slotAfter) : False := by
  cases body with
  | graph bodyNext =>
      cases slots with
      | graph slotNext =>
          rcases before with ⟨state, stack, control⟩
          cases stack with
          | empty => simp [bodyMachineNext] at bodyNext
          | push rest frame =>
              rcases frame with ⟨current, frames⟩
              cases control with
              | object value =>
                  cases frames with
                  | empty => simp [bodyMachineNext] at bodyNext
                  | push below top =>
                      cases top <;>
                        simp [bodyMachineNext, slotInitializationNext]
                          at bodyNext slotNext
              | initializeSlotGroups object groups statements =>
                  simp [bodyMachineNext] at bodyNext
              | initializeSequentialSlots object declarations groups statements =>
                  simp [bodyMachineNext] at bodyNext
              | evaluate expression => simp [slotInitializationNext] at slotNext
              | evaluateMessage template =>
                  simp [slotInitializationNext] at slotNext
              | messageValue message => simp [slotInitializationNext] at slotNext
              | initClass classId object message =>
                  simp [slotInitializationNext] at slotNext
              | ownInitialization classId object message =>
                  simp [slotInitializationNext] at slotNext
              | dispatch request message => simp [slotInitializationNext] at slotNext
              | invoke method receiver definingClass message =>
                  simp [slotInitializationNext] at slotNext
              | invokeClosure closure message =>
                  simp [slotInitializationNext] at slotNext
              | «initialize» activation groups statements target =>
                  simp [slotInitializationNext] at slotNext
              | body target statements => simp [slotInitializationNext] at slotNext
              | finish value => simp [slotInitializationNext] at slotNext
              | transfer target value => simp [slotInitializationNext] at slotNext
              | halt value => simp [slotInitializationNext] at slotNext
              | abort exception => simp [slotInitializationNext] at slotNext
              | throw error => simp [slotInitializationNext] at slotNext
              | runtimeError error => simp [slotInitializationNext] at slotNext

theorem returnMachine_slotInitialization_disjoint {p : Program}
    {before returnAfter slotAfter : SequentialConfig}
    (returns : p.ReturnMachineStep before returnAfter)
    (slots : p.SlotInitializationStep before slotAfter) : False := by
  cases returns with
  | graph returnNext =>
      cases slots with
      | graph slotNext =>
          rcases before with ⟨state, stack, control⟩
          cases stack with
          | empty => simp [returnMachineNext] at returnNext
          | push rest frame =>
              rcases frame with ⟨current, frames⟩
              cases control with
              | object value =>
                  cases frames with
                  | empty => simp [returnMachineNext] at returnNext
                  | push below top =>
                      cases top <;>
                        simp [returnMachineNext, slotInitializationNext]
                          at returnNext slotNext
              | initializeSlotGroups object groups statements =>
                  simp [returnMachineNext] at returnNext
              | initializeSequentialSlots object declarations groups statements =>
                  simp [returnMachineNext] at returnNext
              | evaluate expression => simp [slotInitializationNext] at slotNext
              | evaluateMessage template =>
                  simp [slotInitializationNext] at slotNext
              | messageValue message => simp [slotInitializationNext] at slotNext
              | initClass classId object message =>
                  simp [slotInitializationNext] at slotNext
              | ownInitialization classId object message =>
                  simp [slotInitializationNext] at slotNext
              | dispatch request message => simp [slotInitializationNext] at slotNext
              | invoke method receiver definingClass message =>
                  simp [slotInitializationNext] at slotNext
              | invokeClosure closure message =>
                  simp [slotInitializationNext] at slotNext
              | «initialize» activation groups statements target =>
                  simp [slotInitializationNext] at slotNext
              | body target statements => simp [slotInitializationNext] at slotNext
              | finish value => simp [slotInitializationNext] at slotNext
              | transfer target value => simp [slotInitializationNext] at slotNext
              | halt value => simp [slotInitializationNext] at slotNext
              | abort exception => simp [slotInitializationNext] at slotNext
              | throw error => simp [slotInitializationNext] at slotNext
              | runtimeError error => simp [slotInitializationNext] at slotNext

theorem sequentialStep_slotInitialization_disjoint {p : Program}
    {before sequentialAfter slotAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (slots : p.SlotInitializationStep before slotAfter) : False := by
  cases sequential with
  | expression expression =>
      cases slots with
      | graph next => cases expression <;> simp [slotInitializationNext] at next
  | request request =>
      cases slots with
      | graph next => cases request <;> simp [slotInitializationNext] at next
  | invocation invocation =>
      cases slots with
      | graph next => cases invocation <;> simp [slotInitializationNext] at next
  | body body => exact bodyMachine_slotInitialization_disjoint body slots
  | returns returns => exact returnMachine_slotInitialization_disjoint returns slots
  | closure closure =>
      cases slots with
      | graph next =>
          cases closure with
          | creation creation => cases creation <;>
              simp [slotInitializationNext] at next
          | dispatch dispatch => cases dispatch <;>
              simp [slotInitializationNext] at next
          | invocation invocation => cases invocation <;>
              simp [slotInitializationNext] at next
  | objectSlots objectSlots =>
      cases slots with
      | graph next => cases objectSlots <;> simp [slotInitializationNext] at next
  | classes classes =>
      cases slots with
      | graph next => cases classes <;> simp [slotInitializationNext] at next
  | messages messages =>
      cases slots with
      | graph next => cases messages <;> simp [slotInitializationNext] at next

theorem sequentialStep_instanceInitialization_disjoint {p : Program}
    {before sequentialAfter initializationAfter : SequentialConfig}
    (sequential : p.SequentialStep before sequentialAfter)
    (initialization : p.InstanceInitializationStep before initializationAfter) :
    False := by
  cases initialization with
  | factory factory => exact sequentialStep_factoryNew_disjoint sequential factory
  | coordinator coordinator =>
      exact sequentialStep_initializationCoordinator_disjoint sequential coordinator
  | slots slots => exact sequentialStep_slotInitialization_disjoint sequential slots

/-- The enlarged sequential semantics through complete instance
    initialization. -/
inductive SequentialStepWithInitialization (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | prior {before after : SequentialConfig} :
      p.SequentialStep before after →
        p.SequentialStepWithInitialization before after
  | initialization {before after : SequentialConfig} :
      p.InstanceInitializationStep before after →
        p.SequentialStepWithInitialization before after

theorem sequentialStepWithInitialization_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (step₁ : p.SequentialStepWithInitialization before after₁)
    (step₂ : p.SequentialStepWithInitialization before after₂) : after₁ = after₂ := by
  cases step₁ with
  | prior prior₁ =>
      cases step₂ with
      | prior prior₂ => exact sequentialStep_deterministic wf prior₁ prior₂
      | initialization initialization₂ =>
          exact (sequentialStep_instanceInitialization_disjoint
            prior₁ initialization₂).elim
  | initialization initialization₁ =>
      cases step₂ with
      | prior prior₂ =>
          exact (sequentialStep_instanceInitialization_disjoint
            prior₂ initialization₁).elim
      | initialization initialization₂ =>
          exact instanceInitializationStep_deterministic
            initialization₁ initialization₂

theorem sequentialStepWithInitialization_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.SequentialStepWithInitialization before after) :
    SequentialWellFormed p after := by
  cases step with
  | prior prior => exact sequentialStep_preserves_wellFormed wf prior
  | initialization initialization =>
      exact instanceInitializationStep_preserves_wellFormed wf initialization

end Program
end Newspeak
