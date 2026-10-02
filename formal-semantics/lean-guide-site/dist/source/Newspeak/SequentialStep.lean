import Newspeak.MessageEvaluation

namespace Newspeak
namespace Program

/-- Install the result of complete request processing as the next control
    term.  DNU has already been performed by `CompleteRequest`, so `missing`
    has no constructor here. -/
inductive RequestCompletionStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | invoke {state nextState : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {request : SendRequest}
      {message finalMessage : Message} {method : MethodDef}
      {receiver : ObjRef} {definingClass : ClassId}
      (completion : p.CompleteRequest state current request message nextState
        (.invoke method receiver definingClass finalMessage)) :
      RequestCompletionStep p
        ⟨state, .push rest ⟨current, frames⟩, .dispatch request message⟩
        ⟨nextState, .push rest ⟨current, frames⟩,
          .invoke method receiver definingClass finalMessage⟩
  | invalidSuper {state : AllocationState} {rest : ActivationStack}
      {current : ActivationId} {frames : EvalStack} {request : SendRequest}
      {message : Message} {currentClass : ClassId}
      (completion : p.CompleteRequest state current request message state
        (.invalidSuper currentClass)) :
      RequestCompletionStep p
        ⟨state, .push rest ⟨current, frames⟩, .dispatch request message⟩
        ⟨state, .push rest ⟨current, frames⟩,
          .runtimeError (.invalidSuper currentClass)⟩

theorem requestCompletionStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (step₁ : p.RequestCompletionStep before after₁)
    (step₂ : p.RequestCompletionStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | invoke completion₁ =>
      cases step₂ with
      | invoke completion₂ =>
          have result := completeRequest_deterministic wf completion₁ completion₂
          rcases result with ⟨hstate, houtcome⟩
          cases hstate
          cases houtcome
          rfl
      | invalidSuper completion₂ =>
          have result := completeRequest_deterministic wf completion₁ completion₂
          cases result.2
  | invalidSuper completion₁ =>
      cases step₂ with
      | invoke completion₂ =>
          have result := completeRequest_deterministic wf completion₁ completion₂
          cases result.2
      | invalidSuper completion₂ =>
          have result := completeRequest_deterministic wf completion₁ completion₂
          cases result.2
          rfl

theorem expressionOrder_bodyMachine_disjoint {p : Program}
    {before expressionAfter bodyAfter : SequentialConfig}
    (expression : p.ExpressionOrderStep before expressionAfter)
    (body : p.BodyMachineStep before bodyAfter) : False := by
  cases body with
  | graph next =>
      cases expression with
      | value => simp [bodyMachineNext] at next
      | selfValue => simp [bodyMachineNext] at next
      | ordinaryReceiver => simp [bodyMachineNext] at next
      | eventualReceiver => simp [bodyMachineNext] at next
      | @nonOrdinary _ _ _ _ expression _ requestData =>
          cases expression <;>
            simp [nonOrdinaryRequest, bodyMachineNext] at requestData next
      | receiverValue => simp [bodyMachineNext] at next
      | eventualReceiverValue => simp [bodyMachineNext] at next
      | argumentValue => simp [bodyMachineNext] at next

theorem requestCompletion_bodyMachine_disjoint {p : Program}
    {before requestAfter bodyAfter : SequentialConfig}
    (request : p.RequestCompletionStep before requestAfter)
    (body : p.BodyMachineStep before bodyAfter) : False := by
  cases body with
  | graph next => cases request <;> simp [bodyMachineNext] at next

theorem methodInvocation_bodyMachine_disjoint {p : Program}
    {before invocationAfter bodyAfter : SequentialConfig}
    (invocation : p.MethodInvocationStep before invocationAfter)
    (body : p.BodyMachineStep before bodyAfter) : False := by
  cases body with
  | graph next => cases invocation <;> simp [bodyMachineNext] at next

theorem expressionOrder_returnMachine_disjoint {p : Program}
    {before expressionAfter returnAfter : SequentialConfig}
    (expression : p.ExpressionOrderStep before expressionAfter)
    (returns : p.ReturnMachineStep before returnAfter) : False := by
  cases returns with
  | graph next => cases expression <;> simp [returnMachineNext] at next

theorem requestCompletion_returnMachine_disjoint {p : Program}
    {before requestAfter returnAfter : SequentialConfig}
    (request : p.RequestCompletionStep before requestAfter)
    (returns : p.ReturnMachineStep before returnAfter) : False := by
  cases returns with
  | graph next => cases request <;> simp [returnMachineNext] at next

theorem methodInvocation_returnMachine_disjoint {p : Program}
    {before invocationAfter returnAfter : SequentialConfig}
    (invocation : p.MethodInvocationStep before invocationAfter)
    (returns : p.ReturnMachineStep before returnAfter) : False := by
  cases returns with
  | graph next => cases invocation <;> simp [returnMachineNext] at next

theorem bodyMachine_returnMachine_disjoint {p : Program}
    {before bodyAfter returnAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (returns : p.ReturnMachineStep before returnAfter) : False := by
  cases body with
  | graph bodyNext =>
      cases returns with
      | graph returnNext =>
          rcases before with ⟨state, stack, control⟩
          cases stack with
          | empty => simp [bodyMachineNext] at bodyNext
          | push rest currentFrame =>
              rcases currentFrame with ⟨current, frames⟩
              cases control <;>
                try { simp [bodyMachineNext, returnMachineNext] at bodyNext returnNext }
              case object =>
                cases frames with
                | empty => simp [bodyMachineNext] at bodyNext
                | push below top =>
                    cases top <;>
                      simp [bodyMachineNext, returnMachineNext] at bodyNext returnNext

theorem expressionOrder_closureMachine_disjoint {p : Program}
    {before expressionAfter closureAfter : SequentialConfig}
    (expression : p.ExpressionOrderStep before expressionAfter)
    (closure : p.ClosureMachineStep before closureAfter) : False := by
  cases closure with
  | creation creation =>
      cases creation <;> cases expression with
      | nonOrdinary requestData =>
          simp [nonOrdinaryRequest] at requestData
  | dispatch dispatch =>
      cases dispatch
      cases expression
  | invocation invocation =>
      rcases closureInvocation_control invocation with ⟨_, _, invocationControl⟩
      cases expression <;> simp at invocationControl

theorem requestCompletion_closureMachine_disjoint {p : Program}
    {before requestAfter closureAfter : SequentialConfig}
    (request : p.RequestCompletionStep before requestAfter)
    (closure : p.ClosureMachineStep before closureAfter) : False := by
  cases closure with
  | creation creation => cases creation <;> cases request
  | dispatch dispatch =>
      cases dispatch with
      | @value state _ _ _ id closureDef message live selectorMatches arityMatches =>
          have closureCall : Heap.ClosureCall state.heap
              (.closureObject id) message :=
            ⟨id, closureDef, rfl, live, selectorMatches, arityMatches⟩
          cases request with
          | invoke completion =>
              exact (completeOrdinary_notClosureCall completion) closureCall
          | invalidSuper completion =>
              exact (completeOrdinary_notClosureCall completion) closureCall
  | invocation invocation =>
      rcases closureInvocation_control invocation with ⟨_, _, invocationControl⟩
      cases request <;> simp at invocationControl

theorem methodInvocation_closureMachine_disjoint {p : Program}
    {before invocationAfter closureAfter : SequentialConfig}
    (invocation : p.MethodInvocationStep before invocationAfter)
    (closure : p.ClosureMachineStep before closureAfter) : False := by
  cases closure with
  | creation creation => cases invocation <;> cases creation
  | dispatch dispatch => cases invocation <;> cases dispatch
  | invocation closureInvocation =>
      rcases closureInvocation_control closureInvocation with
        ⟨_, _, closureControl⟩
      cases invocation <;> simp at closureControl

theorem bodyMachine_closureMachine_disjoint {p : Program}
    {before bodyAfter closureAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (closure : p.ClosureMachineStep before closureAfter) : False := by
  cases body with
  | graph next =>
      cases closure with
      | creation creation => cases creation <;> simp [bodyMachineNext] at next
      | dispatch dispatch => cases dispatch <;> simp [bodyMachineNext] at next
      | invocation invocation =>
          cases invocation <;> simp [bodyMachineNext] at next

theorem returnMachine_closureMachine_disjoint {p : Program}
    {before returnAfter closureAfter : SequentialConfig}
    (returns : p.ReturnMachineStep before returnAfter)
    (closure : p.ClosureMachineStep before closureAfter) : False := by
  cases returns with
  | graph next =>
      cases closure with
      | creation creation => cases creation <;> simp [returnMachineNext] at next
      | dispatch dispatch => cases dispatch <;> simp [returnMachineNext] at next
      | invocation invocation =>
          cases invocation <;> simp [returnMachineNext] at next

theorem expressionOrder_objectSlot_disjoint {p : Program}
    {before expressionAfter slotAfter : SequentialConfig}
    (expression : p.ExpressionOrderStep before expressionAfter)
    (slots : p.ObjectSlotStep before slotAfter) : False := by
  cases slots with
  | atom =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | read =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | writeStart =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | writeCommit => cases expression
  | currentRead =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | currentWrite =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | lazyHit =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | lazyMiss =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | lazyCommit => cases expression

theorem requestCompletion_objectSlot_disjoint {p : Program}
    {before requestAfter slotAfter : SequentialConfig}
    (request : p.RequestCompletionStep before requestAfter)
    (slots : p.ObjectSlotStep before slotAfter) : False := by
  cases slots <;> cases request

theorem methodInvocation_objectSlot_disjoint {p : Program}
    {before invocationAfter slotAfter : SequentialConfig}
    (invocation : p.MethodInvocationStep before invocationAfter)
    (slots : p.ObjectSlotStep before slotAfter) : False := by
  cases slots <;> cases invocation

theorem bodyMachine_objectSlot_disjoint {p : Program}
    {before bodyAfter slotAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (slots : p.ObjectSlotStep before slotAfter) : False := by
  cases body with
  | graph next => cases slots <;> simp [bodyMachineNext] at next

theorem returnMachine_objectSlot_disjoint {p : Program}
    {before returnAfter slotAfter : SequentialConfig}
    (returns : p.ReturnMachineStep before returnAfter)
    (slots : p.ObjectSlotStep before slotAfter) : False := by
  cases returns with
  | graph next => cases slots <;> simp [returnMachineNext] at next

theorem closureMachine_objectSlot_disjoint {p : Program}
    {before closureAfter slotAfter : SequentialConfig}
    (closure : p.ClosureMachineStep before closureAfter)
    (slots : p.ObjectSlotStep before slotAfter) : False := by
  cases closure with
  | creation creation => cases creation <;> cases slots
  | dispatch dispatch => cases dispatch <;> cases slots
  | invocation invocation => cases invocation <;> cases slots

theorem expressionOrder_classConstruction_disjoint {p : Program}
    {before expressionAfter classAfter : SequentialConfig}
    (expression : p.ExpressionOrderStep before expressionAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases classes with
  | bodyStart =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | mixinStart =>
      cases expression with
      | nonOrdinary requestData => simp [nonOrdinaryRequest] at requestData
  | bodyCommit => cases expression
  | bodyInheritanceError => cases expression
  | bodyTopError => cases expression
  | mixinSuperclassDone => cases expression
  | mixinCommit => cases expression
  | mixinSuperclassError => cases expression
  | mixinSourceError => cases expression

theorem requestCompletion_classConstruction_disjoint {p : Program}
    {before requestAfter classAfter : SequentialConfig}
    (request : p.RequestCompletionStep before requestAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases classes <;> cases request

theorem methodInvocation_classConstruction_disjoint {p : Program}
    {before invocationAfter classAfter : SequentialConfig}
    (invocation : p.MethodInvocationStep before invocationAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases classes <;> cases invocation

theorem bodyMachine_classConstruction_disjoint {p : Program}
    {before bodyAfter classAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases body with
  | graph next => cases classes <;> simp [bodyMachineNext] at next

theorem returnMachine_classConstruction_disjoint {p : Program}
    {before returnAfter classAfter : SequentialConfig}
    (returns : p.ReturnMachineStep before returnAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases returns with
  | graph next => cases classes <;> simp [returnMachineNext] at next

theorem closureMachine_classConstruction_disjoint {p : Program}
    {before closureAfter classAfter : SequentialConfig}
    (closure : p.ClosureMachineStep before closureAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases classes <;> cases closure with
  | creation creation => cases creation
  | dispatch dispatch => cases dispatch
  | invocation invocation => cases invocation

theorem objectSlot_classConstruction_disjoint {p : Program}
    {before slotAfter classAfter : SequentialConfig}
    (slots : p.ObjectSlotStep before slotAfter)
    (classes : p.ClassConstructionStep before classAfter) : False := by
  cases classes <;> cases slots

theorem expressionOrder_messageEvaluation_disjoint {p : Program}
    {before expressionAfter messageAfter : SequentialConfig}
    (expression : p.ExpressionOrderStep before expressionAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases messages <;> cases expression

theorem requestCompletion_messageEvaluation_disjoint {p : Program}
    {before requestAfter messageAfter : SequentialConfig}
    (request : p.RequestCompletionStep before requestAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases messages <;> cases request

theorem methodInvocation_messageEvaluation_disjoint {p : Program}
    {before invocationAfter messageAfter : SequentialConfig}
    (invocation : p.MethodInvocationStep before invocationAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases messages <;> cases invocation

theorem bodyMachine_messageEvaluation_disjoint {p : Program}
    {before bodyAfter messageAfter : SequentialConfig}
    (body : p.BodyMachineStep before bodyAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases body with
  | graph next => cases messages <;> simp [bodyMachineNext] at next

theorem returnMachine_messageEvaluation_disjoint {p : Program}
    {before returnAfter messageAfter : SequentialConfig}
    (returns : p.ReturnMachineStep before returnAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases returns with
  | graph next => cases messages <;> simp [returnMachineNext] at next

theorem closureMachine_messageEvaluation_disjoint {p : Program}
    {before closureAfter messageAfter : SequentialConfig}
    (closure : p.ClosureMachineStep before closureAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases messages <;> cases closure with
  | creation creation => cases creation
  | dispatch dispatch => cases dispatch
  | invocation invocation => cases invocation

theorem objectSlot_messageEvaluation_disjoint {p : Program}
    {before slotAfter messageAfter : SequentialConfig}
    (slots : p.ObjectSlotStep before slotAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases messages <;> cases slots

theorem classConstruction_messageEvaluation_disjoint {p : Program}
    {before classAfter messageAfter : SequentialConfig}
    (classes : p.ClassConstructionStep before classAfter)
    (messages : p.MessageEvaluationStep before messageAfter) : False := by
  cases messages <;> cases classes

/-- Current union of the sequential-machine rules.  Its constructors remain
    disjoint by control-term shape; later slices extend this same relation. -/
inductive SequentialStep (p : Program) :
    SequentialConfig → SequentialConfig → Prop where
  | expression {before after : SequentialConfig} :
      p.ExpressionOrderStep before after → p.SequentialStep before after
  | request {before after : SequentialConfig} :
      p.RequestCompletionStep before after → p.SequentialStep before after
  | invocation {before after : SequentialConfig} :
      p.MethodInvocationStep before after → p.SequentialStep before after
  | body {before after : SequentialConfig} :
      p.BodyMachineStep before after → p.SequentialStep before after
  | returns {before after : SequentialConfig} :
      p.ReturnMachineStep before after → p.SequentialStep before after
  | closure {before after : SequentialConfig} :
      p.ClosureMachineStep before after → p.SequentialStep before after
  | objectSlots {before after : SequentialConfig} :
      p.ObjectSlotStep before after → p.SequentialStep before after
  | classes {before after : SequentialConfig} :
      p.ClassConstructionStep before after → p.SequentialStep before after
  | messages {before after : SequentialConfig} :
      p.MessageEvaluationStep before after → p.SequentialStep before after

theorem sequentialStep_deterministic {p : Program}
    {before after₁ after₂ : SequentialConfig}
    (wf : p.WellFormed before.allocation.heap)
    (step₁ : p.SequentialStep before after₁)
    (step₂ : p.SequentialStep before after₂) : after₁ = after₂ := by
  cases step₁ with
  | expression expression₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact expressionOrderStep_deterministic expression₁ expression₂
      | request request₂ => cases expression₁ <;> cases request₂
      | invocation invocation₂ => cases expression₁ <;> cases invocation₂
      | body body₂ => exact (expressionOrder_bodyMachine_disjoint expression₁ body₂).elim
      | returns return₂ =>
          exact (expressionOrder_returnMachine_disjoint expression₁ return₂).elim
      | closure closure₂ =>
          exact (expressionOrder_closureMachine_disjoint expression₁ closure₂).elim
      | objectSlots slots₂ =>
          exact (expressionOrder_objectSlot_disjoint expression₁ slots₂).elim
      | classes classes₂ =>
          exact (expressionOrder_classConstruction_disjoint expression₁ classes₂).elim
      | messages messages₂ =>
          exact (expressionOrder_messageEvaluation_disjoint expression₁ messages₂).elim
  | request request₁ =>
      cases step₂ with
      | expression expression₂ => cases request₁ <;> cases expression₂
      | request request₂ =>
          exact requestCompletionStep_deterministic wf request₁ request₂
      | invocation invocation₂ => cases request₁ <;> cases invocation₂
      | body body₂ => exact (requestCompletion_bodyMachine_disjoint request₁ body₂).elim
      | returns return₂ =>
          exact (requestCompletion_returnMachine_disjoint request₁ return₂).elim
      | closure closure₂ =>
          exact (requestCompletion_closureMachine_disjoint request₁ closure₂).elim
      | objectSlots slots₂ =>
          exact (requestCompletion_objectSlot_disjoint request₁ slots₂).elim
      | classes classes₂ =>
          exact (requestCompletion_classConstruction_disjoint request₁ classes₂).elim
      | messages messages₂ =>
          exact (requestCompletion_messageEvaluation_disjoint request₁ messages₂).elim
  | invocation invocation₁ =>
      cases step₂ with
      | expression expression₂ => cases invocation₁ <;> cases expression₂
      | request request₂ => cases invocation₁ <;> cases request₂
      | invocation invocation₂ =>
          exact methodInvocationStep_deterministic invocation₁ invocation₂
      | body body₂ => exact (methodInvocation_bodyMachine_disjoint invocation₁ body₂).elim
      | returns return₂ =>
          exact (methodInvocation_returnMachine_disjoint invocation₁ return₂).elim
      | closure closure₂ =>
          exact (methodInvocation_closureMachine_disjoint invocation₁ closure₂).elim
      | objectSlots slots₂ =>
          exact (methodInvocation_objectSlot_disjoint invocation₁ slots₂).elim
      | classes classes₂ =>
          exact (methodInvocation_classConstruction_disjoint invocation₁ classes₂).elim
      | messages messages₂ =>
          exact (methodInvocation_messageEvaluation_disjoint invocation₁ messages₂).elim
  | body body₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact (expressionOrder_bodyMachine_disjoint expression₂ body₁).elim
      | request request₂ =>
          exact (requestCompletion_bodyMachine_disjoint request₂ body₁).elim
      | invocation invocation₂ =>
          exact (methodInvocation_bodyMachine_disjoint invocation₂ body₁).elim
      | body body₂ => exact bodyMachineStep_deterministic body₁ body₂
      | returns return₂ =>
          exact (bodyMachine_returnMachine_disjoint body₁ return₂).elim
      | closure closure₂ =>
          exact (bodyMachine_closureMachine_disjoint body₁ closure₂).elim
      | objectSlots slots₂ =>
          exact (bodyMachine_objectSlot_disjoint body₁ slots₂).elim
      | classes classes₂ =>
          exact (bodyMachine_classConstruction_disjoint body₁ classes₂).elim
      | messages messages₂ =>
          exact (bodyMachine_messageEvaluation_disjoint body₁ messages₂).elim
  | returns return₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact (expressionOrder_returnMachine_disjoint expression₂ return₁).elim
      | request request₂ =>
          exact (requestCompletion_returnMachine_disjoint request₂ return₁).elim
      | invocation invocation₂ =>
          exact (methodInvocation_returnMachine_disjoint invocation₂ return₁).elim
      | body body₂ =>
          exact (bodyMachine_returnMachine_disjoint body₂ return₁).elim
      | returns return₂ => exact returnMachineStep_deterministic return₁ return₂
      | closure closure₂ =>
          exact (returnMachine_closureMachine_disjoint return₁ closure₂).elim
      | objectSlots slots₂ =>
          exact (returnMachine_objectSlot_disjoint return₁ slots₂).elim
      | classes classes₂ =>
          exact (returnMachine_classConstruction_disjoint return₁ classes₂).elim
      | messages messages₂ =>
          exact (returnMachine_messageEvaluation_disjoint return₁ messages₂).elim
  | closure closure₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact (expressionOrder_closureMachine_disjoint expression₂ closure₁).elim
      | request request₂ =>
          exact (requestCompletion_closureMachine_disjoint request₂ closure₁).elim
      | invocation invocation₂ =>
          exact (methodInvocation_closureMachine_disjoint invocation₂ closure₁).elim
      | body body₂ =>
          exact (bodyMachine_closureMachine_disjoint body₂ closure₁).elim
      | returns return₂ =>
          exact (returnMachine_closureMachine_disjoint return₂ closure₁).elim
      | closure closure₂ =>
          exact closureMachineStep_deterministic closure₁ closure₂
      | objectSlots slots₂ =>
          exact (closureMachine_objectSlot_disjoint closure₁ slots₂).elim
      | classes classes₂ =>
          exact (closureMachine_classConstruction_disjoint closure₁ classes₂).elim
      | messages messages₂ =>
          exact (closureMachine_messageEvaluation_disjoint closure₁ messages₂).elim
  | objectSlots slots₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact (expressionOrder_objectSlot_disjoint expression₂ slots₁).elim
      | request request₂ =>
          exact (requestCompletion_objectSlot_disjoint request₂ slots₁).elim
      | invocation invocation₂ =>
          exact (methodInvocation_objectSlot_disjoint invocation₂ slots₁).elim
      | body body₂ =>
          exact (bodyMachine_objectSlot_disjoint body₂ slots₁).elim
      | returns returns₂ =>
          exact (returnMachine_objectSlot_disjoint returns₂ slots₁).elim
      | closure closure₂ =>
          exact (closureMachine_objectSlot_disjoint closure₂ slots₁).elim
      | objectSlots slots₂ => exact objectSlotStep_deterministic slots₁ slots₂
      | classes classes₂ =>
          exact (objectSlot_classConstruction_disjoint slots₁ classes₂).elim
      | messages messages₂ =>
          exact (objectSlot_messageEvaluation_disjoint slots₁ messages₂).elim
  | classes classes₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact (expressionOrder_classConstruction_disjoint expression₂ classes₁).elim
      | request request₂ =>
          exact (requestCompletion_classConstruction_disjoint request₂ classes₁).elim
      | invocation invocation₂ =>
          exact (methodInvocation_classConstruction_disjoint invocation₂ classes₁).elim
      | body body₂ =>
          exact (bodyMachine_classConstruction_disjoint body₂ classes₁).elim
      | returns returns₂ =>
          exact (returnMachine_classConstruction_disjoint returns₂ classes₁).elim
      | closure closure₂ =>
          exact (closureMachine_classConstruction_disjoint closure₂ classes₁).elim
      | objectSlots slots₂ =>
          exact (objectSlot_classConstruction_disjoint slots₂ classes₁).elim
      | classes classes₂ =>
          exact classConstructionStep_deterministic classes₁ classes₂
      | messages messages₂ =>
          exact (classConstruction_messageEvaluation_disjoint classes₁ messages₂).elim
  | messages messages₁ =>
      cases step₂ with
      | expression expression₂ =>
          exact (expressionOrder_messageEvaluation_disjoint expression₂ messages₁).elim
      | request request₂ =>
          exact (requestCompletion_messageEvaluation_disjoint request₂ messages₁).elim
      | invocation invocation₂ =>
          exact (methodInvocation_messageEvaluation_disjoint invocation₂ messages₁).elim
      | body body₂ =>
          exact (bodyMachine_messageEvaluation_disjoint body₂ messages₁).elim
      | returns returns₂ =>
          exact (returnMachine_messageEvaluation_disjoint returns₂ messages₁).elim
      | closure closure₂ =>
          exact (closureMachine_messageEvaluation_disjoint closure₂ messages₁).elim
      | objectSlots slots₂ =>
          exact (objectSlot_messageEvaluation_disjoint slots₂ messages₁).elim
      | classes classes₂ =>
          exact (classConstruction_messageEvaluation_disjoint classes₂ messages₁).elim
      | messages messages₂ =>
          exact messageEvaluationStep_deterministic messages₁ messages₂

end Program
end Newspeak
