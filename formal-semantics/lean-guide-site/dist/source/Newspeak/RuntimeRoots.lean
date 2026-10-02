import Newspeak.GarbageCollectionState

namespace Newspeak

/-! Executable root extraction for the sequential machine.  These functions
    traverse materialized syntax as well as runtime values: an atom occurring
    in suspended code denotes its canonical object and must therefore be
    retained even though the syntax node itself contains only an
    `AtomPayload`. -/

mutual
  def coreExpressionRuntimeReferences (p : Program) : CoreExpr → List ObjRef
    | .value object => [object]
    | .selfValue => []
    | .ordinarySend receiver _ arguments =>
        coreExpressionRuntimeReferences p receiver ++
          coreExpressionListRuntimeReferences p arguments
    | .eventualSend receiver _ arguments =>
        coreExpressionRuntimeReferences p receiver ++
          coreExpressionListRuntimeReferences p arguments
    | .implicitSend _ arguments _ _ =>
        coreExpressionListRuntimeReferences p arguments
    | .selfSend _ arguments _ =>
        coreExpressionListRuntimeReferences p arguments
    | .outerSend _ arguments _ _ =>
        coreExpressionListRuntimeReferences p arguments
    | .superSend _ arguments => coreExpressionListRuntimeReferences p arguments
    | .closureLiteral _ => []
    | .cascadeClosure _ clauses => cascadeClauseRuntimeReferences p clauses
    | .readLocal activation _ => [.activationObject activation]
    | .writeLocal activation _ expression =>
        .activationObject activation :: coreExpressionRuntimeReferences p expression
    | .classBody _ superclass => coreExpressionRuntimeReferences p superclass
    | .mixinApply _ superclass mixinSource =>
        coreExpressionRuntimeReferences p superclass ++
          coreExpressionRuntimeReferences p mixinSource
    | .objectLiteral _ superclass => coreExpressionRuntimeReferences p superclass
    | .atom payload => [p.atoms payload]
    | .tuple _ _ elements => coreExpressionListRuntimeReferences p elements
    | .pattern pattern _ _ => corePatternRuntimeReferences p pattern
    | .cascade _ receiver clauses =>
        coreExpressionRuntimeReferences p receiver ++
          cascadeClauseRuntimeReferences p clauses
    | .readSlot object _ => [.ordinaryObject object]
    | .writeSlot object _ expression =>
        .ordinaryObject object :: coreExpressionRuntimeReferences p expression
    | .currentRead _ => []
    | .currentWrite _ expression => coreExpressionRuntimeReferences p expression
    | .lazyRead _ initializer => coreExpressionRuntimeReferences p initializer
    | .nestedClass _ classExpression =>
        coreExpressionRuntimeReferences p classExpression
    | .newInstanceCurrent _ _ => []

  def coreExpressionListRuntimeReferences (p : Program) :
      List CoreExpr → List ObjRef
    | [] => []
    | expression :: remaining =>
        coreExpressionRuntimeReferences p expression ++
          coreExpressionListRuntimeReferences p remaining

  def cascadeClauseRuntimeReferences (p : Program) :
      List (Selector × List CoreExpr) → List ObjRef
    | [] => []
    | clause :: remaining =>
        coreExpressionListRuntimeReferences p clause.2 ++
          cascadeClauseRuntimeReferences p remaining

  def corePatternRuntimeReferences (p : Program) : CorePattern → List ObjRef
    | .wildcard => []
    | .literal expression => coreExpressionRuntimeReferences p expression
    | .variable _ => []
    | .nested pattern => corePatternRuntimeReferences p pattern
    | .keyword _ _ _ _ pairs => corePatternPairRuntimeReferences p pairs

  def corePatternPairRuntimeReferences (p : Program) :
      List (Selector × CorePattern) → List ObjRef
    | [] => []
    | pair :: remaining =>
        corePatternRuntimeReferences p pair.2 ++
          corePatternPairRuntimeReferences p remaining
end

def localDeclarationRuntimeReferences (p : Program) :
    LocalDeclaration → List ObjRef
  | .immutable _ initializer => coreExpressionRuntimeReferences p initializer
  | .mutableInitialized _ initializer => coreExpressionRuntimeReferences p initializer
  | .mutableUninitialized _ => []
  | .lazyImmutable _ initializer => coreExpressionRuntimeReferences p initializer
  | .lazyMutable _ initializer => coreExpressionRuntimeReferences p initializer

def localDeclarationGroupRuntimeReferences (p : Program) :
    LocalDeclarationGroup → List ObjRef
  | .sequential declaration => localDeclarationRuntimeReferences p declaration
  | .simultaneous declarations =>
      declarations.flatMap (localDeclarationRuntimeReferences p)

def statementRuntimeReferences (p : Program) : Statement → List ObjRef
  | .expression expression => coreExpressionRuntimeReferences p expression
  | .return expression => coreExpressionRuntimeReferences p expression

def messageTemplateRuntimeReferences (p : Program)
    (template : MessageTemplate) : List ObjRef :=
  coreExpressionListRuntimeReferences p template.arguments

def slotDeclarationRuntimeReferences (p : Program) :
    SlotDeclaration → List ObjRef
  | .immutable _ initializer _ => coreExpressionRuntimeReferences p initializer
  | .mutableInitialized _ initializer _ =>
      coreExpressionRuntimeReferences p initializer
  | .mutableUninitialized _ => []

def slotDeclarationGroupRuntimeReferences (p : Program) :
    SlotDeclarationGroup → List ObjRef
  | .sequential declarations | .simultaneous declarations =>
      declarations.flatMap (slotDeclarationRuntimeReferences p)

def classBodyDescriptorRuntimeReferences (p : Program)
    (descriptor : ClassBodyDescriptor) : List ObjRef :=
  messageTemplateRuntimeReferences p descriptor.superclassMessage

def mixinApplicationDescriptorRuntimeReferences (p : Program)
    (descriptor : MixinApplicationDescriptor) : List ObjRef :=
  messageTemplateRuntimeReferences p descriptor.superclassMessage ++
    messageTemplateRuntimeReferences p descriptor.mixinMessage

def objectLiteralDescriptorRuntimeReferences (p : Program)
    (descriptor : ObjectLiteralDescriptor) : List ObjRef :=
  messageTemplateRuntimeReferences p descriptor.superclassMessage

def actorSeedDescriptorRuntimeReferences (p : Program)
    (descriptor : ActorSeedDescriptor) : List ObjRef :=
  messageTemplateRuntimeReferences p descriptor.superclassMessage

def mixinDefinitionRuntimeReferences (p : Program)
    (mixin : MixinDef) : List ObjRef :=
  mixin.initializerGroups.flatMap (slotDeclarationGroupRuntimeReferences p) ++
    mixin.initializerBody.flatMap (statementRuntimeReferences p)

def initializationTargetRuntimeReferences : InitializationTarget → List ObjRef
  | .methodBody receiver => [receiver]
  | .closureBody => []

def sendRequestRuntimeReferences : SendRequest → List ObjRef
  | .ordinary receiver => [receiver]
  | .eventual receiver => [receiver]
  | .implicit _ _ | .outer _ _ | .self _ | .super => []

def evaluationFrameRuntimeReferences (p : Program) : EvalFrame → List ObjRef
  | .receiver _ arguments => coreExpressionListRuntimeReferences p arguments
  | .asyncReceiver _ arguments =>
      coreExpressionListRuntimeReferences p arguments
  | .arguments request _ values remaining =>
      sendRequestRuntimeReferences request ++ values ++
        coreExpressionListRuntimeReferences p remaining
  | .initializeLocal _ remaining body target =>
      remaining.flatMap (localDeclarationGroupRuntimeReferences p) ++
        body.flatMap (statementRuntimeReferences p) ++
        initializationTargetRuntimeReferences target
  | .localWrite activation _ => [.activationObject activation]
  | .slotWrite object _ | .lazySlotStore object _ => [.ordinaryObject object]
  | .makeClassBody descriptor enclosingObject =>
      enclosingObject :: classBodyDescriptorRuntimeReferences p descriptor
  | .makeObjectLiteral descriptor enclosingObject =>
      enclosingObject :: objectLiteralDescriptorRuntimeReferences p descriptor
  | .nestedClassStore object _ => [.ordinaryObject object]
  | .mixinSuperclass descriptor mixinSource =>
      mixinApplicationDescriptorRuntimeReferences p descriptor ++
        coreExpressionRuntimeReferences p mixinSource
  | .mixinSource descriptor superclass =>
      .classObject superclass ::
        mixinApplicationDescriptorRuntimeReferences p descriptor
  | .messageArguments _ values remaining =>
      values ++ coreExpressionListRuntimeReferences p remaining
  | .superclassMessage classId object original
  | .afterSuperclass classId object original =>
      [.classObject classId, .ordinaryObject object] ++ messageReferences original
  | .mixinMessage classId object | .afterMixin classId object =>
      [.classObject classId, .ordinaryObject object]
  | .storeInitializedSlot object _ remainingDeclarations remainingGroups body =>
      .ordinaryObject object ::
        (remainingDeclarations.flatMap (slotDeclarationRuntimeReferences p) ++
          remainingGroups.flatMap (slotDeclarationGroupRuntimeReferences p) ++
          body.flatMap (statementRuntimeReferences p))
  | .simultaneousSlots remainingCode object remainingGroups body =>
      .ordinaryObject object ::
        (coreExpressionListRuntimeReferences p remainingCode ++
          remainingGroups.flatMap (slotDeclarationGroupRuntimeReferences p) ++
          body.flatMap (statementRuntimeReferences p))
  | .simultaneousLocals remainingCode activation remaining body target =>
      .activationObject activation ::
        (coreExpressionListRuntimeReferences p remainingCode ++
          remaining.flatMap (localDeclarationGroupRuntimeReferences p) ++
          body.flatMap (statementRuntimeReferences p) ++
          initializationTargetRuntimeReferences target)
  | .sequence target remaining =>
      initializationTargetRuntimeReferences target ++
        remaining.flatMap (statementRuntimeReferences p)
  | .returnFrame => []

def evaluationStackRuntimeReferences (p : Program) : EvalStack → List ObjRef
  | .empty => []
  | .push rest frame =>
      evaluationStackRuntimeReferences p rest ++
        evaluationFrameRuntimeReferences p frame

def activationFrameRuntimeReferences (p : Program)
    (frame : ActivationFrame) : List ObjRef :=
  .activationObject frame.activation ::
    evaluationStackRuntimeReferences p frame.frames

def activationStackRuntimeReferences (p : Program) :
    ActivationStack → List ObjRef
  | .empty => []
  | .push rest frame =>
      activationStackRuntimeReferences p rest ++
        activationFrameRuntimeReferences p frame

def controlTermRuntimeReferences (p : Program) : ControlTerm → List ObjRef
  | .evaluate expression => coreExpressionRuntimeReferences p expression
  | .object value | .finish value | .halt value | .abort value => [value]
  | .evaluateMessage template => messageTemplateRuntimeReferences p template
  | .messageValue message => messageReferences message
  | .initClass classId object message
  | .ownInitialization classId object message =>
      [.classObject classId, .ordinaryObject object] ++ messageReferences message
  | .initializeSlotGroups object groups body =>
      .ordinaryObject object ::
        (groups.flatMap (slotDeclarationGroupRuntimeReferences p) ++
          body.flatMap (statementRuntimeReferences p))
  | .initializeSequentialSlots object declarations remainingGroups body =>
      .ordinaryObject object ::
        (declarations.flatMap (slotDeclarationRuntimeReferences p) ++
          remainingGroups.flatMap (slotDeclarationGroupRuntimeReferences p) ++
          body.flatMap (statementRuntimeReferences p))
  | .dispatch request message =>
      sendRequestRuntimeReferences request ++ messageReferences message
  | .invoke _ receiver definingClass message =>
      [receiver, .classObject definingClass] ++ messageReferences message
  | .invokeClosure closure message =>
      .closureObject closure :: messageReferences message
  | .initialize activation locals body target =>
      .activationObject activation ::
        (locals.flatMap (localDeclarationGroupRuntimeReferences p) ++
          body.flatMap (statementRuntimeReferences p) ++
          initializationTargetRuntimeReferences target)
  | .body target statements =>
      initializationTargetRuntimeReferences target ++
        statements.flatMap (statementRuntimeReferences p)
  | .transfer target value => [.activationObject target, value]
  | .throw _ | .runtimeError _ => []

namespace Program

/-- References embedded in finite static program tables.  Total auxiliary
    maps are sampled at their corresponding finite installed domains. -/
def finiteProgramRuntimeReferences (p : Program) (h : Heap) : List ObjRef :=
  p.platform.values ++
  p.mixins.values.flatMap (mixinDefinitionRuntimeReferences p) ++
  p.methodBodies.values.flatMap (List.flatMap (statementRuntimeReferences p)) ++
  p.methodBodies.domain.flatMap fun methodId =>
    (p.methodLocals methodId).flatMap
      (localDeclarationGroupRuntimeReferences p) ++
  p.closureBodies.values.flatMap (List.flatMap (statementRuntimeReferences p)) ++
  p.closureBodies.domain.flatMap fun declaration =>
    (p.closureLocals declaration).flatMap
      (localDeclarationGroupRuntimeReferences p) ++
  p.patternVariable.values.flatMap (coreExpressionRuntimeReferences p) ++
  p.classBodies.values.flatMap (classBodyDescriptorRuntimeReferences p) ++
  p.mixinApplications.values.flatMap
    (mixinApplicationDescriptorRuntimeReferences p) ++
  p.objectLiterals.values.flatMap
    (objectLiteralDescriptorRuntimeReferences p) ++
  p.actorSeeds.values.flatMap (actorSeedDescriptorRuntimeReferences p) ++
  h.activations.domain.flatMap fun activation =>
    coreExpressionRuntimeReferences p (p.pastFutureExpression activation)

/-- Conservative program roots.  Installed runtime classes and actors are
    explicit roots in this first policy: this discharges current global
    invariants without pretending that class or actor reclamation has already
    been specified. -/
def conservativeProgramRootReferences (p : Program) (h : Heap) : List ObjRef :=
  [p.nilObject,
   .classObject p.object,
   .classObject p.classClass,
   .classObject p.metaclassClass,
   .classObject p.messageMirrorClass,
   .classObject p.activationClass,
   .classObject p.closureClass] ++
  h.classes.domain.map ObjRef.classObject ++
  h.actors.domain.map ObjRef.actorObject ++
  p.finiteProgramRuntimeReferences h

end Program

/-- Complete executable roots for a sequential safe point.  `externalRoots`
    represents host/VM handles deliberately outside the language state. -/
def sequentialRuntimeRootReferences (p : Program) (config : SequentialConfig)
    (externalRoots : List ObjRef) : List ObjRef :=
  FiniteStore.deduplicated
    (externalRoots ++
      p.conservativeProgramRootReferences config.allocation.heap ++
      activationStackRuntimeReferences p config.stack ++
      controlTermRuntimeReferences p config.control)

theorem mem_sequentialRuntimeRootReferences_iff (p : Program)
    (config : SequentialConfig) (externalRoots : List ObjRef)
    (object : ObjRef) :
    object ∈ sequentialRuntimeRootReferences p config externalRoots ↔
      object ∈ externalRoots ∨
      object ∈ p.conservativeProgramRootReferences config.allocation.heap ∨
      object ∈ activationStackRuntimeReferences p config.stack ∨
      object ∈ controlTermRuntimeReferences p config.control := by
  simp [sequentialRuntimeRootReferences, FiniteStore.mem_deduplicated]

theorem sequentialRuntimeRootReferences_nodup (p : Program)
    (config : SequentialConfig) (externalRoots : List ObjRef) :
    (sequentialRuntimeRootReferences p config externalRoots).Nodup :=
  FiniteStore.deduplicated_nodup _

theorem Program.nil_mem_sequentialRuntimeRootReferences (p : Program)
    (config : SequentialConfig) (externalRoots : List ObjRef) :
    p.nilObject ∈ sequentialRuntimeRootReferences p config externalRoots := by
  simp [sequentialRuntimeRootReferences,
    Program.conservativeProgramRootReferences,
    FiniteStore.mem_deduplicated]

theorem Heap.root_mem_conditionallyReachableReferences {h : Heap}
    {roots : List ObjRef} {object : ObjRef} (root : object ∈ roots)
    (live : h.IsLiveObject object) :
    object ∈ h.conditionallyReachableReferences roots :=
  (h.mem_conditionallyReachableReferences_iff_reachable roots object).mpr
    (.root root live)

theorem Program.conservativeRoots_class_adequate (p : Program)
    (config : SequentialConfig) (externalRoots : List ObjRef) :
    p.CollectionClassRootsAdequate config.allocation.heap
      (sequentialRuntimeRootReferences p config externalRoots) := by
  intro classId classDef lookup
  apply Heap.root_mem_conditionallyReachableReferences
  · apply (mem_sequentialRuntimeRootReferences_iff
      p config externalRoots (.classObject classId)).mpr
    apply Or.inr
    apply Or.inl
    have inDomain : classId ∈ config.allocation.heap.classes.domain :=
      config.allocation.heap.classes.mem_domain_of_lookup_eq_some lookup
    have inClassRoots : (.classObject classId : ObjRef) ∈
        config.allocation.heap.classes.domain.map ObjRef.classObject :=
      List.mem_map.mpr ⟨classId, inDomain, rfl⟩
    simp [Program.conservativeProgramRootReferences, inClassRoots]
  · exact ⟨classDef.metaclass, by simp [Heap.classOf, lookup]⟩

theorem activationStackRuntimeReferences_adequate (p : Program) (h : Heap)
    (roots : List ObjRef) (stack : ActivationStack)
    (included : ∀ object, object ∈ activationStackRuntimeReferences p stack →
      object ∈ roots) (live : Program.StackLive h stack) :
    CollectionStackRootsAdequate h roots stack := by
  induction stack with
  | empty => trivial
  | push rest frame ih =>
      rcases live with ⟨restLive, activation, lookup⟩
      have restIncluded : ∀ object,
          object ∈ activationStackRuntimeReferences p rest → object ∈ roots := by
        intro object member
        apply included object
        simp [activationStackRuntimeReferences, member]
      refine ⟨ih restIncluded restLive, ?_⟩
      apply Heap.root_mem_conditionallyReachableReferences
      · apply included
        simp [activationStackRuntimeReferences, activationFrameRuntimeReferences]
      · exact ⟨activation.objectClass, by simp [Heap.classOf, lookup]⟩

theorem runtimeRoots_stack_adequate (p : Program) (config : SequentialConfig)
    (externalRoots : List ObjRef) (live : Program.StackLive
      config.allocation.heap config.stack) :
    CollectionStackRootsAdequate config.allocation.heap
      (sequentialRuntimeRootReferences p config externalRoots) config.stack := by
  apply activationStackRuntimeReferences_adequate p config.allocation.heap
    (sequentialRuntimeRootReferences p config externalRoots) config.stack
  · intro object member
    exact (mem_sequentialRuntimeRootReferences_iff
      p config externalRoots object).mpr (Or.inr (Or.inr (Or.inl member)))
  · exact live

/-- Collection using roots computed from the concrete safe-point state. -/
def SequentialConfig.collectGarbageFromRuntimeRoots (p : Program)
    (config : SequentialConfig) (externalRoots : List ObjRef) :
    SequentialConfig :=
  config.collectGarbage
    (sequentialRuntimeRootReferences p config externalRoots) p.nilObject

theorem Program.SequentialWellFormed.collectGarbageFromRuntimeRoots_wellFormed
    {p : Program} {config : SequentialConfig}
    (wf : Program.SequentialWellFormed p config)
    (externalRoots : List ObjRef) :
    Program.SequentialWellFormed p
      (config.collectGarbageFromRuntimeRoots p externalRoots) := by
  exact wf.collectGarbage_wellFormed
    (sequentialRuntimeRootReferences p config externalRoots) p.nilObject
    (p.conservativeRoots_class_adequate config externalRoots)
    (runtimeRoots_stack_adequate p config externalRoots wf.stack)

theorem Program.collectGarbageFromRuntimeRoots_weakContainersWellFormed
    {p : Program} {config : SequentialConfig}
    (nilLive : config.allocation.heap.IsLiveObject p.nilObject)
    (externalRoots : List ObjRef) :
    Heap.WeakContainersWellFormed
      (config.collectGarbageFromRuntimeRoots p externalRoots).allocation.heap := by
  exact config.allocation.heap.collectHeap_weakContainersWellFormed
    (sequentialRuntimeRootReferences p config externalRoots) p.nilObject
    (p.nil_mem_sequentialRuntimeRootReferences config externalRoots) nilLive

end Newspeak
