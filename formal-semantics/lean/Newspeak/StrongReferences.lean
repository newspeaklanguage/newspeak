import Newspeak.HeapEnumeration

namespace Newspeak

/-! Exact structural reference extraction for the base sequential heap.
WeakArray and WeakMap observations are intentionally absent: their weak and
conditional edges belong to the optional GC overlay, not this unconditional
strong graph. -/

mutual
  def coreExpressionReferences : CoreExpr → List ObjRef
    | .value object => [object]
    | .selfValue => []
    | .ordinarySend receiver _ arguments =>
        coreExpressionReferences receiver ++
          coreExpressionListReferences arguments
    | .eventualSend receiver _ arguments =>
        coreExpressionReferences receiver ++
          coreExpressionListReferences arguments
    | .implicitSend _ arguments _ _ =>
        coreExpressionListReferences arguments
    | .selfSend _ arguments _ => coreExpressionListReferences arguments
    | .outerSend _ arguments _ _ =>
        coreExpressionListReferences arguments
    | .superSend _ arguments => coreExpressionListReferences arguments
    | .closureLiteral _ => []
    | .cascadeClosure _ clauses => cascadeClauseReferences clauses
    | .readLocal activation _ => [.activationObject activation]
    | .writeLocal activation _ expression =>
        .activationObject activation :: coreExpressionReferences expression
    | .classBody _ superclass => coreExpressionReferences superclass
    | .mixinApply _ superclass mixinSource =>
        coreExpressionReferences superclass ++
          coreExpressionReferences mixinSource
    | .objectLiteral _ superclass => coreExpressionReferences superclass
    | .atom _ => []
    | .tuple _ _ elements => coreExpressionListReferences elements
    | .pattern pattern _ _ => corePatternReferences pattern
    | .cascade _ receiver clauses =>
        coreExpressionReferences receiver ++
          cascadeClauseReferences clauses
    | .readSlot object _ => [.ordinaryObject object]
    | .writeSlot object _ expression =>
        .ordinaryObject object :: coreExpressionReferences expression
    | .currentRead _ => []
    | .currentWrite _ expression => coreExpressionReferences expression
    | .lazyRead _ initializer => coreExpressionReferences initializer
    | .nestedClass _ classExpression =>
        coreExpressionReferences classExpression
    | .newInstanceCurrent _ _ => []

  def coreExpressionListReferences : List CoreExpr → List ObjRef
    | [] => []
    | expression :: remaining =>
        coreExpressionReferences expression ++
          coreExpressionListReferences remaining

  def cascadeClauseReferences :
      List (Selector × List CoreExpr) → List ObjRef
    | [] => []
    | clause :: remaining =>
        coreExpressionListReferences clause.2 ++
          cascadeClauseReferences remaining

  def corePatternReferences : CorePattern → List ObjRef
    | .wildcard => []
    | .literal expression => coreExpressionReferences expression
    | .variable _ => []
    | .nested pattern => corePatternReferences pattern
    | .keyword _ _ _ _ pairs => corePatternPairReferences pairs

  def corePatternPairReferences :
      List (Selector × CorePattern) → List ObjRef
    | [] => []
    | pair :: remaining =>
        corePatternReferences pair.2 ++
          corePatternPairReferences remaining
end

def localDeclarationReferences : LocalDeclaration → List ObjRef
  | .immutable _ initializer => coreExpressionReferences initializer
  | .mutableInitialized _ initializer => coreExpressionReferences initializer
  | .mutableUninitialized _ => []
  | .lazyImmutable _ initializer => coreExpressionReferences initializer
  | .lazyMutable _ initializer => coreExpressionReferences initializer

def localDeclarationGroupReferences : LocalDeclarationGroup → List ObjRef
  | .sequential declaration => localDeclarationReferences declaration
  | .simultaneous declarations =>
      declarations.flatMap localDeclarationReferences

def statementReferences : Statement → List ObjRef
  | .expression expression => coreExpressionReferences expression
  | .return expression => coreExpressionReferences expression

def messageReferences (message : Message) : List ObjRef :=
  message.arguments

def localCellReferences : LocalCell → List ObjRef
  | .uninitialized => []
  | .value object => [object]

def optionalClassReference : Option ClassId → List ObjRef
  | none => []
  | some classId => [.classObject classId]

def optionalActivationReference : Option ActivationId → List ObjRef
  | none => []
  | some activation => [.activationObject activation]

def mirrorPayloadReferences : MirrorPayload → List ObjRef
  | .message message => messageReferences message
  | .authority authority =>
      match authority.target with
      | .mixinTarget mixin => [.mixinObject mixin]
      | .classTarget classId => [.classObject classId]
      | .objectTarget object => [object]
      | .activationTarget activation => [.activationObject activation]
      | .actorTarget actor => [.actorObject actor]
      | .vmTarget _ | .programTarget | .methodTarget _ => []
  | .opaque => []

/-- Unconditional references structurally stored by a runtime class record. -/
def classRecordStrongReferences (classDef : ClassDef) : List ObjRef :=
  FiniteStore.deduplicated
    [.mixinObject classDef.mixin,
     .classObject classDef.superclass,
     classDef.enclosingObject,
     .classObject classDef.metaclass]

def ordinaryObjectRecordStrongReferences (objectDef : ObjectDef) : List ObjRef :=
  FiniteStore.deduplicated
    ([.classObject objectDef.classId] ++ objectDef.slots.values ++
      objectDef.nestedClasses.values.map ObjRef.classObject)

def activationRecordStrongReferences
    (activation : ActivationDef) : List ObjRef :=
  FiniteStore.deduplicated
    ([.classObject activation.objectClass] ++
      activation.parameters.values ++
      activation.locals.values.flatMap localCellReferences ++
      [activation.currentReceiver] ++
      optionalClassReference activation.currentClass ++
      optionalActivationReference activation.continuation ++
      optionalActivationReference activation.homeMethod ++
      activation.activationScopes.values.map ObjRef.activationObject ++
      activation.objectLiteralScopes.values)

def closureRecordStrongReferences (closure : ClosureDef) : List ObjRef :=
  FiniteStore.deduplicated
    ([.classObject closure.classId,
      .activationObject closure.definingActivation,
      closure.capturedReceiver] ++
      optionalClassReference closure.capturedClass ++
      optionalActivationReference closure.homeMethod ++
      closure.locals.flatMap localDeclarationGroupReferences ++
      closure.body.flatMap statementReferences)

def mirrorRecordStrongReferences (mirror : MirrorDef) : List ObjRef :=
  FiniteStore.deduplicated
    (.classObject mirror.classId :: mirrorPayloadReferences mirror.payload)

def actorRecordStrongReferences (actor : ActorDef) : List ObjRef :=
  [.classObject actor.classId]

namespace Heap

/-- Structural references in one heap payload, before intersecting them with
the current collectable-store domain. -/
def recordStrongReferences (h : Heap) : ObjRef → List ObjRef
  | .ordinaryObject id =>
      match h.objects id with
      | none => []
      | some objectDef => ordinaryObjectRecordStrongReferences objectDef
  | .classObject id =>
      match h.classes id with
      | none => []
      | some classDef => classRecordStrongReferences classDef
  | .mixinObject id =>
      match h.mixinObjects id with
      | none => []
      | some classId => [.classObject classId]
  | .activationObject id =>
      match h.activations id with
      | none => []
      | some activation => activationRecordStrongReferences activation
  | .closureObject id =>
      match h.closures id with
      | none => []
      | some closure => closureRecordStrongReferences closure
  | .mirrorObject id =>
      match h.mirrors id with
      | none => []
      | some mirror => mirrorRecordStrongReferences mirror
  | .actorObject id =>
      match h.actors id with
      | none => []
      | some actor => actorRecordStrongReferences actor

@[simp] theorem recordStrongReferences_ordinary_present (h : Heap)
    (id : ObjectId) (objectDef : ObjectDef)
    (lookup : h.objects id = some objectDef) :
    h.recordStrongReferences (.ordinaryObject id) =
      ordinaryObjectRecordStrongReferences objectDef := by
  simp [recordStrongReferences, lookup]

@[simp] theorem recordStrongReferences_class_present (h : Heap)
    (id : ClassId) (classDef : ClassDef)
    (lookup : h.classes id = some classDef) :
    h.recordStrongReferences (.classObject id) =
      classRecordStrongReferences classDef := by
  simp [recordStrongReferences, lookup]

@[simp] theorem recordStrongReferences_mixin_present (h : Heap)
    (id : MixinId) (classId : ClassId)
    (lookup : h.mixinObjects id = some classId) :
    h.recordStrongReferences (.mixinObject id) = [.classObject classId] := by
  simp [recordStrongReferences, lookup]

@[simp] theorem recordStrongReferences_activation_present (h : Heap)
    (id : ActivationId) (activation : ActivationDef)
    (lookup : h.activations id = some activation) :
    h.recordStrongReferences (.activationObject id) =
      activationRecordStrongReferences activation := by
  simp [recordStrongReferences, lookup]

@[simp] theorem recordStrongReferences_closure_present (h : Heap)
    (id : ClosureId) (closure : ClosureDef)
    (lookup : h.closures id = some closure) :
    h.recordStrongReferences (.closureObject id) =
      closureRecordStrongReferences closure := by
  simp [recordStrongReferences, lookup]

@[simp] theorem recordStrongReferences_mirror_present (h : Heap)
    (id : MirrorId) (mirror : MirrorDef)
    (lookup : h.mirrors id = some mirror) :
    h.recordStrongReferences (.mirrorObject id) =
      mirrorRecordStrongReferences mirror := by
  simp [recordStrongReferences, lookup]

@[simp] theorem recordStrongReferences_actor_present (h : Heap)
    (id : ActorId) (actor : ActorDef)
    (lookup : h.actors id = some actor) :
    h.recordStrongReferences (.actorObject id) =
      actorRecordStrongReferences actor := by
  simp [recordStrongReferences, lookup]

def isLiveObject (h : Heap) (object : ObjRef) : Bool :=
  (h.classOf object).isSome

@[simp] theorem isLiveObject_eq_true_iff (h : Heap) (object : ObjRef) :
    h.isLiveObject object = true ↔ h.IsLiveObject object := by
  cases result : h.classOf object <;> simp [isLiveObject, IsLiveObject, result]

/-- Equation `strongSucc`, specialized to the current sequential heap. -/
def strongSuccessors (h : Heap) (source : ObjRef) : List ObjRef :=
  FiniteStore.deduplicated
    ((h.recordStrongReferences source).filter h.isLiveObject)

@[simp] theorem mem_strongSuccessors_iff (h : Heap)
    (source target : ObjRef) :
    target ∈ h.strongSuccessors source ↔
      target ∈ h.recordStrongReferences source ∧ h.IsLiveObject target := by
  simp [strongSuccessors, FiniteStore.mem_deduplicated,
    isLiveObject_eq_true_iff]

theorem strongSuccessors_nodup (h : Heap) (source : ObjRef) :
    (h.strongSuccessors source).Nodup :=
  FiniteStore.deduplicated_nodup _

theorem strongSuccessors_are_live (h : Heap) (source target : ObjRef)
    (member : target ∈ h.strongSuccessors source) :
    h.IsLiveObject target :=
  (h.mem_strongSuccessors_iff source target).mp member |>.2

def StrongReferenceEdge (h : Heap) (source target : ObjRef) : Prop :=
  target ∈ h.strongSuccessors source

/-- Finite direct roots, intersected with the current collectable domain. -/
def liveRootReferences (h : Heap) (roots : List ObjRef) : List ObjRef :=
  FiniteStore.deduplicated (roots.filter h.isLiveObject)

@[simp] theorem mem_liveRootReferences_iff (h : Heap)
    (roots : List ObjRef) (object : ObjRef) :
    object ∈ h.liveRootReferences roots ↔
      object ∈ roots ∧ h.IsLiveObject object := by
  simp [liveRootReferences, FiniteStore.mem_deduplicated,
    isLiveObject_eq_true_iff]

/-- One executable iteration of the unconditional strong-reachability
equation. -/
def extendStrongReachability (h : Heap) (reached : List ObjRef) : List ObjRef :=
  FiniteStore.deduplicated
    (reached ++ reached.flatMap h.strongSuccessors)

@[simp] theorem mem_extendStrongReachability_iff (h : Heap)
    (reached : List ObjRef) (target : ObjRef) :
    target ∈ h.extendStrongReachability reached ↔
      target ∈ reached ∨
        ∃ source, source ∈ reached ∧
          target ∈ h.strongSuccessors source := by
  simp [extendStrongReachability, FiniteStore.mem_deduplicated,
    List.mem_flatMap]

def strongReachabilityAt (h : Heap) (roots : List ObjRef) :
    Nat → List ObjRef
  | 0 => h.liveRootReferences roots
  | depth + 1 => h.extendStrongReachability
      (h.strongReachabilityAt roots depth)

def StronglyReachableWithin (h : Heap) (roots : List ObjRef) :
    Nat → ObjRef → Prop
  | 0, target => target ∈ roots ∧ h.IsLiveObject target
  | depth + 1, target =>
      h.StronglyReachableWithin roots depth target ∨
        ∃ source, h.StronglyReachableWithin roots depth source ∧
          h.StrongReferenceEdge source target

@[simp] theorem mem_strongReachabilityAt_iff (h : Heap)
    (roots : List ObjRef) (depth : Nat) (target : ObjRef) :
    target ∈ h.strongReachabilityAt roots depth ↔
      h.StronglyReachableWithin roots depth target := by
  induction depth generalizing target with
  | zero => simp [strongReachabilityAt, StronglyReachableWithin]
  | succ depth ih =>
      simp [strongReachabilityAt, StronglyReachableWithin,
        StrongReferenceEdge, ih]

theorem strongReachabilityAt_nodup (h : Heap) (roots : List ObjRef)
    (depth : Nat) : (h.strongReachabilityAt roots depth).Nodup := by
  cases depth with
  | zero => exact FiniteStore.deduplicated_nodup _
  | succ depth => exact FiniteStore.deduplicated_nodup _

theorem strongReachabilityAt_objects_are_live (h : Heap)
    (roots : List ObjRef) (depth : Nat) (target : ObjRef)
    (member : target ∈ h.strongReachabilityAt roots depth) :
    h.IsLiveObject target := by
  induction depth with
  | zero =>
      exact (h.mem_liveRootReferences_iff roots target).mp member |>.2
  | succ depth ih =>
      rcases (h.mem_extendStrongReachability_iff
        (h.strongReachabilityAt roots depth) target).mp member with
        previous | ⟨source, _sourceReached, successor⟩
      · exact ih previous
      · exact h.strongSuccessors_are_live source target successor

/-- The finite-store bound used by the executable base reachability pass.
`StrongReachabilityProofs` proves that this bound has stabilized and is the
least set containing the roots and closed under strong edges. -/
def stronglyReachableReferences (h : Heap) (roots : List ObjRef) : List ObjRef :=
  h.strongReachabilityAt roots h.liveObjectReferences.length

@[simp] theorem mem_stronglyReachableReferences_iff (h : Heap)
    (roots : List ObjRef) (target : ObjRef) :
    target ∈ h.stronglyReachableReferences roots ↔
      h.StronglyReachableWithin roots h.liveObjectReferences.length target := by
  exact h.mem_strongReachabilityAt_iff roots _ target

theorem stronglyReachableReferences_nodup (h : Heap)
    (roots : List ObjRef) :
    (h.stronglyReachableReferences roots).Nodup :=
  h.strongReachabilityAt_nodup roots _

theorem stronglyReachableReferences_are_live (h : Heap)
    (roots : List ObjRef) (target : ObjRef)
    (member : target ∈ h.stronglyReachableReferences roots) :
    h.IsLiveObject target :=
  h.strongReachabilityAt_objects_are_live roots _ target member

end Heap
end Newspeak
