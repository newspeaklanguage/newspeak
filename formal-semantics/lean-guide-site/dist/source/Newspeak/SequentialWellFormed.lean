import Newspeak.SequentialStep

namespace Newspeak
namespace Program

theorem classChain_of_classes_eq {p : Program} {h h' : Heap}
    (classesEq : h'.classes = h.classes) {c : ClassId}
    {chain : List ClassId} (witness : p.ClassChain h c chain) :
    p.ClassChain h' c chain := by
  induction witness with
  | top => exact .top
  | @step c parent tail notTop superclass _ ih =>
      exact .step notTop (by
        simpa [Program.superclass?, classesEq] using superclass) ih

theorem WellFormed.of_classes_eq {p : Program} {h h' : Heap}
    (wf : p.WellFormed h) (classesEq : h'.classes = h.classes)
    (objectClassesAreLive : ∀ object classId,
      h'.classOf object = some classId → p.IsLiveClass h' classId)
    (activationCurrentClassesAreLive : ∀ activationId activation,
      h'.activations activationId = some activation →
        p.OptionalClassLive h' activation.currentClass)
    (closureCapturedClassesAreLive : ∀ closureId closure,
      h'.closures closureId = some closure →
        p.OptionalClassLive h' closure.capturedClass) :
    p.WellFormed h' := by
  have live_iff (classId : ClassId) :
      p.IsLiveClass h' classId ↔ p.IsLiveClass h classId := by
    simp [Program.IsLiveClass, classesEq]
  refine
    { toLookupWellFormed := ?_
      objectIsNotTop := wf.objectIsNotTop
      messageMirrorClassIsLive := (live_iff _).mpr wf.messageMirrorClassIsLive
      activationClassIsLive := (live_iff _).mpr wf.activationClassIsLive
      closureClassIsLive := (live_iff _).mpr wf.closureClassIsLive
      atomCanonical := wf.atomCanonical
      objectClassesAreLive := objectClassesAreLive
      activationCurrentClassesAreLive := activationCurrentClassesAreLive
      closureCapturedClassesAreLive := closureCapturedClassesAreLive
      directSelectorCoherent := ?_
      directOwnerCoherent := ?_
      declarationMixinCoherent := wf.declarationMixinCoherent }
  · refine
      { topHasNoClassRecord := by simpa [classesEq] using wf.topHasNoClassRecord
        objectIsLive := (live_iff _).mpr wf.objectIsLive
        classHasMixin := ?_
        superclassIsLive := ?_
        chainsEndAtTop := ?_ }
    · intro c classDef live
      exact wf.classHasMixin c classDef (by simpa [classesEq] using live)
    · intro c parent superclass
      have oldSuperclass : p.superclass? h c = some parent := by
        simpa [Program.superclass?, classesEq] using superclass
      exact (live_iff _).mpr (wf.superclassIsLive c parent oldSuperclass)
    · intro c live
      have oldLive : p.IsLiveClass h c := (live_iff _).mp live
      rcases wf.chainsEndAtTop c oldLive with ⟨chain, witness⟩
      exact ⟨chain, classChain_of_classes_eq classesEq witness⟩
  · intro c selector method direct
    apply wf.directSelectorCoherent c selector method
    simpa [Program.direct, classesEq] using direct
  · intro c classDef mixinDef selector method classLive mixinLive methodLive
    exact wf.directOwnerCoherent c classDef mixinDef selector method
      (by simpa [classesEq] using classLive) mixinLive methodLive

theorem WellFormed.installActivation_wellFormed {p : Program} {h : Heap}
    (wf : p.WellFormed h) {id : ActivationId} {activation : ActivationDef}
    (objectClassLive : p.IsLiveClass h activation.objectClass)
    (currentClass : p.OptionalClassLive h activation.currentClass) :
    p.WellFormed (h.installActivation id activation) := by
  have carryLive {classId : ClassId} (live : p.IsLiveClass h classId) :
      p.IsLiveClass (h.installActivation id activation) classId := by
    simpa [Program.IsLiveClass, Heap.installActivation] using live
  apply wf.of_classes_eq (h' := h.installActivation id activation) rfl
  · intro object classId live
    cases object with
    | activationObject candidate =>
        by_cases atId : candidate = id
        · subst candidate
          simp [Heap.classOf, Heap.installActivation] at live
          subst classId
          exact carryLive objectClassLive
        · have oldLive : h.classOf (.activationObject candidate) =
              some classId := by
            simpa [Heap.classOf, Heap.installActivation, atId] using live
          exact carryLive (wf.objectClassesAreLive
            (.activationObject candidate) classId oldLive)
    | ordinaryObject candidate =>
        exact carryLive (wf.objectClassesAreLive (.ordinaryObject candidate)
          classId (by simpa [Heap.classOf, Heap.installActivation] using live))
    | classObject candidate =>
        exact carryLive (wf.objectClassesAreLive (.classObject candidate)
          classId (by simpa [Heap.classOf, Heap.installActivation] using live))
    | mixinObject candidate =>
        exact carryLive (wf.objectClassesAreLive (.mixinObject candidate)
          classId (by simpa [Heap.classOf, Heap.installActivation] using live))
    | closureObject candidate =>
        exact carryLive (wf.objectClassesAreLive (.closureObject candidate)
          classId (by simpa [Heap.classOf, Heap.installActivation] using live))
    | mirrorObject candidate =>
        exact carryLive (wf.objectClassesAreLive (.mirrorObject candidate)
          classId (by simpa [Heap.classOf, Heap.installActivation] using live))
    | actorObject candidate =>
        exact carryLive (wf.objectClassesAreLive (.actorObject candidate)
          classId (by simpa [Heap.classOf, Heap.installActivation] using live))
  · intro candidate candidateDef live
    by_cases atId : candidate = id
    · subst candidate
      simp [Heap.installActivation] at live
      subst candidateDef
      simpa [OptionalClassLive, Program.IsLiveClass,
        Heap.installActivation] using currentClass
    · have oldLive : h.activations candidate = some candidateDef := by
        simpa [Heap.installActivation, atId] using live
      simpa [OptionalClassLive, Program.IsLiveClass,
        Heap.installActivation] using
        wf.activationCurrentClassesAreLive candidate candidateDef oldLive
  · intro closureId closure live
    simpa [OptionalClassLive, Program.IsLiveClass,
      Heap.installActivation] using
      wf.closureCapturedClassesAreLive closureId closure (by
        simpa [Heap.installActivation] using live)

theorem WellFormed.installClosure_wellFormed {p : Program} {h : Heap}
    (wf : p.WellFormed h) {id : ClosureId} {closure : ClosureDef}
    (objectClassLive : p.IsLiveClass h closure.classId)
    (capturedClass : p.OptionalClassLive h closure.capturedClass) :
    p.WellFormed (h.installClosure id closure) := by
  have carryLive {classId : ClassId} (live : p.IsLiveClass h classId) :
      p.IsLiveClass (h.installClosure id closure) classId := by
    simpa [Program.IsLiveClass, Heap.installClosure] using live
  apply wf.of_classes_eq (h' := h.installClosure id closure) rfl
  · intro object classId live
    cases object with
    | closureObject candidate =>
        by_cases atId : candidate = id
        · subst candidate
          simp [Heap.classOf, Heap.installClosure] at live
          subst classId
          exact carryLive objectClassLive
        · exact carryLive (wf.objectClassesAreLive (.closureObject candidate)
            classId (by
              simpa [Heap.classOf, Heap.installClosure, atId] using live))
    | ordinaryObject candidate => exact carryLive (wf.objectClassesAreLive
        (.ordinaryObject candidate) classId (by
          simpa [Heap.classOf, Heap.installClosure] using live))
    | classObject candidate => exact carryLive (wf.objectClassesAreLive
        (.classObject candidate) classId (by
          simpa [Heap.classOf, Heap.installClosure] using live))
    | mixinObject candidate => exact carryLive (wf.objectClassesAreLive
        (.mixinObject candidate) classId (by
          simpa [Heap.classOf, Heap.installClosure] using live))
    | activationObject candidate => exact carryLive (wf.objectClassesAreLive
        (.activationObject candidate) classId (by
          simpa [Heap.classOf, Heap.installClosure] using live))
    | mirrorObject candidate => exact carryLive (wf.objectClassesAreLive
        (.mirrorObject candidate) classId (by
          simpa [Heap.classOf, Heap.installClosure] using live))
    | actorObject candidate => exact carryLive (wf.objectClassesAreLive
        (.actorObject candidate) classId (by
          simpa [Heap.classOf, Heap.installClosure] using live))
  · intro activationId activation live
    simpa [OptionalClassLive, Program.IsLiveClass, Heap.installClosure] using
      wf.activationCurrentClassesAreLive activationId activation
        (by simpa [Heap.installClosure] using live)
  · intro candidate candidateDef live
    by_cases atId : candidate = id
    · subst candidate
      simp [Heap.installClosure] at live
      subst candidateDef
      simpa [OptionalClassLive, Program.IsLiveClass, Heap.installClosure] using
        capturedClass
    · simpa [OptionalClassLive, Program.IsLiveClass, Heap.installClosure] using
        wf.closureCapturedClassesAreLive candidate candidateDef
          (by simpa [Heap.installClosure, atId] using live)

theorem WellFormed.installMirror_wellFormed {p : Program} {h : Heap}
    (wf : p.WellFormed h) {id : MirrorId} {mirror : MirrorDef}
    (objectClassLive : p.IsLiveClass h mirror.classId) :
    p.WellFormed (h.installMirror id mirror) := by
  have carryLive {classId : ClassId} (live : p.IsLiveClass h classId) :
      p.IsLiveClass (h.installMirror id mirror) classId := by
    simpa [Program.IsLiveClass, Heap.installMirror] using live
  apply wf.of_classes_eq (h' := h.installMirror id mirror) rfl
  · intro object classId live
    cases object with
    | mirrorObject candidate =>
        by_cases atId : candidate = id
        · subst candidate
          simp [Heap.classOf, Heap.installMirror] at live
          subst classId
          exact carryLive objectClassLive
        · exact carryLive (wf.objectClassesAreLive (.mirrorObject candidate)
            classId (by
              simpa [Heap.classOf, Heap.installMirror, atId] using live))
    | ordinaryObject candidate => exact carryLive (wf.objectClassesAreLive
        (.ordinaryObject candidate) classId (by
          simpa [Heap.classOf, Heap.installMirror] using live))
    | classObject candidate => exact carryLive (wf.objectClassesAreLive
        (.classObject candidate) classId (by
          simpa [Heap.classOf, Heap.installMirror] using live))
    | mixinObject candidate => exact carryLive (wf.objectClassesAreLive
        (.mixinObject candidate) classId (by
          simpa [Heap.classOf, Heap.installMirror] using live))
    | activationObject candidate => exact carryLive (wf.objectClassesAreLive
        (.activationObject candidate) classId (by
          simpa [Heap.classOf, Heap.installMirror] using live))
    | closureObject candidate => exact carryLive (wf.objectClassesAreLive
        (.closureObject candidate) classId (by
          simpa [Heap.classOf, Heap.installMirror] using live))
    | actorObject candidate => exact carryLive (wf.objectClassesAreLive
        (.actorObject candidate) classId (by
          simpa [Heap.classOf, Heap.installMirror] using live))
  · intro activationId activation live
    simpa [OptionalClassLive, Program.IsLiveClass, Heap.installMirror] using
      wf.activationCurrentClassesAreLive activationId activation
        (by simpa [Heap.installMirror] using live)
  · intro closureId closure live
    simpa [OptionalClassLive, Program.IsLiveClass, Heap.installMirror] using
      wf.closureCapturedClassesAreLive closureId closure (by
        simpa [Heap.installMirror] using live)

theorem unrestrictedLookupResultClass_live_aux {p : Program} {h : Heap}
    (wf : p.WellFormed h) {selector : Selector} {start : ClassId}
    {outcome : Option LookupResult} (startLive : p.IsLiveClass h start)
    (rules : p.UnrestrictedLookupRules h selector start outcome)
    {result : LookupResult} (outcomeEq : outcome = some result) :
    p.IsLiveClass h result.definingClass := by
  induction rules generalizing result with
  | top => simp at outcomeEq
  | here _ _ =>
      cases Option.some.inj outcomeEq
      exact startLive
  | @super c parent _ _ _ superclass _ ih =>
      exact ih (wf.superclassIsLive c parent superclass) outcomeEq

theorem publicLookupResultClass_live_aux {p : Program} {h : Heap}
    (wf : p.WellFormed h) {selector : Selector} {start : ClassId}
    {outcome : Option LookupResult} (startLive : p.IsLiveClass h start)
    (rules : p.PublicLookupRules h selector start outcome)
    {result : LookupResult} (outcomeEq : outcome = some result) :
    p.IsLiveClass h result.definingClass := by
  induction rules generalizing result with
  | top => simp at outcomeEq
  | hit _ _ _ =>
      cases Option.some.inj outcomeEq
      exact startLive
  | protectedBarrier _ _ _ => simp at outcomeEq
  | @superAbsent c parent _ _ _ superclass _ ih =>
      exact ih (wf.superclassIsLive c parent superclass) outcomeEq
  | @superPrivate c parent _ _ _ _ _ superclass _ ih =>
      exact ih (wf.superclassIsLive c parent superclass) outcomeEq

theorem protectedLookupResultClass_live_aux {p : Program} {h : Heap}
    (wf : p.WellFormed h) {selector : Selector} {start : ClassId}
    {outcome : Option LookupResult} (startLive : p.IsLiveClass h start)
    (rules : p.ProtectedLookupRules h selector start outcome)
    {result : LookupResult} (outcomeEq : outcome = some result) :
    p.IsLiveClass h result.definingClass := by
  induction rules generalizing result with
  | top => simp at outcomeEq
  | hitPublic _ _ _ =>
      cases Option.some.inj outcomeEq
      exact startLive
  | hitProtected _ _ _ =>
      cases Option.some.inj outcomeEq
      exact startLive
  | @superAbsent c parent _ _ _ superclass _ ih =>
      exact ih (wf.superclassIsLive c parent superclass) outcomeEq
  | @superPrivate c parent _ _ _ _ _ superclass _ ih =>
      exact ih (wf.superclassIsLive c parent superclass) outcomeEq

theorem unrestrictedLookupResultClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {selector : Selector} {start : ClassId}
    {result : LookupResult} (startLive : p.IsLiveClass h start)
    (rules : p.UnrestrictedLookupRules h selector start (some result)) :
    p.IsLiveClass h result.definingClass :=
  unrestrictedLookupResultClass_live_aux wf startLive rules rfl

theorem publicLookupResultClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {selector : Selector} {start : ClassId}
    {result : LookupResult} (startLive : p.IsLiveClass h start)
    (rules : p.PublicLookupRules h selector start (some result)) :
    p.IsLiveClass h result.definingClass :=
  publicLookupResultClass_live_aux wf startLive rules rfl

theorem protectedLookupResultClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {selector : Selector} {start : ClassId}
    {result : LookupResult} (startLive : p.IsLiveClass h start)
    (rules : p.ProtectedLookupRules h selector start (some result)) :
    p.IsLiveClass h result.definingClass :=
  protectedLookupResultClass_live_aux wf startLive rules rfl

theorem ClassChain.member_live {p : Program} {h : Heap}
    (_wf : p.WellFormed h) {start : ClassId} {chain : List ClassId}
    (witness : p.ClassChain h start chain) {classId : ClassId}
    (member : classId ∈ chain) : p.IsLiveClass h classId := by
  induction witness with
  | top =>
      simp at member
      subst classId
      exact Or.inl rfl
  | @step c parent tail notTop superclass tailWitness ih =>
      simp at member
      rcases member with rfl | member
      · cases liveClass : h.classes classId with
        | none => simp [Program.superclass?, notTop, liveClass] at superclass
        | some classDef => exact Or.inr ⟨classDef, liveClass⟩
      · exact ih member

theorem nearestApplicationOnChain_mem {p : Program} {h : Heap}
    {target : ClassDeclId} {chain : List ClassId} {classId : ClassId}
    (found : p.nearestApplicationOnChain h target chain = some classId) :
    classId ∈ chain := by
  induction chain with
  | nil => simp [Program.nearestApplicationOnChain] at found
  | cons head tail ih =>
      simp only [Program.nearestApplicationOnChain] at found
      split at found
      · contradiction
      · split at found
        · have equal := Option.some.inj found
          subst classId
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem head (ih found)

theorem ClassChain.start_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {start : ClassId} {chain : List ClassId}
    (witness : p.ClassChain h start chain) : p.IsLiveClass h start := by
  apply witness.member_live wf
  cases witness <;> simp

theorem targetApplicationClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {receiver : ObjRef} {target : ClassDeclId}
    {classId : ClassId}
    (application : p.TargetApplication h receiver target (some classId)) :
    p.IsLiveClass h classId := by
  rcases application with ⟨receiverClass, _, chain, witness, found⟩
  exact witness.member_live wf (nearestApplicationOnChain_mem found)

theorem ordinaryDispatch_invocationClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {receiver invocationReceiver : ObjRef}
    {message invocationMessage : Message} {method : MethodDef}
    {definingClass : ClassId}
    (dispatch : p.OrdinaryDispatch h receiver message
      (.invoke method invocationReceiver definingClass invocationMessage)) :
    p.IsLiveClass h definingClass := by
  cases dispatch with
  | hit receiverClassLive lookup =>
      exact publicLookupResultClass_live wf
        (wf.objectClassesAreLive receiver _ receiverClassLive) lookup

theorem superDispatch_invocationClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId} {message : Message}
    {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
    (dispatch : p.SuperDispatch h activationId message
      (.invoke method receiver definingClass message)) :
    p.IsLiveClass h definingClass := by
  cases dispatch with
  | hit _ _ _ _ superclass lookup =>
      exact protectedLookupResultClass_live wf
        (wf.superclassIsLive _ _ superclass) lookup

theorem outerDispatch_invocationClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {target immediate : ClassDeclId} {message : Message}
    {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
    (dispatch : p.OuterDispatch h activationId target immediate message
      (.invoke method receiver definingClass message)) :
    p.IsLiveClass h definingClass := by
  cases dispatch with
  | privateHit _ _ _ _ application _ =>
      exact targetApplicationClass_live wf application
  | protectedHit _ _ _ _ _ receiverClassLive lookup =>
      exact protectedLookupResultClass_live wf
        (wf.objectClassesAreLive receiver _ receiverClassLive) lookup

theorem implicitDispatch_invocationClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {immediate : Option ClassDeclId} {annotation : Option ScopeDecl}
    {message : Message} {method : MethodDef} {receiver : ObjRef}
    {definingClass : ClassId}
    (dispatch : p.ImplicitDispatch h activationId immediate annotation message
      (.invoke method receiver definingClass message)) :
    p.IsLiveClass h definingClass := by
  cases dispatch with
  | classScope _ _ outer => exact outerDispatch_invocationClass_live wf outer
  | objectLiteralScope _ _ _ receiverClassLive lookup _ =>
      exact unrestrictedLookupResultClass_live wf
        (wf.objectClassesAreLive receiver _ receiverClassLive) lookup
  | activationScope _ _ _ ordinary =>
      exact ordinaryDispatch_invocationClass_live wf ordinary
  | self _ _ selfDispatch =>
      exact outerDispatch_invocationClass_live wf selfDispatch

theorem resolveRequest_invocationClass_live {p : Program} {h : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {request : SendRequest} {message : Message} {method : MethodDef}
    {receiver : ObjRef} {definingClass : ClassId}
    (resolution : p.ResolveRequest h activationId request message
      (.invoke method receiver definingClass message)) :
    p.IsLiveClass h definingClass := by
  cases resolution with
  | ordinary _ dispatch => exact ordinaryDispatch_invocationClass_live wf dispatch
  | implicit dispatch => exact implicitDispatch_invocationClass_live wf dispatch
  | outer dispatch => exact outerDispatch_invocationClass_live wf dispatch
  | self dispatch => exact outerDispatch_invocationClass_live wf dispatch
  | super dispatch => exact superDispatch_invocationClass_live wf dispatch

theorem dnuFallback_invocationClass_live {p : Program}
    {state nextState : AllocationState} {receiver invocationReceiver : ObjRef}
    {lookupStart : ClassId} {original finalMessage : Message}
    {method : MethodDef} {definingClass : ClassId}
    (wf : p.WellFormed state.heap)
    (startLive : p.IsLiveClass state.heap lookupStart)
    (fallback : p.DnuFallback state receiver lookupStart original nextState
      (.invoke method invocationReceiver definingClass finalMessage)) :
    p.IsLiveClass state.heap definingClass := by
  cases fallback with
  | apply selection =>
      cases selection with
      | found lookup =>
          exact unrestrictedLookupResultClass_live wf startLive lookup

theorem completeRequest_invocationClass_live {p : Program}
    {state nextState : AllocationState} {activationId : ActivationId}
    {request : SendRequest} {message finalMessage : Message}
    {method : MethodDef} {receiver : ObjRef} {definingClass : ClassId}
    (wf : p.WellFormed state.heap)
    (completion : p.CompleteRequest state activationId request message nextState
      (.invoke method receiver definingClass finalMessage)) :
    p.IsLiveClass state.heap definingClass := by
  cases completion with
  | invoke resolution => exact resolveRequest_invocationClass_live wf resolution
  | dnu _ hasChain fallback =>
      rcases hasChain with ⟨chain, witness⟩
      exact dnuFallback_invocationClass_live wf
        (witness.start_live wf) fallback

theorem writeActivationLocal_preserves_wellFormed {p : Program} {h h' : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    {slot : LocalSlotId} {value : ObjRef}
    (write : h.writeActivationLocal activationId slot value = some h') :
    p.WellFormed h' := by
  cases activationLive : h.activations activationId with
  | none => simp [Heap.writeActivationLocal, activationLive] at write
  | some activation =>
      cases slotLive : activation.locals slot with
      | none =>
          simp [Heap.writeActivationLocal, activationLive, slotLive] at write
      | some cell =>
          simp [Heap.writeActivationLocal, activationLive, slotLive] at write
          subst h'
          apply wf.installActivation_wellFormed
          · exact wf.objectClassesAreLive (.activationObject activationId)
              activation.objectClass (by
                simp [Heap.classOf, activationLive])
          · exact wf.activationCurrentClassesAreLive activationId activation
              activationLive

theorem severActivationContinuation_preserves_wellFormed {p : Program}
    {h h' : Heap}
    (wf : p.WellFormed h) {activationId : ActivationId}
    (sever : h.severActivationContinuation activationId = some h') :
    p.WellFormed h' := by
  cases activationLive : h.activations activationId with
  | none => simp [Heap.severActivationContinuation, activationLive] at sever
  | some activation =>
      simp [Heap.severActivationContinuation, activationLive] at sever
      subst h'
      apply wf.installActivation_wellFormed
      · exact wf.objectClassesAreLive (.activationObject activationId)
          activation.objectClass (by simp [Heap.classOf, activationLive])
      · exact wf.activationCurrentClassesAreLive activationId activation
          activationLive

theorem Heap.classOf_markUncontinuable (h : Heap) (target : ActivationId)
    (object : ObjRef) :
    (h.markUncontinuable target).classOf object = h.classOf object := by
  classical
  cases object <;> try rfl
  case activationObject activationId =>
    by_cases dependent : DependentActivation h target activationId
    · cases activationLive : h.activations activationId <;>
        simp [Heap.classOf, Heap.markUncontinuable, dependent, activationLive,
          markActivationUncontinuable]
    · simp [Heap.classOf, Heap.markUncontinuable, dependent]

theorem markUncontinuable_preserves_wellFormed {p : Program} {h : Heap}
    (wf : p.WellFormed h) (target : ActivationId) :
    p.WellFormed (h.markUncontinuable target) := by
  classical
  have carryLive {classId : ClassId} (live : p.IsLiveClass h classId) :
      p.IsLiveClass (h.markUncontinuable target) classId := by
    simpa [Program.IsLiveClass, Heap.markUncontinuable] using live
  apply wf.of_classes_eq (h' := h.markUncontinuable target) rfl
  · intro object classId live
    exact carryLive (wf.objectClassesAreLive object classId (by
      simpa [Heap.classOf_markUncontinuable] using live))
  · intro activationId activation live
    by_cases dependent : DependentActivation h target activationId
    · simp [Heap.markUncontinuable, dependent] at live
      rcases live with ⟨oldActivation, oldLive, transformed⟩
      subst activation
      simpa [OptionalClassLive, Program.IsLiveClass,
        Heap.markUncontinuable, markActivationUncontinuable] using
        wf.activationCurrentClassesAreLive activationId oldActivation oldLive
    · have oldLive : h.activations activationId = some activation := by
        simpa [Heap.markUncontinuable, dependent] using live
      simpa [OptionalClassLive, Program.IsLiveClass,
        Heap.markUncontinuable] using
        wf.activationCurrentClassesAreLive activationId activation oldLive
  · intro closureId closure live
    simpa [OptionalClassLive, Program.IsLiveClass,
      Heap.markUncontinuable] using
      wf.closureCapturedClassesAreLive closureId closure (by
        simpa [Heap.markUncontinuable] using live)

def StackLive (h : Heap) : ActivationStack → Prop
  | .empty => True
  | .push rest frame =>
      StackLive h rest ∧ ∃ activation, h.activations frame.activation = some activation

def ControlWellFormed (p : Program) (h : Heap) : ControlTerm → Prop
  | .invoke _ _ definingClass _ => p.IsLiveClass h definingClass
  | _ => True

/-- The invariant carried by every configuration in the sequential machine.
    It separates global program/heap coherence, allocation-frontier freshness,
    liveness of every activation named by the stack, and the one control form
    (`invoke`) that carries a class subsequently installed in an activation. -/
structure SequentialWellFormed (p : Program)
    (config : SequentialConfig) : Prop where
  heap : p.WellFormed config.allocation.heap
  supplies : config.allocation.SuppliesFresh
  stack : StackLive config.allocation.heap config.stack
  control : ControlWellFormed p config.allocation.heap config.control

theorem stackLive_transport {h h' : Heap} {stack : ActivationStack}
    (live : StackLive h stack)
    (retains : ∀ id activation, h.activations id = some activation →
      ∃ activation', h'.activations id = some activation') :
    StackLive h' stack := by
  induction stack with
  | empty => trivial
  | push rest frame ih =>
      rcases live with ⟨restLive, activation, activationLive⟩
      exact ⟨ih restLive, retains frame.activation activation activationLive⟩

theorem stackLive_resumeActivation {h : Heap}
    {stack resumed : ActivationStack} {target : ActivationId}
    (live : StackLive h stack)
    (resume : resumeActivation stack target = some resumed) :
    StackLive h resumed := by
  induction stack with
  | empty => simp [resumeActivation] at resume
  | push rest frame ih =>
      rcases live with ⟨restLive, frameDef, frameLive⟩
      by_cases atTarget : frame.activation = target
      · simp [resumeActivation, atTarget] at resume
        subst resumed
        exact ⟨restLive, frameDef, frameLive⟩
      · simp [resumeActivation, atTarget] at resume
        exact ih restLive resume

theorem Heap.installMirror_retainsActivations (h : Heap) (id : MirrorId)
    (mirror : MirrorDef) :
    ∀ activationId activation,
      h.activations activationId = some activation →
      ∃ activation',
        (h.installMirror id mirror).activations activationId = some activation' := by
  intro activationId activation live
  exact ⟨activation, by simpa [Heap.installMirror] using live⟩

theorem Heap.installClosure_retainsActivations (h : Heap) (id : ClosureId)
    (closure : ClosureDef) :
    ∀ activationId activation,
      h.activations activationId = some activation →
      ∃ activation',
        (h.installClosure id closure).activations activationId = some activation' := by
  intro activationId activation live
  exact ⟨activation, by simpa [Heap.installClosure] using live⟩

theorem Heap.installActivation_fresh_retains (h : Heap) (id : ActivationId)
    (activation : ActivationDef) (fresh : h.activations id = none) :
    ∀ oldId oldActivation,
      h.activations oldId = some oldActivation →
      ∃ newActivation,
        (h.installActivation id activation).activations oldId =
          some newActivation := by
  intro oldId oldActivation live
  have away : oldId ≠ id := by
    intro equal
    subst oldId
    rw [fresh] at live
    contradiction
  exact ⟨oldActivation, by
    simpa [Heap.installActivation, away] using live⟩

theorem allocateMessageMirror_wellFormed {p : Program}
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (message : Message) :
    p.WellFormed (p.allocateMessageMirror state message).1.heap ∧
      (p.allocateMessageMirror state message).1.SuppliesFresh := by
  constructor
  · apply wf.installMirror_wellFormed
    simpa [Program.messageMirrorDefinition] using wf.messageMirrorClassIsLive
  · exact p.allocateMessageMirror_preserves_supplies fresh message

theorem allocateMethodActivation_wellFormed {p : Program}
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (method : MethodDef) (receiver : ObjRef)
    (definingClass : ClassId) (message : Message)
    (continuation : Option ActivationId)
    (definingClassLive : p.IsLiveClass state.heap definingClass) :
    p.WellFormed (p.allocateMethodActivation state method receiver
        definingClass message continuation).1.heap ∧
      (p.allocateMethodActivation state method receiver definingClass message
        continuation).1.SuppliesFresh := by
  constructor
  · apply wf.installActivation_wellFormed
    · simpa [Program.methodActivationDefinition] using wf.activationClassIsLive
    · simpa [Program.methodActivationDefinition, OptionalClassLive] using
        definingClassLive
  · exact p.allocateMethodActivation_preserves_supplies fresh method receiver
      definingClass message continuation

theorem allocateClosureObject_wellFormed {p : Program}
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (definingActivation : ActivationId)
    (defining : ActivationDef) (declaration : ActivationDeclId)
    (body : List Statement)
    (definingLive : state.heap.activations definingActivation = some defining) :
    let closure := p.closureDefinition definingActivation defining declaration body
    p.WellFormed (p.allocateClosureObject state closure).1.heap ∧
      (p.allocateClosureObject state closure).1.SuppliesFresh := by
  let closure := p.closureDefinition definingActivation defining declaration body
  have capturedLive : p.OptionalClassLive state.heap closure.capturedClass := by
    simpa [closure, Program.closureDefinition] using
      wf.activationCurrentClassesAreLive definingActivation defining definingLive
  constructor
  · apply wf.installClosure_wellFormed
    · simpa [closure, Program.closureDefinition] using wf.closureClassIsLive
    · exact capturedLive
  · exact p.allocateClosureObject_preserves_supplies fresh closure

theorem allocateCascadeClosureObject_wellFormed {p : Program}
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (definingActivation : ActivationId)
    (defining : ActivationDef) (descriptor : CascadeDescriptor)
    (clauses : List (Selector × List CoreExpr))
    (definingLive : state.heap.activations definingActivation = some defining) :
    let closure := p.cascadeClosureDefinition definingActivation defining
      descriptor clauses
    p.WellFormed (p.allocateClosureObject state closure).1.heap ∧
      (p.allocateClosureObject state closure).1.SuppliesFresh := by
  let closure := p.cascadeClosureDefinition definingActivation defining
    descriptor clauses
  have capturedLive : p.OptionalClassLive state.heap closure.capturedClass := by
    simpa [closure, Program.cascadeClosureDefinition] using
      wf.activationCurrentClassesAreLive definingActivation defining definingLive
  constructor
  · apply wf.installClosure_wellFormed
    · simpa [closure, Program.cascadeClosureDefinition] using
        wf.closureClassIsLive
    · exact capturedLive
  · exact p.allocateClosureObject_preserves_supplies fresh closure

theorem allocateClosureActivation_wellFormed {p : Program}
    {state : AllocationState} (wf : p.WellFormed state.heap)
    (fresh : state.SuppliesFresh) (closureId : ClosureId)
    (closure : ClosureDef) (defining : ActivationDef) (message : Message)
    (continuation : Option ActivationId)
    (closureLive : state.heap.closures closureId = some closure) :
    p.WellFormed (p.allocateClosureActivation state closure defining message
        continuation).1.heap ∧
      (p.allocateClosureActivation state closure defining message
        continuation).1.SuppliesFresh := by
  have capturedLive := wf.closureCapturedClassesAreLive closureId closure
    closureLive
  constructor
  · apply wf.installActivation_wellFormed
    · simpa [Program.closureActivationDefinition] using wf.activationClassIsLive
    · simpa [Program.closureActivationDefinition] using capturedLive
  · exact p.allocateClosureActivation_preserves_supplies fresh closure defining
      message continuation

theorem Heap.writeActivationLocal_retainsActivations {h h' : Heap}
    {activationId : ActivationId} {slot : LocalSlotId} {value : ObjRef}
    (write : h.writeActivationLocal activationId slot value = some h') :
    ∀ oldId oldActivation, h.activations oldId = some oldActivation →
      ∃ newActivation, h'.activations oldId = some newActivation := by
  intro oldId oldActivation oldLive
  cases activationLive : h.activations activationId with
  | none => simp [Heap.writeActivationLocal, activationLive] at write
  | some activation =>
      cases slotLive : activation.locals slot with
      | none => simp [Heap.writeActivationLocal, activationLive, slotLive] at write
      | some cell =>
          simp [Heap.writeActivationLocal, activationLive, slotLive] at write
          subst h'
          by_cases atTarget : oldId = activationId
          · subst oldId
            exact ⟨_, Heap.installActivation_at _ _ _⟩
          · exact ⟨oldActivation, by
              simpa [Heap.installActivation, atTarget] using oldLive⟩

theorem Heap.writeActivationLocal_preserves_absence {h h' : Heap}
    {activationId candidate : ActivationId} {slot : LocalSlotId}
    {value : ObjRef}
    (write : h.writeActivationLocal activationId slot value = some h')
    (absent : h.activations candidate = none) :
    h'.activations candidate = none := by
  cases activationLive : h.activations activationId with
  | none => simp [Heap.writeActivationLocal, activationLive] at write
  | some activation =>
      cases slotLive : activation.locals slot with
      | none => simp [Heap.writeActivationLocal, activationLive, slotLive] at write
      | some cell =>
          simp [Heap.writeActivationLocal, activationLive, slotLive] at write
          subst h'
          have away : candidate ≠ activationId := by
            intro equal
            subst candidate
            rw [activationLive] at absent
            contradiction
          simpa [Heap.installActivation, away] using absent

theorem Heap.writeActivationLocal_preserves_otherStores {h h' : Heap}
    {activationId : ActivationId} {slot : LocalSlotId} {value : ObjRef}
    (write : h.writeActivationLocal activationId slot value = some h') :
    h'.mirrors = h.mirrors ∧ h'.closures = h.closures ∧
      h'.objects = h.objects ∧ h'.classes = h.classes := by
  cases activationLive : h.activations activationId with
  | none => simp [Heap.writeActivationLocal, activationLive] at write
  | some activation =>
      cases slotLive : activation.locals slot with
      | none => simp [Heap.writeActivationLocal, activationLive, slotLive] at write
      | some cell =>
          simp [Heap.writeActivationLocal, activationLive, slotLive] at write
          subst h'
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem Heap.severActivationContinuation_retainsActivations {h h' : Heap}
    {activationId : ActivationId}
    (sever : h.severActivationContinuation activationId = some h') :
    ∀ oldId oldActivation, h.activations oldId = some oldActivation →
      ∃ newActivation, h'.activations oldId = some newActivation := by
  intro oldId oldActivation oldLive
  cases activationLive : h.activations activationId with
  | none => simp [Heap.severActivationContinuation, activationLive] at sever
  | some activation =>
      simp [Heap.severActivationContinuation, activationLive] at sever
      subst h'
      by_cases atTarget : oldId = activationId
      · subst oldId
        exact ⟨_, Heap.installActivation_at _ _ _⟩
      · exact ⟨oldActivation, by
          simpa [Heap.installActivation, atTarget] using oldLive⟩

theorem Heap.severActivationContinuation_preserves_absence {h h' : Heap}
    {activationId candidate : ActivationId}
    (sever : h.severActivationContinuation activationId = some h')
    (absent : h.activations candidate = none) :
    h'.activations candidate = none := by
  cases activationLive : h.activations activationId with
  | none => simp [Heap.severActivationContinuation, activationLive] at sever
  | some activation =>
      simp [Heap.severActivationContinuation, activationLive] at sever
      subst h'
      have away : candidate ≠ activationId := by
        intro equal
        subst candidate
        rw [activationLive] at absent
        contradiction
      simpa [Heap.installActivation, away] using absent

theorem Heap.severActivationContinuation_preserves_otherStores {h h' : Heap}
    {activationId : ActivationId}
    (sever : h.severActivationContinuation activationId = some h') :
    h'.mirrors = h.mirrors ∧ h'.closures = h.closures ∧
      h'.objects = h.objects ∧ h'.classes = h.classes := by
  cases activationLive : h.activations activationId with
  | none => simp [Heap.severActivationContinuation, activationLive] at sever
  | some activation =>
      simp [Heap.severActivationContinuation, activationLive] at sever
      subst h'
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem Heap.markUncontinuable_retainsActivations (h : Heap)
    (target : ActivationId) :
    ∀ oldId oldActivation, h.activations oldId = some oldActivation →
      ∃ newActivation,
        (h.markUncontinuable target).activations oldId = some newActivation := by
  classical
  intro oldId oldActivation oldLive
  by_cases dependent : DependentActivation h target oldId
  · exact ⟨markActivationUncontinuable oldActivation, by
      simp [Heap.markUncontinuable, dependent, oldLive]⟩
  · exact ⟨oldActivation, by
      simp [Heap.markUncontinuable, dependent, oldLive]⟩

theorem Heap.markUncontinuable_preserves_absence (h : Heap)
    (target candidate : ActivationId)
    (absent : h.activations candidate = none) :
    (h.markUncontinuable target).activations candidate = none := by
  classical
  by_cases dependent : DependentActivation h target candidate <;>
    simp [Heap.markUncontinuable, dependent, absent]

theorem Heap.writeObjectSlot_preserves_classOf {h h' : Heap}
    {object : ObjectId} {slot : SlotId} {value : ObjRef}
    (write : h.writeObjectSlot object slot value = some h') :
    ∀ reference, h'.classOf reference = h.classOf reference := by
  intro reference
  cases objectLive : h.objects object with
  | none => simp [Heap.writeObjectSlot, objectLive] at write
  | some objectDef =>
      cases slotLive : objectDef.slots slot with
      | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
      | some oldValue =>
          simp [Heap.writeObjectSlot, objectLive, slotLive] at write
          subst h'
          cases reference with
          | ordinaryObject candidate =>
              by_cases atTarget : candidate = object
              · subst candidate
                simp [Heap.classOf, Heap.installObject, objectLive]
              · simp [Heap.classOf, Heap.installObject, atTarget]
          | classObject candidate => rfl
          | mixinObject candidate => rfl
          | activationObject candidate => rfl
          | closureObject candidate => rfl
          | mirrorObject candidate => rfl
          | actorObject candidate => rfl

theorem Heap.writeObjectSlot_preserves_absence {h h' : Heap}
    {object candidate : ObjectId} {slot : SlotId} {value : ObjRef}
    (write : h.writeObjectSlot object slot value = some h')
    (absent : h.objects candidate = none) : h'.objects candidate = none := by
  cases objectLive : h.objects object with
  | none => simp [Heap.writeObjectSlot, objectLive] at write
  | some objectDef =>
      cases slotLive : objectDef.slots slot with
      | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
      | some oldValue =>
          simp [Heap.writeObjectSlot, objectLive, slotLive] at write
          subst h'
          have away : candidate ≠ object := by
            intro equal
            subst candidate
            rw [objectLive] at absent
            contradiction
          simpa [Heap.installObject, away] using absent

theorem Heap.writeObjectSlot_retainsActivations {h h' : Heap}
    {object : ObjectId} {slot : SlotId} {value : ObjRef}
    (write : h.writeObjectSlot object slot value = some h') :
    ∀ id activation, h.activations id = some activation →
      ∃ activation', h'.activations id = some activation' := by
  intro id activation live
  cases objectLive : h.objects object with
  | none => simp [Heap.writeObjectSlot, objectLive] at write
  | some objectDef =>
      cases slotLive : objectDef.slots slot with
      | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
      | some oldValue =>
          simp [Heap.writeObjectSlot, objectLive, slotLive] at write
          subst h'
          exact ⟨activation, live⟩

theorem WellFormed.writeObjectSlot_wellFormed {p : Program} {h h' : Heap}
    (wf : p.WellFormed h) {object : ObjectId} {slot : SlotId}
    {value : ObjRef}
    (write : h.writeObjectSlot object slot value = some h') :
    p.WellFormed h' := by
  have classOfEq := Heap.writeObjectSlot_preserves_classOf write
  have classesEq : h'.classes = h.classes := by
    cases objectLive : h.objects object with
    | none => simp [Heap.writeObjectSlot, objectLive] at write
    | some objectDef =>
        cases slotLive : objectDef.slots slot with
        | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
        | some oldValue =>
            simp [Heap.writeObjectSlot, objectLive, slotLive] at write
            subst h'
            rfl
  apply wf.of_classes_eq classesEq
  · intro reference classId live
    have oldLive := wf.objectClassesAreLive reference classId
      ((classOfEq reference).symm.trans live)
    simpa [OptionalClassLive, Program.IsLiveClass, classesEq] using oldLive
  · intro activationId activation live
    have oldActivation : h.activations activationId = some activation := by
      cases objectLive : h.objects object with
      | none => simp [Heap.writeObjectSlot, objectLive] at write
      | some objectDef =>
          cases slotLive : objectDef.slots slot with
          | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
          | some oldValue =>
              simp [Heap.writeObjectSlot, objectLive, slotLive] at write
              subst h'
              exact live
    have oldLive := wf.activationCurrentClassesAreLive activationId activation
      oldActivation
    simpa [OptionalClassLive, Program.IsLiveClass, classesEq] using oldLive
  · intro closureId closure live
    have oldClosure : h.closures closureId = some closure := by
      cases objectLive : h.objects object with
      | none => simp [Heap.writeObjectSlot, objectLive] at write
      | some objectDef =>
          cases slotLive : objectDef.slots slot with
          | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
          | some oldValue =>
              simp [Heap.writeObjectSlot, objectLive, slotLive] at write
              subst h'
              exact live
    have oldLive := wf.closureCapturedClassesAreLive closureId closure oldClosure
    simpa [OptionalClassLive, Program.IsLiveClass, classesEq] using oldLive

theorem AllocationState.writeObjectSlot_preserves_supplies
    {state : AllocationState} {heap : Heap} {object : ObjectId}
    {slot : SlotId} {value : ObjRef} (fresh : state.SuppliesFresh)
    (write : state.heap.writeObjectSlot object slot value = some heap) :
    ({state with heap := heap} : AllocationState).SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id frontier
    change heap.mirrors id = none
    cases objectLive : state.heap.objects object with
    | none => simp [Heap.writeObjectSlot, objectLive] at write
    | some objectDef =>
        cases slotLive : objectDef.slots slot with
        | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
        | some oldValue =>
            simp [Heap.writeObjectSlot, objectLive, slotLive] at write
            subst heap
            exact fresh.1 id frontier
  · intro id frontier
    change heap.activations id = none
    cases objectLive : state.heap.objects object with
    | none => simp [Heap.writeObjectSlot, objectLive] at write
    | some objectDef =>
        cases slotLive : objectDef.slots slot with
        | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
        | some oldValue =>
            simp [Heap.writeObjectSlot, objectLive, slotLive] at write
            subst heap
            exact fresh.2.1 id frontier
  · intro id frontier
    change heap.closures id = none
    cases objectLive : state.heap.objects object with
    | none => simp [Heap.writeObjectSlot, objectLive] at write
    | some objectDef =>
        cases slotLive : objectDef.slots slot with
        | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
        | some oldValue =>
            simp [Heap.writeObjectSlot, objectLive, slotLive] at write
            subst heap
            exact fresh.2.2.1 id frontier
  · intro id frontier
    exact Heap.writeObjectSlot_preserves_absence write
      (fresh.2.2.2.1 id frontier)
  · intro id frontier
    change heap.classes id = none
    cases objectLive : state.heap.objects object with
    | none => simp [Heap.writeObjectSlot, objectLive] at write
    | some objectDef =>
        cases slotLive : objectDef.slots slot with
        | none => simp [Heap.writeObjectSlot, objectLive, slotLive] at write
        | some oldValue =>
            simp [Heap.writeObjectSlot, objectLive, slotLive] at write
            subst heap
            exact fresh.2.2.2.2 id frontier

theorem AllocationState.writeActivationLocal_preserves_supplies
    {state : AllocationState} {heap : Heap} {activation : ActivationId}
    {slot : LocalSlotId} {value : ObjRef} (fresh : state.SuppliesFresh)
    (write : state.heap.writeActivationLocal activation slot value = some heap) :
    ({state with heap := heap} : AllocationState).SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id frontier
    rw [(Heap.writeActivationLocal_preserves_otherStores write).1]
    exact fresh.1 id frontier
  · intro id frontier
    exact Heap.writeActivationLocal_preserves_absence write
      (fresh.2.1 id frontier)
  · intro id frontier
    rw [(Heap.writeActivationLocal_preserves_otherStores write).2.1]
    exact fresh.2.2.1 id frontier
  · intro id frontier
    rw [(Heap.writeActivationLocal_preserves_otherStores write).2.2.1]
    exact fresh.2.2.2.1 id frontier
  · intro id frontier
    rw [(Heap.writeActivationLocal_preserves_otherStores write).2.2.2]
    exact fresh.2.2.2.2 id frontier

theorem AllocationState.severActivationContinuation_preserves_supplies
    {state : AllocationState} {heap : Heap} {activation : ActivationId}
    (fresh : state.SuppliesFresh)
    (sever : state.heap.severActivationContinuation activation = some heap) :
    ({state with heap := heap} : AllocationState).SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id frontier
    rw [(Heap.severActivationContinuation_preserves_otherStores sever).1]
    exact fresh.1 id frontier
  · intro id frontier
    exact Heap.severActivationContinuation_preserves_absence sever
      (fresh.2.1 id frontier)
  · intro id frontier
    rw [(Heap.severActivationContinuation_preserves_otherStores sever).2.1]
    exact fresh.2.2.1 id frontier
  · intro id frontier
    rw [(Heap.severActivationContinuation_preserves_otherStores sever).2.2.1]
    exact fresh.2.2.2.1 id frontier
  · intro id frontier
    rw [(Heap.severActivationContinuation_preserves_otherStores sever).2.2.2]
    exact fresh.2.2.2.2 id frontier

theorem AllocationState.markUncontinuable_preserves_supplies
    {state : AllocationState} (fresh : state.SuppliesFresh)
    (target : ActivationId) :
    ({state with heap := state.heap.markUncontinuable target} :
      AllocationState).SuppliesFresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id frontier
    change state.heap.mirrors id = none
    exact fresh.1 id frontier
  · intro id frontier
    exact Heap.markUncontinuable_preserves_absence state.heap target id
      (fresh.2.1 id frontier)
  · intro id frontier
    change state.heap.closures id = none
    exact fresh.2.2.1 id frontier
  · intro id frontier
    exact fresh.2.2.2.1 id frontier
  · intro id frontier
    exact fresh.2.2.2.2 id frontier

theorem expressionOrderStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.ExpressionOrderStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | value => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | selfValue _ => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | ordinaryReceiver => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | eventualReceiver => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | @nonOrdinary _ _ _ _ expression pending _ =>
      rcases pending with ⟨request, selector, arguments⟩
      cases arguments <;> exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | @receiverValue state rest current frames receiver selector arguments =>
      cases arguments <;>
        refine ⟨wf.heap, wf.supplies, ?_, trivial⟩ <;>
        simpa [continueReceiver, StackLive] using wf.stack
  | @eventualReceiverValue state rest current frames receiver selector arguments =>
      cases arguments <;>
        refine ⟨wf.heap, wf.supplies, ?_, trivial⟩ <;>
        simpa [continueEventualReceiver, StackLive] using wf.stack
  | @argumentValue state rest current frames request selector values remaining value =>
      cases remaining <;>
        refine ⟨wf.heap, wf.supplies, ?_, trivial⟩ <;>
        simpa [continueArguments, StackLive] using wf.stack

theorem requestCompletionStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.RequestCompletionStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | @invoke state nextState rest current frames request message finalMessage
      method receiver definingClass completion =>
      cases completion with
      | invoke resolution =>
          exact ⟨wf.heap, wf.supplies, wf.stack,
            resolveRequest_invocationClass_live wf.heap resolution⟩
      | dnu resolution hasChain fallback =>
          cases fallback with
          | apply selection =>
              let allocation := p.allocateMessageMirror state message
              have allocationWf := p.allocateMessageMirror_wellFormed wf.heap
                wf.supplies message
              refine ⟨allocationWf.1, allocationWf.2, ?_, ?_⟩
              · exact stackLive_transport wf.stack
                  (Heap.installMirror_retainsActivations _ _ _)
              · have oldLive := completeRequest_invocationClass_live wf.heap
                    (.dnu resolution hasChain (.apply selection))
                simpa [ControlWellFormed, Program.finishDnu, allocation,
                  Program.allocateMessageMirror, Program.IsLiveClass,
                  Heap.installMirror] using oldLive
  | invalidSuper completion =>
      exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩

theorem methodInvocationStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.MethodInvocationStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | @nonTail state rest current frames topFrame method receiver definingClass
      message locals body _ _ _ _ =>
      let allocation := p.allocateMethodActivation state method receiver
        definingClass message (some current)
      have allocationWf := p.allocateMethodActivation_wellFormed wf.heap
        wf.supplies method receiver definingClass message (some current) wf.control
      have freshId := p.allocateMethodActivation_was_fresh wf.supplies.2.1
        method receiver definingClass message (some current)
      have oldStack : StackLive state.heap
          (.push rest ⟨current, .push frames topFrame⟩) := wf.stack
      have retained : StackLive allocation.1.heap
          (.push rest ⟨current, .push frames topFrame⟩) :=
        stackLive_transport oldStack
          (Heap.installActivation_fresh_retains state.heap
            ⟨state.nextActivation⟩
            (p.methodActivationDefinition ⟨state.nextActivation⟩ method
              receiver definingClass message (some current)) freshId)
      refine ⟨allocationWf.1, allocationWf.2, ⟨retained, ?_⟩, trivial⟩
      exact ⟨p.methodActivationDefinition allocation.2 method receiver
        definingClass message (some current), by
          simpa [Program.nonTailInvocationTarget, allocation] using
            p.allocateMethodActivation_installs state
            method receiver definingClass message (some current)⟩
  | @tail state rest current currentDef method receiver definingClass message
      locals body currentActivation _ _ _ _ =>
      let allocation := p.allocateMethodActivation state method receiver
        definingClass message currentDef.continuation
      have allocationWf := p.allocateMethodActivation_wellFormed wf.heap
        wf.supplies method receiver definingClass message currentDef.continuation
        wf.control
      have freshId := p.allocateMethodActivation_was_fresh wf.supplies.2.1
        method receiver definingClass message currentDef.continuation
      rcases wf.stack with ⟨restLive, _, _⟩
      have retainedRest : StackLive allocation.1.heap rest :=
        stackLive_transport restLive
          (Heap.installActivation_fresh_retains state.heap
            ⟨state.nextActivation⟩
            (p.methodActivationDefinition ⟨state.nextActivation⟩ method
              receiver definingClass message currentDef.continuation) freshId)
      refine ⟨allocationWf.1, allocationWf.2, ⟨retainedRest, ?_⟩, trivial⟩
      exact ⟨p.methodActivationDefinition allocation.2 method receiver
        definingClass message currentDef.continuation, by
          simpa [Program.tailInvocationTarget, allocation] using
            p.allocateMethodActivation_installs state
            method receiver definingClass message currentDef.continuation⟩

theorem closureMachineStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.ClosureMachineStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | creation creation =>
      cases creation with
      | @create state rest current frames defining declaration body definingLive _ =>
          let closure := p.closureDefinition current defining declaration body
          let allocation := p.allocateClosureObject state closure
          have allocationWf := p.allocateClosureObject_wellFormed wf.heap
            wf.supplies current defining declaration body definingLive
          refine ⟨allocationWf.1, allocationWf.2, ?_, trivial⟩
          exact stackLive_transport wf.stack
            (Heap.installClosure_retainsActivations state.heap allocation.2 closure)
      | @createCascade state rest current frames defining descriptor clauses
          definingLive =>
          let closure := p.cascadeClosureDefinition current defining descriptor clauses
          let allocation := p.allocateClosureObject state closure
          have allocationWf := p.allocateCascadeClosureObject_wellFormed wf.heap
            wf.supplies current defining descriptor clauses definingLive
          refine ⟨allocationWf.1, allocationWf.2, ?_, trivial⟩
          exact stackLive_transport wf.stack
            (Heap.installClosure_retainsActivations state.heap allocation.2 closure)
  | dispatch dispatch =>
      cases dispatch
      exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | invocation invocation =>
      cases invocation with
      | @nonTail state rest current frames topFrame id closure defining message
          closureLive definingLive _ _ =>
          let allocation := p.allocateClosureActivation state closure defining
            message (some current)
          have allocationWf := p.allocateClosureActivation_wellFormed wf.heap
            wf.supplies id closure defining message (some current) closureLive
          have freshId := p.allocateClosureActivation_was_fresh wf.supplies.2.1
            closure defining message (some current)
          have retained : StackLive allocation.1.heap
              (.push rest ⟨current, .push frames topFrame⟩) :=
            stackLive_transport wf.stack
              (Heap.installActivation_fresh_retains state.heap
                ⟨state.nextActivation⟩
                (p.closureActivationDefinition ⟨state.nextActivation⟩ closure
                  defining message (some current)) freshId)
          refine ⟨allocationWf.1, allocationWf.2, ⟨retained, ?_⟩, trivial⟩
          exact ⟨p.closureActivationDefinition allocation.2 closure defining
            message (some current), by
              simpa [Program.nonTailClosureInvocationTarget, allocation] using
                p.allocateClosureActivation_installs state
                closure defining message (some current)⟩
      | @tail state rest current caller defining closure id message callerLive
          closureLive definingLive _ _ =>
          let allocation := p.allocateClosureActivation state closure defining
            message caller.continuation
          have allocationWf := p.allocateClosureActivation_wellFormed wf.heap
            wf.supplies id closure defining message caller.continuation closureLive
          have freshId := p.allocateClosureActivation_was_fresh wf.supplies.2.1
            closure defining message caller.continuation
          rcases wf.stack with ⟨restLive, _, _⟩
          have retainedRest : StackLive allocation.1.heap rest :=
            stackLive_transport restLive
              (Heap.installActivation_fresh_retains state.heap
                ⟨state.nextActivation⟩
                (p.closureActivationDefinition ⟨state.nextActivation⟩ closure
                  defining message caller.continuation) freshId)
          refine ⟨allocationWf.1, allocationWf.2,
            ⟨retainedRest, ?_⟩, trivial⟩
          exact ⟨p.closureActivationDefinition allocation.2 closure defining
            message caller.continuation, by
              simpa [Program.tailClosureInvocationTarget, allocation] using
                p.allocateClosureActivation_installs state
                closure defining message caller.continuation⟩

theorem bodyMachineStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.BodyMachineStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | graph next =>
      rcases before with ⟨state, stack, control⟩
      cases stack with
      | empty => simp [Program.bodyMachineNext] at next
      | push rest frame =>
          rcases frame with ⟨current, frames⟩
          cases control with
          | evaluate expression =>
              cases expression with
              | readLocal activation slot =>
                  cases read : state.heap.readActivationLocal activation slot with
                  | none => simp [Program.bodyMachineNext, read] at next
                  | some value =>
                      simp [Program.bodyMachineNext, read] at next
                      subst after
                      exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
              | writeLocal activation slot expression =>
                  simp [Program.bodyMachineNext] at next
                  subst after
                  exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
              | classBody declaration superclass =>
                  simp [Program.bodyMachineNext] at next
              | mixinApply declaration superclass mixinSource =>
                  simp [Program.bodyMachineNext] at next
              | objectLiteral declaration superclass =>
                  simp [Program.bodyMachineNext] at next
              | atom payload => simp [Program.bodyMachineNext] at next
              | tuple site descriptor elements =>
                  simp [Program.bodyMachineNext] at next
              | pattern value annotation immediate =>
                  simp [Program.bodyMachineNext] at next
              | cascade descriptor receiver clauses =>
                  simp [Program.bodyMachineNext] at next
              | readSlot object slot => simp [Program.bodyMachineNext] at next
              | writeSlot object slot expression =>
                  simp [Program.bodyMachineNext] at next
              | currentRead slot => simp [Program.bodyMachineNext] at next
              | currentWrite slot expression =>
                  simp [Program.bodyMachineNext] at next
              | lazyRead slot initializer =>
                  simp [Program.bodyMachineNext] at next
              | nestedClass declaration classExpression =>
                  simp [Program.bodyMachineNext] at next
              | newInstanceCurrent selector parameters =>
                  simp [Program.bodyMachineNext] at next
              | value object => simp [Program.bodyMachineNext] at next
              | selfValue => simp [Program.bodyMachineNext] at next
              | ordinarySend receiver selector arguments =>
                  simp [Program.bodyMachineNext] at next
              | eventualSend receiver selector arguments =>
                  simp [Program.bodyMachineNext] at next
              | implicitSend selector arguments annotation immediate =>
                  simp [Program.bodyMachineNext] at next
              | selfSend selector arguments immediate =>
                  simp [Program.bodyMachineNext] at next
              | outerSend selector arguments target immediate =>
                  simp [Program.bodyMachineNext] at next
              | superSend selector arguments => simp [Program.bodyMachineNext] at next
              | closureLiteral declaration => simp [Program.bodyMachineNext] at next
              | cascadeClosure descriptor clauses =>
                  simp [Program.bodyMachineNext] at next
          | evaluateMessage template => simp [Program.bodyMachineNext] at next
          | messageValue message => simp [Program.bodyMachineNext] at next
          | initClass classId object message =>
              simp [Program.bodyMachineNext] at next
          | ownInitialization classId object message =>
              simp [Program.bodyMachineNext] at next
          | initializeSlotGroups object groups body =>
              simp [Program.bodyMachineNext] at next
          | initializeSequentialSlots object declarations remaining body =>
              simp [Program.bodyMachineNext] at next
          | object value =>
              cases frames with
              | empty => simp [Program.bodyMachineNext] at next
              | push below top =>
                  cases top with
                  | receiver selector arguments => simp [Program.bodyMachineNext] at next
                  | asyncReceiver selector arguments =>
                      simp [Program.bodyMachineNext] at next
                  | arguments request selector values remaining =>
                      simp [Program.bodyMachineNext] at next
                  | initializeLocal slot remaining body target =>
                      cases write : state.heap.writeActivationLocal current slot value with
                      | none => simp [Program.bodyMachineNext, write] at next
                      | some heap =>
                          simp [Program.bodyMachineNext, write] at next
                          subst after
                          refine ⟨writeActivationLocal_preserves_wellFormed
                              wf.heap write,
                            AllocationState.writeActivationLocal_preserves_supplies
                              wf.supplies write,
                            ?_, trivial⟩
                          have retained := stackLive_transport wf.stack
                            (Heap.writeActivationLocal_retainsActivations write)
                          simpa [StackLive] using retained
                  | localWrite activation slot =>
                      cases write : state.heap.writeActivationLocal activation slot value with
                      | none => simp [Program.bodyMachineNext, write] at next
                      | some heap =>
                          simp [Program.bodyMachineNext, write] at next
                          subst after
                          refine ⟨writeActivationLocal_preserves_wellFormed
                              wf.heap write,
                            AllocationState.writeActivationLocal_preserves_supplies
                              wf.supplies write,
                            ?_, trivial⟩
                          have retained := stackLive_transport wf.stack
                            (Heap.writeActivationLocal_retainsActivations write)
                          simpa [StackLive] using retained
                  | slotWrite object slot => simp [Program.bodyMachineNext] at next
                  | lazySlotStore object slot =>
                      simp [Program.bodyMachineNext] at next
                  | makeClassBody descriptor enclosingObject =>
                      simp [Program.bodyMachineNext] at next
                  | makeObjectLiteral descriptor enclosingObject =>
                      simp [Program.bodyMachineNext] at next
                  | nestedClassStore object declaration =>
                      simp [Program.bodyMachineNext] at next
                  | mixinSuperclass descriptor mixinSource =>
                      simp [Program.bodyMachineNext] at next
                  | mixinSource descriptor superclass =>
                      simp [Program.bodyMachineNext] at next
                  | messageArguments selector values remaining =>
                      simp [Program.bodyMachineNext] at next
                  | superclassMessage classId object original =>
                      simp [Program.bodyMachineNext] at next
                  | afterSuperclass classId object original =>
                      simp [Program.bodyMachineNext] at next
                  | mixinMessage classId object =>
                      simp [Program.bodyMachineNext] at next
                  | afterMixin classId object =>
                      simp [Program.bodyMachineNext] at next
                  | storeInitializedSlot object slot declarations groups body =>
                      simp [Program.bodyMachineNext] at next
                  | simultaneousSlots code object groups body =>
                      simp [Program.bodyMachineNext] at next
                  | simultaneousLocals code activation remaining body target =>
                      cases code with
                      | nil =>
                          simp [Program.bodyMachineNext] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                      | cons first later =>
                          simp [Program.bodyMachineNext] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                  | sequence target remaining =>
                      cases remaining with
                      | nil =>
                          simp [Program.bodyMachineNext] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                      | cons statement later =>
                          simp [Program.bodyMachineNext] at next
                          subst after
                          exact ⟨wf.heap, wf.supplies, by
                            simpa [StackLive] using wf.stack, trivial⟩
                  | returnFrame => simp [Program.bodyMachineNext] at next
          | «initialize» activation groups body target =>
              by_cases currentActivation : activation = current
              · subst activation
                cases groups with
                | nil =>
                    simp [Program.bodyMachineNext] at next
                    subst after
                    exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
                | cons group remaining =>
                    cases group with
                    | simultaneous declarations =>
                        cases code : p.localSimCode current declarations with
                        | nil =>
                            simp [Program.bodyMachineNext, startSimultaneousLocals,
                              code] at next
                            subst after
                            exact ⟨wf.heap, wf.supplies, by
                              simpa [StackLive] using wf.stack, trivial⟩
                        | cons first later =>
                            simp [Program.bodyMachineNext, startSimultaneousLocals,
                              code] at next
                            subst after
                            exact ⟨wf.heap, wf.supplies, by
                              simpa [StackLive] using wf.stack, trivial⟩
                    | sequential declaration =>
                        cases declaration with
                        | immutable slot initializer =>
                            simp [Program.bodyMachineNext, eagerLocalInitializer] at next
                            subst after
                            exact ⟨wf.heap, wf.supplies, by
                              simpa [StackLive] using wf.stack, trivial⟩
                        | mutableInitialized slot initializer =>
                            simp [Program.bodyMachineNext, eagerLocalInitializer] at next
                            subst after
                            exact ⟨wf.heap, wf.supplies, by
                              simpa [StackLive] using wf.stack, trivial⟩
                        | mutableUninitialized slot =>
                            cases write : state.heap.writeActivationLocal current slot
                                p.nilObject with
                            | none => simp [Program.bodyMachineNext,
                                eagerLocalInitializer, nilInitializedLocal, write] at next
                            | some heap =>
                                simp [Program.bodyMachineNext, eagerLocalInitializer,
                                  nilInitializedLocal, write] at next
                                subst after
                                refine ⟨writeActivationLocal_preserves_wellFormed
                                    wf.heap write,
                                  AllocationState.writeActivationLocal_preserves_supplies
                                    wf.supplies write,
                                  ?_, trivial⟩
                                exact stackLive_transport wf.stack
                                  (Heap.writeActivationLocal_retainsActivations write)
                        | lazyImmutable slot initializer =>
                            cases write : state.heap.writeActivationLocal current slot
                                p.nilObject with
                            | none => simp [Program.bodyMachineNext,
                                eagerLocalInitializer, nilInitializedLocal, write] at next
                            | some heap =>
                                simp [Program.bodyMachineNext, eagerLocalInitializer,
                                  nilInitializedLocal, write] at next
                                subst after
                                refine ⟨writeActivationLocal_preserves_wellFormed
                                    wf.heap write,
                                  AllocationState.writeActivationLocal_preserves_supplies
                                    wf.supplies write,
                                  stackLive_transport wf.stack
                                    (Heap.writeActivationLocal_retainsActivations write),
                                  trivial⟩
                        | lazyMutable slot initializer =>
                            cases write : state.heap.writeActivationLocal current slot
                                p.nilObject with
                            | none => simp [Program.bodyMachineNext,
                                eagerLocalInitializer, nilInitializedLocal, write] at next
                            | some heap =>
                                simp [Program.bodyMachineNext, eagerLocalInitializer,
                                  nilInitializedLocal, write] at next
                                subst after
                                refine ⟨writeActivationLocal_preserves_wellFormed
                                    wf.heap write,
                                  AllocationState.writeActivationLocal_preserves_supplies
                                    wf.supplies write,
                                  stackLive_transport wf.stack
                                    (Heap.writeActivationLocal_retainsActivations write),
                                  trivial⟩
              · simp [Program.bodyMachineNext, currentActivation] at next
          | body target statements =>
              cases statements with
              | nil =>
                  simp [Program.bodyMachineNext] at next
                  subst after
                  exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
              | cons statement remaining =>
                  simp [Program.bodyMachineNext] at next
                  subst after
                  exact ⟨wf.heap, wf.supplies, by
                    simpa [StackLive] using wf.stack, trivial⟩
          | finish value =>
              cases activationLive : state.heap.activations current with
              | none => simp [Program.bodyMachineNext, activationLive] at next
              | some activation =>
                  cases sever : state.heap.severActivationContinuation current with
                  | none => simp [Program.bodyMachineNext, activationLive, sever] at next
                  | some heap =>
                      cases continuation : activation.continuation with
                      | none =>
                          simp [Program.bodyMachineNext, activationLive, sever,
                            continuation] at next
                          subst after
                          exact ⟨severActivationContinuation_preserves_wellFormed
                              wf.heap sever,
                            AllocationState.severActivationContinuation_preserves_supplies
                              wf.supplies sever,
                            trivial, trivial⟩
                      | some target =>
                          cases resume : resumeActivation
                              (.push rest ⟨current, frames⟩) target with
                          | none => simp [Program.bodyMachineNext, activationLive,
                              sever, continuation, resume] at next
                          | some resumed =>
                              simp [Program.bodyMachineNext, activationLive, sever,
                                continuation, resume] at next
                              subst after
                              refine ⟨severActivationContinuation_preserves_wellFormed
                                  wf.heap sever,
                                AllocationState.severActivationContinuation_preserves_supplies
                                  wf.supplies sever,
                                ?_, trivial⟩
                              exact stackLive_transport
                                (stackLive_resumeActivation wf.stack resume)
                                (Heap.severActivationContinuation_retainsActivations sever)
          | dispatch request message => simp [Program.bodyMachineNext] at next
          | invoke method receiver definingClass message =>
              simp [Program.bodyMachineNext] at next
          | invokeClosure closure message => simp [Program.bodyMachineNext] at next
          | transfer target value => simp [Program.bodyMachineNext] at next
          | halt value => simp [Program.bodyMachineNext] at next
          | abort exception => simp [Program.bodyMachineNext] at next
          | throw error => simp [Program.bodyMachineNext] at next
          | runtimeError error => simp [Program.bodyMachineNext] at next

theorem returnMachineStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.ReturnMachineStep before after) :
    SequentialWellFormed p after := by
  classical
  cases step with
  | graph next =>
      rcases before with ⟨state, stack, control⟩
      cases stack with
      | empty => simp [Program.returnMachineNext] at next
      | push rest frame =>
          rcases frame with ⟨current, frames⟩
          cases control with
          | object value =>
              cases frames with
              | empty => simp [Program.returnMachineNext] at next
              | push below top =>
                  cases top <;> try { simp [Program.returnMachineNext] at next }
                  case returnFrame =>
                    cases targetResult : state.heap.returnTarget current with
                    | none =>
                        simp [Program.returnMachineNext, targetResult] at next
                    | some target =>
                        simp [Program.returnMachineNext, targetResult] at next
                        subst after
                        exact ⟨wf.heap, wf.supplies, by
                          simpa [StackLive] using wf.stack, trivial⟩
          | transfer target value =>
              cases expectedResult : state.heap.returnTarget current with
              | none => simp [Program.returnMachineNext, expectedResult] at next
              | some expected =>
                  by_cases targetMatches : target = expected
                  · subst expected
                    cases targetLive : state.heap.activations target with
                    | none =>
                        simp [Program.returnMachineNext, expectedResult,
                          targetLive] at next
                    | some targetActivation =>
                        have markedHeap := markUncontinuable_preserves_wellFormed
                          wf.heap target
                        have markedSupplies :=
                          AllocationState.markUncontinuable_preserves_supplies
                            wf.supplies target
                        have retained := stackLive_transport wf.stack
                          (Heap.markUncontinuable_retainsActivations state.heap target)
                        cases continuable : targetActivation.continuable with
                        | false =>
                            simp [Program.returnMachineNext, expectedResult,
                              targetLive, continuable] at next
                            subst after
                            exact ⟨markedHeap, markedSupplies, retained, trivial⟩
                        | true =>
                            cases continuation : targetActivation.continuation with
                            | none =>
                                simp [Program.returnMachineNext, expectedResult,
                                  targetLive, continuable, continuation] at next
                                subst after
                                exact ⟨markedHeap, markedSupplies, retained, trivial⟩
                            | some continuationId =>
                                cases resume : resumeActivation
                                    (.push rest ⟨current, frames⟩)
                                    continuationId with
                                | none =>
                                    simp [Program.returnMachineNext, expectedResult,
                                      targetLive, continuable, continuation,
                                      resume] at next
                                | some resumed =>
                                    simp [Program.returnMachineNext, expectedResult,
                                      targetLive, continuable, continuation,
                                      resume] at next
                                    subst after
                                    refine ⟨markedHeap, markedSupplies, ?_, trivial⟩
                                    exact stackLive_transport
                                      (stackLive_resumeActivation wf.stack resume)
                                      (Heap.markUncontinuable_retainsActivations
                                        state.heap target)
                  · simp [Program.returnMachineNext, expectedResult,
                      targetMatches] at next
          | evaluate expression => simp [Program.returnMachineNext] at next
          | evaluateMessage template => simp [Program.returnMachineNext] at next
          | messageValue message => simp [Program.returnMachineNext] at next
          | initClass classId object message =>
              simp [Program.returnMachineNext] at next
          | ownInitialization classId object message =>
              simp [Program.returnMachineNext] at next
          | initializeSlotGroups object groups body =>
              simp [Program.returnMachineNext] at next
          | initializeSequentialSlots object declarations remaining body =>
              simp [Program.returnMachineNext] at next
          | dispatch request message => simp [Program.returnMachineNext] at next
          | invoke method receiver definingClass message =>
              simp [Program.returnMachineNext] at next
          | invokeClosure closure message => simp [Program.returnMachineNext] at next
          | «initialize» activation groups body target =>
              simp [Program.returnMachineNext] at next
          | body target statements => simp [Program.returnMachineNext] at next
          | finish value => simp [Program.returnMachineNext] at next
          | halt value => simp [Program.returnMachineNext] at next
          | abort exception => simp [Program.returnMachineNext] at next
          | throw error => simp [Program.returnMachineNext] at next
          | runtimeError error => simp [Program.returnMachineNext] at next

theorem objectSlotStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.ObjectSlotStep before after) : SequentialWellFormed p after := by
  cases step with
  | atom => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | read => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | writeStart =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | writeCommit written =>
      refine ⟨wf.heap.writeObjectSlot_wellFormed written,
        AllocationState.writeObjectSlot_preserves_supplies wf.supplies written,
        ?_, trivial⟩
      exact stackLive_transport wf.stack
        (Heap.writeObjectSlot_retainsActivations written)
  | currentRead => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | currentWrite => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | lazyHit => exact ⟨wf.heap, wf.supplies, wf.stack, trivial⟩
  | lazyMiss =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | lazyCommit written =>
      refine ⟨wf.heap.writeObjectSlot_wellFormed written,
        AllocationState.writeObjectSlot_preserves_supplies wf.supplies written,
        ?_, trivial⟩
      exact stackLive_transport wf.stack
        (Heap.writeObjectSlot_retainsActivations written)

theorem allocateClassPair_retainsActivations (p : Program)
    (state : AllocationState) (origin : ClassOrigin)
    (instanceMixin classMixin : MixinId) (superclass : ClassId)
    (enclosingObject : ObjRef) (factory : FactoryDef) :
    ∀ id activation, state.heap.activations id = some activation →
      ∃ activation',
        (p.allocateClassPair state origin instanceMixin classMixin superclass
          enclosingObject factory).1.heap.activations id = some activation' := by
  intro id activation live
  exact ⟨activation, by
    simpa [Program.allocateClassPair, Heap.installClass] using live⟩

theorem classConstructionStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.ClassConstructionStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | bodyStart =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | bodyCommit valid topValid allocated allocationWf =>
      refine ⟨allocationWf, ?_, ?_, trivial⟩
      · rw [allocated]
        exact allocateClassPair_preserves_supplies p wf.supplies _ _ _ _ _ _
      · rw [allocated]
        exact stackLive_transport wf.stack
          (allocateClassPair_retainsActivations p _ _ _ _ _ _ _)
  | bodyInheritanceError =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | bodyTopError =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | mixinStart =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | mixinSuperclassDone =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | mixinCommit source factory message factoryMatches allocated allocationWf =>
      refine ⟨allocationWf, ?_, ?_, trivial⟩
      · rw [allocated]
        exact allocateClassPair_preserves_supplies p wf.supplies _ _ _ _ _ _
      · rw [allocated]
        exact stackLive_transport wf.stack
          (allocateClassPair_retainsActivations p _ _ _ _ _ _ _)
  | mixinSuperclassError =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩
  | mixinSourceError =>
      exact ⟨wf.heap, wf.supplies, by simpa [StackLive] using wf.stack, trivial⟩

theorem messageEvaluationStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.MessageEvaluationStep before after) :
    SequentialWellFormed p after := by
  cases step with
  | @start state rest current frames template =>
      rcases template with ⟨selector, arguments⟩
      cases arguments with
      | nil => exact ⟨by simpa [Program.startMessageEvaluation] using wf.heap,
          by simpa [Program.startMessageEvaluation] using wf.supplies,
          by simpa [Program.startMessageEvaluation, StackLive] using wf.stack,
          trivial⟩
      | cons first remaining =>
          exact ⟨by simpa [Program.startMessageEvaluation] using wf.heap,
            by simpa [Program.startMessageEvaluation] using wf.supplies,
            by simpa [Program.startMessageEvaluation, StackLive] using wf.stack,
            trivial⟩
  | @argument state rest current frames selector values remaining value =>
      cases remaining with
      | nil =>
          exact ⟨by simpa [Program.continueMessageEvaluation] using wf.heap,
            by simpa [Program.continueMessageEvaluation] using wf.supplies,
            by simpa [Program.continueMessageEvaluation, StackLive] using wf.stack,
            trivial⟩
      | cons first later =>
          exact ⟨by simpa [Program.continueMessageEvaluation] using wf.heap,
            by simpa [Program.continueMessageEvaluation] using wf.supplies,
            by simpa [Program.continueMessageEvaluation, StackLive] using wf.stack,
            trivial⟩

theorem sequentialStep_preserves_wellFormed {p : Program}
    {before after : SequentialConfig} (wf : SequentialWellFormed p before)
    (step : p.SequentialStep before after) : SequentialWellFormed p after := by
  cases step with
  | expression expression =>
      exact expressionOrderStep_preserves_wellFormed wf expression
  | request request =>
      exact requestCompletionStep_preserves_wellFormed wf request
  | invocation invocation =>
      exact methodInvocationStep_preserves_wellFormed wf invocation
  | body body => exact bodyMachineStep_preserves_wellFormed wf body
  | returns returns => exact returnMachineStep_preserves_wellFormed wf returns
  | closure closure => exact closureMachineStep_preserves_wellFormed wf closure
  | objectSlots slots => exact objectSlotStep_preserves_wellFormed wf slots
  | classes classes => exact classConstructionStep_preserves_wellFormed wf classes
  | messages messages => exact messageEvaluationStep_preserves_wellFormed wf messages

end Program
end Newspeak
