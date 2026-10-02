import Newspeak.ReflectionAuthority

namespace Newspeak

inductive FrameControl where
  | activeControl (frames : EvalStack) (term : ControlTerm)
  | suspendedControl (frames : EvalStack)
deriving Repr

inductive FrameTemplateKey where
  | retain (activation : ActivationId)
  | freshFrame (key : FreshFrameId)
deriving Repr, DecidableEq, BEq

/-- Complete activation record whose activation-valued internal links refer
    to keys in the same stack template. -/
structure ActivationRecordTemplate where
  objectClass : ClassId
  provenance : ActivationProvenance
  parameters : FiniteStore ParameterId ObjRef
  locals : FiniteStore LocalSlotId LocalCell
  currentReceiver : ObjRef
  currentClass : Option ClassId
  continuation : Option FrameTemplateKey
  homeMethod : Option FrameTemplateKey
  continuable : Bool
  activationScopes : FiniteStore ActivationDeclId FrameTemplateKey
  objectLiteralScopes : FiniteStore ObjectLiteralDeclId ObjRef

structure FrameTemplate where
  key : FrameTemplateKey
  activation : ActivationRecordTemplate
  control : FrameControl

abbrev StackTemplate := List FrameTemplate

structure MixinInitializerReplacement where
  declaration : ActivationDeclId
  selector : Selector
  parameters : List ParameterId
  groups : List SlotDeclarationGroup
  body : List Statement

/-- The seven command families are constructors of one sum, making their
    partition exhaustive and disjoint by construction.  Constructor names are
    intentionally distinct from base-language writes and from one another. -/
inductive ReflectionCommand where
  | replaceMethodBody (mirror : MirrorId) (method : MethodId)
      (body : List Statement)
  | replaceMethodDefinition (mirror : MirrorId) (mixin : MixinId)
      (method : MethodId) (definition : MethodDef)
      (localGroups : List LocalDeclarationGroup) (body : List Statement)
  | addMethodDefinition (mirror : MirrorId) (mixin : MixinId)
      (definition : MethodDef) (localGroups : List LocalDeclarationGroup)
      (body : List Statement)
  | removeMethodDefinition (mirror : MirrorId) (mixin : MixinId)
      (method : MethodId)
  | replaceSlotDeclarations (mirror : MirrorId) (mixin : MixinId)
      (groups : List SlotDeclarationGroup)
  | replaceNestedDeclarations (mirror : MirrorId) (mixin : MixinId)
      (declarations : List ClassDeclId)
  | replaceMixinInitializer (mirror : MirrorId) (mixin : MixinId)
      (initializer : MixinInitializerReplacement)
  | changeSuperclass (mirror : MirrorId) (classId superclass : ClassId)
  | changeClassEnclosingObject (mirror : MirrorId) (classId : ClassId)
      (enclosingObject : ObjRef)
  | changeObjectClass (mirror : MirrorId) (object : ObjectId)
      (classId : ClassId)
  | objectSlotWrite (mirror : MirrorId) (object : ObjectId)
      (slot : SlotId) (value : ObjRef)
  | activationParameterWrite (mirror : MirrorId) (activation : ActivationId)
      (parameter : ParameterId) (value : ObjRef)
  | activationLocalWrite (mirror : MirrorId) (activation : ActivationId)
      (slot : LocalSlotId) (value : ObjRef)
  | changeActivationCurrentClass (mirror : MirrorId)
      (activation : ActivationId) (classId : Option ClassId)
  | changeActivationContinuation (mirror : MirrorId)
      (activation : ActivationId) (continuation : Option ActivationId)
  | makeActivationUncontinuable (mirror : MirrorId)
      (activation : ActivationId)
  | continueAtActivation (mirror : MirrorId) (actor : ActorId)
      (activation : ActivationId) (value : ObjRef)
  | pauseActor (mirror : MirrorId) (actor : ActorId)
      (reason : DebuggerStopReason)
  | replaceCurrentActorStack (mirror : MirrorId) (actor : ActorId)
      (stack : StackTemplate)
  | replacePausedActorStack (mirror : MirrorId) (actor : ActorId)
      (token : PauseTokenId) (stack : StackTemplate)
  | resumePausedActorAtFullSpeed (mirror : MirrorId) (actor : ActorId)
      (token : PauseTokenId)
  | replaceAndResumePausedActorStack (mirror : MirrorId) (actor : ActorId)
      (token : PauseTokenId) (stack : StackTemplate)

inductive ReflectionCommandKind where
  | code
  | classGraph
  | objectClass
  | objectSlot
  | activation
  | continuation
  | debugger
deriving Repr, DecidableEq, BEq

def ReflectionCommand.kind : ReflectionCommand → ReflectionCommandKind
  | .replaceMethodBody ..
  | .replaceMethodDefinition ..
  | .addMethodDefinition ..
  | .removeMethodDefinition ..
  | .replaceSlotDeclarations ..
  | .replaceNestedDeclarations ..
  | .replaceMixinInitializer .. => .code
  | .changeSuperclass ..
  | .changeClassEnclosingObject .. => .classGraph
  | .changeObjectClass .. => .objectClass
  | .objectSlotWrite .. => .objectSlot
  | .activationParameterWrite ..
  | .activationLocalWrite ..
  | .changeActivationCurrentClass ..
  | .changeActivationContinuation ..
  | .makeActivationUncontinuable .. => .activation
  | .continueAtActivation .. => .continuation
  | .pauseActor ..
  | .replaceCurrentActorStack ..
  | .replacePausedActorStack ..
  | .resumePausedActorAtFullSpeed ..
  | .replaceAndResumePausedActorStack .. => .debugger

def ReflectionCommand.mirror : ReflectionCommand → MirrorId
  | .replaceMethodBody mirror ..
  | .replaceMethodDefinition mirror ..
  | .addMethodDefinition mirror ..
  | .removeMethodDefinition mirror ..
  | .replaceSlotDeclarations mirror ..
  | .replaceNestedDeclarations mirror ..
  | .replaceMixinInitializer mirror ..
  | .changeSuperclass mirror ..
  | .changeClassEnclosingObject mirror ..
  | .changeObjectClass mirror ..
  | .objectSlotWrite mirror ..
  | .activationParameterWrite mirror ..
  | .activationLocalWrite mirror ..
  | .changeActivationCurrentClass mirror ..
  | .changeActivationContinuation mirror ..
  | .makeActivationUncontinuable mirror ..
  | .continueAtActivation mirror ..
  | .pauseActor mirror ..
  | .replaceCurrentActorStack mirror ..
  | .replacePausedActorStack mirror ..
  | .resumePausedActorAtFullSpeed mirror ..
  | .replaceAndResumePausedActorStack mirror .. => mirror

def ReflectionCommand.requiredRight (command : ReflectionCommand) : ReflectRight :=
  match command.kind with
  | .code => .editCode
  | .classGraph => .editClass
  | .objectClass => .reclassifyObject
  | .objectSlot => .editObjectSlots
  | .activation => .editActivation
  | .continuation => .controlContinuation
  | .debugger => .controlActorStack

def ReflectionCommand.target : ReflectionCommand → MirrorTarget
  | .replaceMethodBody _ method _ => .methodTarget method
  | .replaceMethodDefinition _ _ method _ _ _ => .methodTarget method
  | .addMethodDefinition _ mixin _ _ _ => .mixinTarget mixin
  | .removeMethodDefinition _ _ method => .methodTarget method
  | .replaceSlotDeclarations _ mixin _
  | .replaceNestedDeclarations _ mixin _
  | .replaceMixinInitializer _ mixin _ => .mixinTarget mixin
  | .changeSuperclass _ classId _
  | .changeClassEnclosingObject _ classId _ => .classTarget classId
  | .changeObjectClass _ object _
  | .objectSlotWrite _ object _ _ => .objectTarget (.ordinaryObject object)
  | .activationParameterWrite _ activation _ _
  | .activationLocalWrite _ activation _ _
  | .changeActivationCurrentClass _ activation _
  | .changeActivationContinuation _ activation _
  | .makeActivationUncontinuable _ activation
  | .continueAtActivation _ _ activation _ => .activationTarget activation
  | .pauseActor _ actor _
  | .replaceCurrentActorStack _ actor _
  | .replacePausedActorStack _ actor _ _
  | .resumePausedActorAtFullSpeed _ actor _
  | .replaceAndResumePausedActorStack _ actor _ _ => .actorTarget actor

def ReflectionCommand.Authorized (world : ActorWorld) (actor : ActorId)
    (command : ReflectionCommand) : Prop :=
  MirrorAuthorizes world actor command.mirror command.target
    command.requiredRight

inductive ActivationFieldLocation where
  | parameter (parameter : ParameterId)
  | local (slot : LocalSlotId)
  | currentClass
  | continuation
  | continuable
deriving Repr, DecidableEq, BEq

inductive ReflectionWriteLocation where
  | methodBody (method : MethodId)
  | methodDefinition (method : MethodId)
  /-- The selector-to-method dictionary of one mixin.  This deliberately
      coarsens selector-level writes: method replacement and removal inspect
      the old selector as well as writing the new one, so disjoint new
      selectors alone are not a sufficient noninterference test. -/
  | methodDictionary (mixin : MixinId)
  | selector (mixin : MixinId) (selector : Selector)
  | slotDeclarations (mixin : MixinId)
  | nestedDeclarations (mixin : MixinId)
  | mixinInitializer (mixin : MixinId)
  | superclass (classId : ClassId)
  | classEnclosingObject (classId : ClassId)
  | objectClass (object : ObjectId)
  | objectSlot (object : ObjectId) (slot : SlotId)
  /-- The continuation-dependency graph as a whole.  Operations that pop or
      retire frames can update a state-dependent set of activation records,
      so their static footprint must conservatively overlap every activation
      record and field. -/
  | activationGraph
  | activationRecord (activation : ActivationId)
  | activationField (activation : ActivationId)
      (field : ActivationFieldLocation)
  | actorStack (actor : ActorId)
  /-- Global supply consumed when a debugger operation mints a fresh pause
      token.  Recording it prevents two otherwise actor-disjoint token-minting
      commands from being classified as literally commuting: their execution
      order assigns the two fresh numbers to different actors. -/
  | pauseTokenSupply
deriving Repr, DecidableEq, BEq

def stackTemplateRecordLocations (stack : StackTemplate) :
    List ReflectionWriteLocation :=
  stack.filterMap fun frame => match frame.key with
    | .retain activation => some (.activationRecord activation)
    | .freshFrame _ => none

def ReflectionCommand.debuggerActor? : ReflectionCommand → Option ActorId
  | .pauseActor _ actor _
  | .replaceCurrentActorStack _ actor _
  | .replacePausedActorStack _ actor _ _
  | .resumePausedActorAtFullSpeed _ actor _
  | .replaceAndResumePausedActorStack _ actor _ _ => some actor
  | _ => none

def ReflectionCommand.mintsPauseToken : ReflectionCommand → Bool
  | .pauseActor .. | .replacePausedActorStack .. => true
  | _ => false

def ReflectionCommand.replacesStack : ReflectionCommand → Bool
  | .replaceCurrentActorStack ..
  | .replacePausedActorStack ..
  | .replaceAndResumePausedActorStack .. => true
  | _ => false

def ReflectionCommand.writes : ReflectionCommand → List ReflectionWriteLocation
  | .replaceMethodBody _ method _ => [.methodBody method]
  | .replaceMethodDefinition _ mixin method definition _ _ =>
      [.methodDefinition method, .methodBody method,
        .methodDictionary mixin, .selector mixin definition.selector]
  | .addMethodDefinition _ mixin definition _ _ =>
      [.methodDefinition definition.identity, .methodBody definition.identity,
        .methodDictionary mixin, .selector mixin definition.selector]
  | .removeMethodDefinition _ mixin method =>
      [.methodDefinition method, .methodBody method, .methodDictionary mixin]
  | .replaceSlotDeclarations _ mixin _ => [.slotDeclarations mixin]
  | .replaceNestedDeclarations _ mixin _ => [.nestedDeclarations mixin]
  | .replaceMixinInitializer _ mixin _ => [.mixinInitializer mixin]
  | .changeSuperclass _ classId _ => [.superclass classId]
  | .changeClassEnclosingObject _ classId _ => [.classEnclosingObject classId]
  | .changeObjectClass _ object _ => [.objectClass object]
  | .objectSlotWrite _ object slot _ => [.objectSlot object slot]
  | .activationParameterWrite _ activation parameter _ =>
      [.activationField activation (.parameter parameter)]
  | .activationLocalWrite _ activation slot _ =>
      [.activationField activation (.local slot)]
  | .changeActivationCurrentClass _ activation _ =>
      [.activationField activation .currentClass]
  | .changeActivationContinuation _ activation _ =>
      [.activationField activation .continuation]
  | .makeActivationUncontinuable _ activation =>
      [.activationGraph, .activationField activation .continuable]
  | .continueAtActivation _ actor activation _ =>
      [.actorStack actor, .activationGraph,
        .activationField activation .continuation]
  | .pauseActor _ actor _ => [.actorStack actor, .pauseTokenSupply]
  | .replaceCurrentActorStack _ actor stack
  | .replaceAndResumePausedActorStack _ actor _ stack =>
      .actorStack actor :: .activationGraph :: stackTemplateRecordLocations stack
  | .replacePausedActorStack _ actor _ stack =>
      .pauseTokenSupply :: .actorStack actor :: .activationGraph ::
        stackTemplateRecordLocations stack
  | .resumePausedActorAtFullSpeed _ actor _ => [.actorStack actor]

inductive ReflectionLocationsOverlap :
    ReflectionWriteLocation → ReflectionWriteLocation → Prop where
  | same (location : ReflectionWriteLocation) :
      ReflectionLocationsOverlap location location
  | recordField (activation : ActivationId) (field : ActivationFieldLocation) :
      ReflectionLocationsOverlap (.activationRecord activation)
        (.activationField activation field)
  | fieldRecord (activation : ActivationId) (field : ActivationFieldLocation) :
      ReflectionLocationsOverlap (.activationField activation field)
        (.activationRecord activation)
  | dictionarySelector (mixin : MixinId) (selector : Selector) :
      ReflectionLocationsOverlap (.methodDictionary mixin)
        (.selector mixin selector)
  | selectorDictionary (mixin : MixinId) (selector : Selector) :
      ReflectionLocationsOverlap (.selector mixin selector)
        (.methodDictionary mixin)
  | graphRecord (activation : ActivationId) :
      ReflectionLocationsOverlap .activationGraph (.activationRecord activation)
  | recordGraph (activation : ActivationId) :
      ReflectionLocationsOverlap (.activationRecord activation) .activationGraph
  | graphField (activation : ActivationId) (field : ActivationFieldLocation) :
      ReflectionLocationsOverlap .activationGraph
        (.activationField activation field)
  | fieldGraph (activation : ActivationId) (field : ActivationFieldLocation) :
      ReflectionLocationsOverlap (.activationField activation field)
        .activationGraph

def ReflectionCommandsCompatible (first second : ReflectionCommand) : Prop :=
  ∀ left, left ∈ first.writes →
    ∀ right, right ∈ second.writes →
      ¬ReflectionLocationsOverlap left right

def ReflectionTransactionNonconflicting
    (transaction : List ReflectionCommand) : Prop :=
  transaction.Pairwise ReflectionCommandsCompatible

theorem ReflectionCommand.kind_partition (command : ReflectionCommand) :
    command.kind = .code ∨ command.kind = .classGraph ∨
    command.kind = .objectClass ∨ command.kind = .objectSlot ∨
    command.kind = .activation ∨ command.kind = .continuation ∨
    command.kind = .debugger := by
  cases command <;> simp [ReflectionCommand.kind]

theorem ReflectionCommand.kind_eq_continuation_iff
    (command : ReflectionCommand) :
    command.kind = .continuation ↔
      ∃ mirror actor activation value,
        command = .continueAtActivation mirror actor activation value := by
  cases command <;> simp [ReflectionCommand.kind]

theorem ReflectionCommand.kind_eq_activation_iff
    (command : ReflectionCommand) :
    command.kind = .activation ↔
      (∃ mirror activation parameter value,
        command = .activationParameterWrite mirror activation parameter value) ∨
      (∃ mirror activation slot value,
        command = .activationLocalWrite mirror activation slot value) ∨
      (∃ mirror activation classId,
        command = .changeActivationCurrentClass mirror activation classId) ∨
      (∃ mirror activation continuation,
        command = .changeActivationContinuation mirror activation continuation) ∨
      (∃ mirror activation,
        command = .makeActivationUncontinuable mirror activation) := by
  cases command <;> simp [ReflectionCommand.kind]

theorem ReflectionCommand.kind_eq_debugger_iff
    (command : ReflectionCommand) :
    command.kind = .debugger ↔
      (∃ mirror actor reason, command = .pauseActor mirror actor reason) ∨
      (∃ mirror actor stack,
        command = .replaceCurrentActorStack mirror actor stack) ∨
      (∃ mirror actor token stack,
        command = .replacePausedActorStack mirror actor token stack) ∨
      (∃ mirror actor token,
        command = .resumePausedActorAtFullSpeed mirror actor token) ∨
      (∃ mirror actor token stack,
        command = .replaceAndResumePausedActorStack mirror actor token stack) := by
  cases command <;> simp [ReflectionCommand.kind]

theorem ReflectionCommand.debuggerActor?_isSome_iff
    (command : ReflectionCommand) :
    command.debuggerActor?.isSome = true ↔ command.kind = .debugger := by
  cases command <;>
    simp [ReflectionCommand.debuggerActor?, ReflectionCommand.kind]

theorem ReflectionLocationsOverlap.symmetric {left right}
    (overlap : ReflectionLocationsOverlap left right) :
    ReflectionLocationsOverlap right left := by
  cases overlap with
  | same _ => exact .same _
  | recordField activation field => exact .fieldRecord activation field
  | fieldRecord activation field => exact .recordField activation field
  | dictionarySelector mixin selector =>
      exact .selectorDictionary mixin selector
  | selectorDictionary mixin selector =>
      exact .dictionarySelector mixin selector
  | graphRecord activation => exact .recordGraph activation
  | recordGraph activation => exact .graphRecord activation
  | graphField activation field => exact .fieldGraph activation field
  | fieldGraph activation field => exact .graphField activation field

theorem ReflectionCommandsCompatible.symmetric {first second}
    (compatible : ReflectionCommandsCompatible first second) :
    ReflectionCommandsCompatible second first := by
  intro right rightMember left leftMember overlap
  exact compatible left leftMember right rightMember overlap.symmetric

end Newspeak
