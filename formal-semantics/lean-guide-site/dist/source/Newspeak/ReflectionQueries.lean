import Newspeak.ReflectionRuntimePreparation
import Newspeak.HeapEnumeration

namespace Newspeak

/-- A class identity paired with the cohort heap in which its record lives. -/
structure LocatedClass where
  location : HeapLocation
  classId : ClassId
deriving Repr, DecidableEq, BEq

structure ReflectedMethod where
  mixin : MixinId
  definition : MethodDef
  body : List Statement
  locals : List LocalDeclarationGroup

structure ReflectedClass where
  location : HeapLocation
  definition : ClassDef

structure ReflectedObject where
  location : HeapLocation
  classId : ClassId

structure ReflectedActivation where
  location : HeapLocation
  definition : ActivationDef

structure ReflectedActor where
  allocation : AllocationState
  runState : Option ActorRunState

/-- Exhaustive reflected-read API.  Enumeration is explicit because it has
    authority targets different from reading an individual record. -/
inductive ReflectionQuery where
  | inspectVM (mirror : MirrorId)
  | inspectProgram (mirror : MirrorId)
  | inspectMixin (mirror : MirrorId) (mixin : MixinId)
  | inspectMethod (mirror : MirrorId) (method : MethodId)
  | inspectClass (mirror : MirrorId) (classId : ClassId)
  | inspectObject (mirror : MirrorId) (object : ObjRef)
  | inspectActivation (mirror : MirrorId) (activation : ActivationId)
  | inspectActor (mirror : MirrorId) (actor : ActorId)
  | enumerateInstancesOf (mirror : MirrorId) (classId : ClassId)
  | enumerateApplicationsOf (mirror : MirrorId) (mixin : MixinId)

inductive ReflectionQueryResult where
  | vm (identity : VMId) (programVersion : Nat)
  | program (value : Program)
  | mixin (value : MixinDef)
  | method (value : ReflectedMethod)
  | class (value : ReflectedClass)
  | object (value : ReflectedObject)
  | activation (value : ReflectedActivation)
  | actor (value : ReflectedActor)
  | instances (values : List ObjRef)
  | applications (values : List LocatedClass)

def ReflectionQuery.mirror : ReflectionQuery → MirrorId
  | .inspectVM mirror | .inspectProgram mirror | .inspectMixin mirror _
  | .inspectMethod mirror _ | .inspectClass mirror _
  | .inspectObject mirror _ | .inspectActivation mirror _
  | .inspectActor mirror _ | .enumerateInstancesOf mirror _
  | .enumerateApplicationsOf mirror _ => mirror

def ReflectionQuery.authorizationTarget (world : ActorWorld) :
    ReflectionQuery → MirrorTarget
  | .inspectVM _ => .vmTarget world.vm
  | .inspectProgram _ => .programTarget
  | .inspectMixin _ mixin | .enumerateApplicationsOf _ mixin =>
      .mixinTarget mixin
  | .inspectMethod _ method => .methodTarget method
  | .inspectClass _ classId | .enumerateInstancesOf _ classId =>
      .classTarget classId
  | .inspectObject _ object => .objectTarget object
  | .inspectActivation _ activation => .activationTarget activation
  | .inspectActor _ actor => .actorTarget actor

def ReflectionQuery.Authorized (world : ActorWorld) (actor : ActorId)
    (query : ReflectionQuery) : Prop :=
  MirrorAuthorizes world actor query.mirror (query.authorizationTarget world)
    .inspect

def ActorWorld.heapAt (world : ActorWorld) : HeapLocation → Option Heap
  | .shared => some world.valueHeap
  | .actor actor => (world.actorAllocations actor).map AllocationState.heap

def ActorWorld.locateObjectReference (world : ActorWorld) (object : ObjRef) :
    Option HeapLocation :=
  if (world.valueHeap.classOf object).isSome then some .shared
  else
    (world.firstActorHeapSatisfying (fun heap =>
      (heap.classOf object).isSome) world.actorAllocations.domain).map .actor

def Program.findMethodInMixin (mixin : MixinDef) (method : MethodId) :
    List Selector → Option MethodDef
  | [] => none
  | selector :: remaining =>
      match mixin.methods selector with
      | some definition =>
          if definition.identity = method then some definition
          else findMethodInMixin mixin method remaining
      | none => findMethodInMixin mixin method remaining

def Program.findMethodDefinition (program : Program) (method : MethodId) :
    List MixinId → Option (MixinId × MethodDef)
  | [] => none
  | mixinId :: remaining =>
      match program.mixins mixinId with
      | some mixin =>
          match Program.findMethodInMixin mixin method mixin.methods.domain with
          | some definition => some (mixinId, definition)
          | none => program.findMethodDefinition method remaining
      | none => program.findMethodDefinition method remaining

def ActorWorld.actorApplicationsOf (world : ActorWorld) (mixin : MixinId) :
    List ActorId → List LocatedClass
  | [] => []
  | actor :: remaining =>
      let current := match world.actorAllocations actor with
        | none => []
        | some allocation =>
            (allocation.heap.allApplicationsOf mixin).map fun classId =>
              ⟨.actor actor, classId⟩
      current ++ world.actorApplicationsOf mixin remaining

def ActorWorld.allCohortApplicationsOf (world : ActorWorld) (mixin : MixinId) :
    List LocatedClass :=
  (world.valueHeap.allApplicationsOf mixin).map (LocatedClass.mk .shared) ++
    world.actorApplicationsOf mixin world.actorAllocations.domain

def ReflectionQuery.execute (world : ActorWorld) :
    ReflectionQuery → Option ReflectionQueryResult
  | .inspectVM _ => some (.vm world.vm world.programVersion)
  | .inspectProgram _ => some (.program world.program)
  | .inspectMixin _ mixin => do
      let definition ← world.program.mixins mixin
      some (.mixin definition)
  | .inspectMethod _ method => do
      let (mixin, definition) ←
        world.program.findMethodDefinition method world.program.mixins.domain
      let body ← world.program.methodBodies method
      some (.method ⟨mixin, definition, body,
        world.program.methodLocals method⟩)
  | .inspectClass _ classId => do
      let location ← world.locateClassId classId
      let heap ← world.heapAt location
      let definition ← heap.classes classId
      some (.class ⟨location, definition⟩)
  | .inspectObject _ object => do
      let location ← world.locateObjectReference object
      let heap ← world.heapAt location
      let classId ← heap.classOf object
      some (.object ⟨location, classId⟩)
  | .inspectActivation _ activation => do
      let location ← world.locateActivationId activation
      let heap ← world.heapAt location
      let definition ← heap.activations activation
      some (.activation ⟨location, definition⟩)
  | .inspectActor _ actor => do
      let allocation ← world.actorAllocations actor
      some (.actor ⟨allocation, world.runStates actor⟩)
  | .enumerateInstancesOf _ classId => do
      let location ← world.locateClassId classId
      let heap ← world.heapAt location
      some (.instances (heap.allInstancesOf classId))
  | .enumerateApplicationsOf _ mixin => do
      let _ ← world.program.mixins mixin
      some (.applications (world.allCohortApplicationsOf mixin))

/-- A reflected read exists only after the requesting actor supplies a mirror
    whose authority contains the target and includes `inspect`. -/
structure AuthorizedReflectionRead (world : ActorWorld) (requester : ActorId)
    (query : ReflectionQuery) (result : ReflectionQueryResult) : Prop where
  authorized : query.Authorized world requester
  executed : query.execute world = some result

theorem AuthorizedReflectionRead.requires_inspect
    {world : ActorWorld} {requester : ActorId} {query : ReflectionQuery}
    {result : ReflectionQueryResult}
    (read : AuthorizedReflectionRead world requester query result) :
    MirrorAuthorizes world requester query.mirror
      (query.authorizationTarget world)
      .inspect :=
  read.authorized

/-- Reads and changes are the exhaustive externally visible reflection access
    forms.  The common theorem below exposes the exact target and right checked
    for either kind. -/
inductive ReflectionAccess (world : ActorWorld) (requester : ActorId) : Prop
  | read {query result} :
      AuthorizedReflectionRead world requester query result →
      ReflectionAccess world requester
  | change {command : ReflectionCommand} : command.Authorized world requester →
      ReflectionAccess world requester

theorem ReflectionAccess.is_authorized
    {world : ActorWorld} {requester : ActorId}
    (access : ReflectionAccess world requester) :
    (∃ (query : ReflectionQuery) (result : ReflectionQueryResult),
      query.execute world = some result ∧
      MirrorAuthorizes world requester query.mirror
        (query.authorizationTarget world) .inspect) ∨
    (∃ command : ReflectionCommand,
      MirrorAuthorizes world requester command.mirror command.target
        command.requiredRight) := by
  cases access with
  | read reflected =>
      exact .inl ⟨_, _, reflected.executed, reflected.authorized⟩
  | change authorized => exact .inr ⟨_, authorized⟩

end Newspeak
