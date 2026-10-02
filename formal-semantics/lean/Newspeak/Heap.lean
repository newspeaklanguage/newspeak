import Newspeak.Program
import Newspeak.FiniteStore

namespace Newspeak

/-- Run-time initializer attached to an instantiable class. -/
inductive InitializerPlan where
  | body (superclassMessage : MessageTemplate)
  | appliedMixin (superclassMessage mixinMessage : MessageTemplate)
deriving Repr

structure FactoryDef where
  activationDeclaration : ActivationDeclId
  selector : Selector
  parameters : List ParameterId
  plan : InitializerPlan
deriving Repr

/-- Runtime class records are heap records, not static program definitions. -/
structure ClassDef where
  mixin : MixinId
  superclass : ClassId
  enclosingObject : ObjRef
  metaclass : ClassId
  origin : ClassOrigin
  primaryFactory : Option FactoryDef

/-- VM-supported weak storage attached to an otherwise ordinary Newspeak
    object.  Fixed instance slots remain in `ObjectDef.slots` and are always
    strong.  Weak-map entries have weak keys and ephemeron (conditionally
    strong) values; that conditional reachability is defined separately from
    the base strong-reference graph. -/
inductive WeakContainer where
  | weakArray (elements : List ObjRef)
  | weakMap (entries : FiniteStore ObjRef ObjRef)

structure ObjectDef where
  classId : ClassId
  slots : FiniteStore SlotId ObjRef
  nestedClasses : FiniteStore ClassDeclId ClassId
  weakContainer : Option WeakContainer := none

inductive ActivationProvenance where
  | top
  | method (identity : MethodId)
  | closure (declaration : ActivationDeclId)
  | initializer (declaration : ActivationDeclId)
deriving Repr, DecidableEq, BEq

inductive LocalCell where
  | uninitialized
  | value (object : ObjRef)
deriving Repr, DecidableEq, BEq

structure ActivationDef where
  objectClass : ClassId
  provenance : ActivationProvenance
  parameters : FiniteStore ParameterId ObjRef
  locals : FiniteStore LocalSlotId LocalCell
  currentReceiver : ObjRef
  currentClass : Option ClassId
  continuation : Option ActivationId
  homeMethod : Option ActivationId
  continuable : Bool
  activationScopes : FiniteStore ActivationDeclId ActivationId
  objectLiteralScopes : FiniteStore ObjectLiteralDeclId ObjRef

structure ClosureDef where
  classId : ClassId
  declaration : ActivationDeclId
  parameters : List ParameterId
  locals : List LocalDeclarationGroup
  body : List Statement
  definingActivation : ActivationId
  capturedReceiver : ObjRef
  capturedClass : Option ClassId
  homeMethod : Option ActivationId

inductive MirrorPayload where
  | message (value : Message)
  | authority (value : MirrorAuthority)
  | opaque
deriving Repr, DecidableEq, BEq

structure MirrorDef where
  classId : ClassId
  payload : MirrorPayload
deriving Repr, DecidableEq, BEq

structure ActorDef where
  classId : ClassId

/-- Every runtime identity store has an exact finite executable domain. -/
structure Heap where
  classes : FiniteStore ClassId ClassDef
  objects : FiniteStore ObjectId ObjectDef
  mixinObjects : FiniteStore MixinId ClassId
  activations : FiniteStore ActivationId ActivationDef
  closures : FiniteStore ClosureId ClosureDef
  mirrors : FiniteStore MirrorId MirrorDef
  actors : FiniteStore ActorId ActorDef

namespace Heap

def installMirror (h : Heap) (id : MirrorId) (mirror : MirrorDef) : Heap :=
  { h with mirrors := h.mirrors.install id mirror }

/-- Functional update of the activation store at one freshly chosen identity. -/
def installActivation (h : Heap) (id : ActivationId)
    (activation : ActivationDef) : Heap :=
  { h with activations := h.activations.install id activation }

def installClosure (h : Heap) (id : ClosureId) (closure : ClosureDef) : Heap :=
  { h with closures := h.closures.install id closure }

def installClass (h : Heap) (id : ClassId) (classDef : ClassDef) : Heap :=
  { h with classes := h.classes.install id classDef }

def installObject (h : Heap) (id : ObjectId) (objectDef : ObjectDef) : Heap :=
  { h with objects := h.objects.install id objectDef }

def readObjectSlot (h : Heap) (object : ObjectId)
    (slot : SlotId) : Option ObjRef := do
  let objectDef ← h.objects object
  objectDef.slots slot

@[simp] def objectSlotTransform (slot : SlotId) (value : ObjRef)
    (objectDef : ObjectDef) : ObjectDef :=
  { objectDef with slots := objectDef.slots.install slot value }

def writeObjectSlot (h : Heap) (object : ObjectId) (slot : SlotId)
    (value : ObjRef) : Option Heap := do
  let objectDef ← h.objects object
  let _ ← objectDef.slots slot
  some (h.installObject object (objectSlotTransform slot value objectDef))

def readNestedClass (h : Heap) (object : ObjectId)
    (declaration : ClassDeclId) : Option ClassId := do
  let objectDef ← h.objects object
  objectDef.nestedClasses declaration

def writeNestedClass (h : Heap) (object : ObjectId)
    (declaration : ClassDeclId) (classId : ClassId) : Option Heap := do
  let objectDef ← h.objects object
  let updated : ObjectDef :=
    { objectDef with
      nestedClasses := objectDef.nestedClasses.install declaration classId }
  some (h.installObject object updated)

def readActivationLocal (h : Heap) (activation : ActivationId)
    (slot : LocalSlotId) : Option ObjRef := do
  let activationDef ← h.activations activation
  match activationDef.locals slot with
  | some (.value object) => some object
  | _ => none

/-- Direct activation-slot write.  It is defined only for a slot already
    present in the activation's physical local layout. -/
def writeActivationLocal (h : Heap) (activation : ActivationId)
    (slot : LocalSlotId) (value : ObjRef) : Option Heap := do
  let activationDef ← h.activations activation
  let _ ← activationDef.locals slot
  let updated : ActivationDef :=
    { activationDef with
      locals := activationDef.locals.install slot (.value value) }
  some (h.installActivation activation updated)

def severActivationContinuation (h : Heap)
    (activation : ActivationId) : Option Heap := do
  let activationDef ← h.activations activation
  some (h.installActivation activation
    { activationDef with continuation := none })

@[simp] theorem installMirror_at (h : Heap) (id : MirrorId)
    (mirror : MirrorDef) :
    (h.installMirror id mirror).mirrors id = some mirror := by
  simp [installMirror]

@[simp] theorem installMirror_away (h : Heap) {id candidate : MirrorId}
    (mirror : MirrorDef) (hne : candidate ≠ id) :
    (h.installMirror id mirror).mirrors candidate = h.mirrors candidate := by
  simp [installMirror, hne]

@[simp] theorem installActivation_at (h : Heap) (id : ActivationId)
    (activation : ActivationDef) :
    (h.installActivation id activation).activations id = some activation := by
  simp [installActivation]

@[simp] theorem installActivation_away (h : Heap)
    {id candidate : ActivationId} (activation : ActivationDef)
    (hne : candidate ≠ id) :
    (h.installActivation id activation).activations candidate =
      h.activations candidate := by
  simp [installActivation, hne]

@[simp] theorem installClosure_at (h : Heap) (id : ClosureId)
    (closure : ClosureDef) :
    (h.installClosure id closure).closures id = some closure := by
  simp [installClosure]

@[simp] theorem installClosure_away (h : Heap) {id candidate : ClosureId}
    (closure : ClosureDef) (hne : candidate ≠ id) :
    (h.installClosure id closure).closures candidate = h.closures candidate := by
  simp [installClosure, hne]

@[simp] theorem installClass_at (h : Heap) (id : ClassId)
    (classDef : ClassDef) :
    (h.installClass id classDef).classes id = some classDef := by
  simp [installClass]

@[simp] theorem installClass_away (h : Heap) {id candidate : ClassId}
    (classDef : ClassDef) (hne : candidate ≠ id) :
    (h.installClass id classDef).classes candidate = h.classes candidate := by
  simp [installClass, hne]

@[simp] theorem installObject_at (h : Heap) (id : ObjectId)
    (objectDef : ObjectDef) :
    (h.installObject id objectDef).objects id = some objectDef := by
  simp [installObject]

@[simp] theorem installObject_away (h : Heap) {id candidate : ObjectId}
    (objectDef : ObjectDef) (hne : candidate ≠ id) :
    (h.installObject id objectDef).objects candidate = h.objects candidate := by
  simp [installObject, hne]

def classOf (h : Heap) : ObjRef → Option ClassId
  | .ordinaryObject id => (h.objects id).map ObjectDef.classId
  | .classObject id => (h.classes id).map ClassDef.metaclass
  | .mixinObject id => h.mixinObjects id
  | .activationObject id => (h.activations id).map ActivationDef.objectClass
  | .closureObject id => (h.closures id).map ClosureDef.classId
  | .mirrorObject id => (h.mirrors id).map MirrorDef.classId
  | .actorObject id => (h.actors id).map ActorDef.classId

def IsLiveObject (h : Heap) (object : ObjRef) : Prop :=
  ∃ classId, h.classOf object = some classId

end Heap

namespace Program

def IsLiveClass (p : Program) (h : Heap) (c : ClassId) : Prop :=
  c = p.top ∨ ∃ cd, h.classes c = some cd

def direct (p : Program) (h : Heap) (c : ClassId)
    (s : Selector) : Option MethodDef := do
  let cd ← h.classes c
  let md ← p.mixins cd.mixin
  md.methods s

def superclass? (p : Program) (h : Heap) (c : ClassId) : Option ClassId := do
  if c = p.top then
    none
  else
    let cd ← h.classes c
    some cd.superclass

/-- `parent ≺ child` exactly when `parent` is the immediate superclass of
    `child`.  This orientation is suitable for `Acc`. -/
def SuperclassPrecedes (p : Program) (h : Heap)
    (parent child : ClassId) : Prop :=
  p.superclass? h child = some parent

theorem direct_unique {p : Program} {h : Heap} {c : ClassId} {s : Selector}
    {f g : MethodDef} (hf : p.direct h c s = some f)
    (hg : p.direct h c s = some g) : f = g := by
  rw [hf] at hg
  injection hg

end Program
end Newspeak
