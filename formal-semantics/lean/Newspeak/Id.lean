namespace Newspeak

structure ObjectId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ClassId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure MixinId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure DeclId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ClassBodyDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ClassDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ObjectLiteralDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ActivationDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ParameterId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure LocalSlotId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Stable source identity of a slot declaration; not a storage address. -/
structure SlotId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- An application owns a distinct cell for each of its slot declarations.
    Reapplying the same mixin must not share or reject those cells. -/
structure PhysicalSlotId where
  application : ClassId
  declaration : SlotId
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Nested-class caches are application-local too, even for repeated mixins. -/
structure NestedCacheId where
  application : ClassId
  declaration : ClassDeclId
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure MethodId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ActivationId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ClosureId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure MirrorId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure ActorId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure PromiseId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure FarRefId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure EventId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure VMId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure PauseTokenId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure CodeImageId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure FreshFrameId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure SiteId where
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Selector where
  spelling : String
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The tagged union of Newspeak object identities.  Tags prevent confusing a
    runtime class object with one of its instances while preserving the rule
    that classes, mixins, activations, closures, mirrors, and actors are all
    Newspeak objects. -/
inductive ObjRef where
  | ordinaryObject (id : ObjectId)
  | classObject (id : ClassId)
  | mixinObject (id : MixinId)
  | activationObject (id : ActivationId)
  | closureObject (id : ClosureId)
  | mirrorObject (id : MirrorId)
  | actorObject (id : ActorId)
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

end Newspeak
