namespace Newspeak

structure ObjectId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ClassId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure MixinId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure DeclId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ClassBodyDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ClassDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ObjectLiteralDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ActivationDeclId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ParameterId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure LocalSlotId where
  index : Nat
deriving Repr, DecidableEq, BEq

/-- Stable physical identity of an instance slot.  Source names are not used
    at run time, so overriding declarations cannot alias storage. -/
structure SlotId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure MethodId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ActivationId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ClosureId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure MirrorId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure ActorId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure PromiseId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure FarRefId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure EventId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure VMId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure PauseTokenId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure CodeImageId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure FreshFrameId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure SiteId where
  index : Nat
deriving Repr, DecidableEq, BEq

structure Selector where
  spelling : String
deriving Repr, DecidableEq, BEq

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
deriving Repr, DecidableEq, BEq

end Newspeak
