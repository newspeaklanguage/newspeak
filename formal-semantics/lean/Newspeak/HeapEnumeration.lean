import Newspeak.TopLevel

namespace Newspeak
namespace Heap

/-- Every object identity currently represented by a runtime heap record.
    `deduplicated` is representation-independent insurance; each individual
    finite store already has a duplicate-free domain, and the `ObjRef` tags
    make the seven mapped domains disjoint. -/
def liveObjectReferences (h : Heap) : List ObjRef :=
  FiniteStore.deduplicated
  ((h.objects.domain.map ObjRef.ordinaryObject) ++
   (h.classes.domain.map ObjRef.classObject) ++
   (h.mixinObjects.domain.map ObjRef.mixinObject) ++
   (h.activations.domain.map ObjRef.activationObject) ++
   (h.closures.domain.map ObjRef.closureObject) ++
   (h.mirrors.domain.map ObjRef.mirrorObject) ++
   (h.actors.domain.map ObjRef.actorObject))

@[simp] theorem mem_liveObjectReferences_iff (h : Heap) (object : ObjRef) :
    object ∈ h.liveObjectReferences ↔ h.IsLiveObject object := by
  cases object with
  | ordinaryObject id =>
      cases result : h.objects id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]
  | classObject id =>
      cases result : h.classes id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]
  | mixinObject id =>
      cases result : h.mixinObjects id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]
  | activationObject id =>
      cases result : h.activations id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]
  | closureObject id =>
      cases result : h.closures id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]
  | mirrorObject id =>
      cases result : h.mirrors id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]
  | actorObject id =>
      cases result : h.actors id <;>
        simp [liveObjectReferences, FiniteStore.mem_deduplicated,
          FiniteStore.mem_domain_iff, IsLiveObject, classOf, result]

theorem liveObjectReferences_nodup (h : Heap) :
    h.liveObjectReferences.Nodup := by
  exact FiniteStore.deduplicated_nodup _

/-- Executable semantics of `allInstancesOf:`.  This includes every Newspeak
    object category, not merely ordinary slot-bearing instances. -/
def allInstancesOf (h : Heap) (classId : ClassId) : List ObjRef :=
  h.liveObjectReferences.filter fun object =>
    decide (h.classOf object = some classId)

@[simp] theorem mem_allInstancesOf_iff (h : Heap) (classId : ClassId)
    (object : ObjRef) :
    object ∈ h.allInstancesOf classId ↔
      h.classOf object = some classId := by
  constructor
  · intro member
    have filtered := (List.mem_filter.mp member).2
    exact of_decide_eq_true filtered
  · intro classOf
    apply List.mem_filter.mpr
    constructor
    · exact (h.mem_liveObjectReferences_iff object).mpr ⟨classId, classOf⟩
    · exact decide_eq_true classOf

theorem allInstancesOf_nodup (h : Heap) (classId : ClassId) :
    (h.allInstancesOf classId).Nodup :=
  List.Pairwise.filter _ h.liveObjectReferences_nodup

/-- Every runtime class record produced by applying the given mixin.  This
    includes metaclasses when their own runtime record applies that mixin. -/
def allApplicationsOf (h : Heap) (mixinId : MixinId) : List ClassId :=
  h.classes.domain.filter fun classId =>
    match h.classes classId with
    | some classDef => decide (classDef.mixin = mixinId)
    | none => false

@[simp] theorem mem_allApplicationsOf_iff (h : Heap) (mixinId : MixinId)
    (classId : ClassId) :
    classId ∈ h.allApplicationsOf mixinId ↔
      ∃ classDef, h.classes classId = some classDef ∧
        classDef.mixin = mixinId := by
  constructor
  · intro member
    rcases List.mem_filter.mp member with ⟨inDomain, selected⟩
    rcases h.classes.exists_value_of_mem_domain inDomain with
      ⟨classDef, lookup⟩
    refine ⟨classDef, lookup, ?_⟩
    have selected' : decide (classDef.mixin = mixinId) = true := by
      simpa [lookup] using selected
    exact of_decide_eq_true selected'
  · rintro ⟨classDef, lookup, mixin⟩
    apply List.mem_filter.mpr
    constructor
    · exact h.classes.mem_domain_of_lookup_eq_some lookup
    · simp [lookup, mixin]

theorem allApplicationsOf_nodup (h : Heap) (mixinId : MixinId) :
    (h.allApplicationsOf mixinId).Nodup :=
  List.Pairwise.filter _ h.classes.domainNodup

end Heap
end Newspeak
