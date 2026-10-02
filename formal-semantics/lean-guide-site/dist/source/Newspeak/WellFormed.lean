import Newspeak.ClassChain

namespace Newspeak
namespace Program

def OptionalClassLive (p : Program) (h : Heap) : Option ClassId → Prop
  | none => True
  | some classId => p.IsLiveClass h classId

/-- Static program coherence shared by elaboration and the dynamic machine.
    Reflection must re-establish this predicate before installing a program. -/
structure WellFormed (p : Program) (h : Heap) : Prop extends LookupWellFormed p h where
  objectIsNotTop : p.object ≠ p.top
  messageMirrorClassIsLive : p.IsLiveClass h p.messageMirrorClass
  activationClassIsLive : p.IsLiveClass h p.activationClass
  closureClassIsLive : p.IsLiveClass h p.closureClass
  atomCanonical : Function.Injective p.atoms
  objectClassesAreLive : ∀ object classId,
    h.classOf object = some classId → p.IsLiveClass h classId
  activationCurrentClassesAreLive : ∀ activationId activation,
    h.activations activationId = some activation →
    p.OptionalClassLive h activation.currentClass
  closureCapturedClassesAreLive : ∀ closureId closure,
    h.closures closureId = some closure →
    p.OptionalClassLive h closure.capturedClass
  directSelectorCoherent : ∀ c selector method,
    p.direct h c selector = some method → method.selector = selector
  directOwnerCoherent : ∀ c classDef mixinDef selector method,
    h.classes c = some classDef →
    p.mixins classDef.mixin = some mixinDef →
    mixinDef.methods selector = some method →
    method.owner = mixinDef.declaration
  declarationMixinCoherent : ∀ declaration mixinId,
    p.declMixin declaration = some mixinId →
    ∃ mixinDef,
      p.mixins mixinId = some mixinDef ∧
      mixinDef.declaration = declaration

theorem WellFormed.chain_exists {p : Program} {h : Heap} (wf : p.WellFormed h)
    {c : ClassId} (live : p.IsLiveClass h c) :
    ∃ chain, p.ClassChain h c chain :=
  wf.chainsEndAtTop c live

theorem WellFormed.class_record_retains_mixin_and_enclosingObject
    {p : Program} {h : Heap} (wf : p.WellFormed h)
    {classId : ClassId} {definition : ClassDef}
    (present : h.classes classId = some definition) :
    ∃ mixinDefinition enclosingObject,
      p.mixins definition.mixin = some mixinDefinition ∧
      definition.enclosingObject = enclosingObject := by
  rcases wf.classHasMixin classId definition present with
    ⟨mixinDefinition, mixinPresent⟩
  exact ⟨mixinDefinition, definition.enclosingObject, mixinPresent, rfl⟩

theorem class_record_retains_origin_declaration
    {h : Heap} {classId : ClassId} {definition : ClassDef}
    (present : h.classes classId = some definition) :
    ∃ declaration,
      (definition.origin = .expression declaration ∨
        definition.origin = .actor declaration) ∧
      h.classes classId = some definition := by
  cases definition.origin with
  | expression declaration => exact ⟨declaration, .inl rfl, present⟩
  | actor declaration => exact ⟨declaration, .inr rfl, present⟩

theorem mixin_lookup_retains_inducing_declaration
    {p : Program} {mixinId : MixinId} {definition : MixinDef}
    (present : p.mixins mixinId = some definition) :
    ∃ declaration,
      definition.declaration = declaration ∧
      p.mixins mixinId = some definition :=
  ⟨definition.declaration, rfl, present⟩

end Program
end Newspeak
