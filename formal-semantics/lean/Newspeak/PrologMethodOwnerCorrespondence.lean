import Newspeak.ReflectionQueries

/-! # Prolog correspondence for reflective method ownership -/

namespace Newspeak
namespace PrologBridge

inductive PrologFindMethodInMixin (mixin : MixinDef) (method : MethodId) :
    List Selector → Option MethodDef → Prop where
  | empty : PrologFindMethodInMixin mixin method [] none
  | hit {selector remaining definition} :
      mixin.methods selector = some definition →
      definition.identity = method →
      PrologFindMethodInMixin mixin method (selector :: remaining)
        (some definition)
  | different {selector remaining definition result} :
      mixin.methods selector = some definition →
      definition.identity ≠ method →
      PrologFindMethodInMixin mixin method remaining result →
      PrologFindMethodInMixin mixin method (selector :: remaining) result
  | absent {selector remaining result} :
      mixin.methods selector = none →
      PrologFindMethodInMixin mixin method remaining result →
      PrologFindMethodInMixin mixin method (selector :: remaining) result

theorem prologFindMethodInMixin_iff {mixin : MixinDef} {method : MethodId}
    {selectors : List Selector} {result : Option MethodDef} :
    PrologFindMethodInMixin mixin method selectors result ↔
      Program.findMethodInMixin mixin method selectors = result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | hit lookup identity =>
        simp [Program.findMethodInMixin, lookup, identity]
    | different lookup identity _ ih =>
        simp [Program.findMethodInMixin, lookup, identity, ih]
    | absent lookup _ ih =>
        simp [Program.findMethodInMixin, lookup, ih]
  · intro equality
    induction selectors generalizing result with
    | nil =>
        simp [Program.findMethodInMixin] at equality
        subst result
        exact .empty
    | cons selector remaining ih =>
        cases lookup : mixin.methods selector with
        | none =>
            simp [Program.findMethodInMixin, lookup] at equality
            exact .absent lookup (ih equality)
        | some definition =>
            by_cases identity : definition.identity = method
            · simp [Program.findMethodInMixin, lookup, identity] at equality
              subst result
              exact .hit lookup identity
            · simp [Program.findMethodInMixin, lookup, identity] at equality
              exact .different lookup identity (ih equality)

inductive PrologFindMethodDefinition (program : Program) (method : MethodId) :
    List MixinId → Option (MixinId × MethodDef) → Prop where
  | empty : PrologFindMethodDefinition program method [] none
  | hit {mixinId remaining mixin definition} :
      program.mixins mixinId = some mixin →
      PrologFindMethodInMixin mixin method mixin.methods.domain
        (some definition) →
      PrologFindMethodDefinition program method (mixinId :: remaining)
        (some (mixinId, definition))
  | noMethod {mixinId remaining mixin result} :
      program.mixins mixinId = some mixin →
      PrologFindMethodInMixin mixin method mixin.methods.domain none →
      PrologFindMethodDefinition program method remaining result →
      PrologFindMethodDefinition program method (mixinId :: remaining) result
  | noMixin {mixinId remaining result} :
      program.mixins mixinId = none →
      PrologFindMethodDefinition program method remaining result →
      PrologFindMethodDefinition program method (mixinId :: remaining) result

theorem prologFindMethodDefinition_iff {program : Program} {method : MethodId}
    {mixins : List MixinId} {result : Option (MixinId × MethodDef)} :
    PrologFindMethodDefinition program method mixins result ↔
      program.findMethodDefinition method mixins = result := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | hit mixinLookup methodLookup =>
        simp [Program.findMethodDefinition, mixinLookup,
          prologFindMethodInMixin_iff.mp methodLookup]
    | noMethod mixinLookup methodLookup _ ih =>
        simp [Program.findMethodDefinition, mixinLookup,
          prologFindMethodInMixin_iff.mp methodLookup, ih]
    | noMixin mixinLookup _ ih =>
        simp [Program.findMethodDefinition, mixinLookup, ih]
  · intro equality
    induction mixins generalizing result with
    | nil =>
        simp [Program.findMethodDefinition] at equality
        subst result
        exact .empty
    | cons mixinId remaining ih =>
        cases mixinLookup : program.mixins mixinId with
        | none =>
            simp [Program.findMethodDefinition, mixinLookup] at equality
            exact .noMixin mixinLookup (ih equality)
        | some mixin =>
            cases methodLookup : Program.findMethodInMixin mixin method
                mixin.methods.domain with
            | none =>
                simp [Program.findMethodDefinition, mixinLookup,
                  methodLookup] at equality
                exact .noMethod mixinLookup
                  (prologFindMethodInMixin_iff.mpr methodLookup) (ih equality)
            | some definition =>
                simp [Program.findMethodDefinition, mixinLookup,
                  methodLookup] at equality
                subst result
                exact .hit mixinLookup
                  (prologFindMethodInMixin_iff.mpr methodLookup)

inductive PrologMethodOwner (program : Program) (method : MethodId) :
    MixinId → Prop where
  | owner {mixin definition} :
      PrologFindMethodDefinition program method program.mixins.domain
        (some (mixin, definition)) →
      PrologMethodOwner program method mixin

theorem prologMethodOwner_iff {program : Program} {method : MethodId}
    {mixin : MixinId} :
    PrologMethodOwner program method mixin ↔
      program.methodOwner? method = some mixin := by
  constructor
  · rintro ⟨found⟩
    simp [Program.methodOwner?, prologFindMethodDefinition_iff.mp found]
  · intro equality
    unfold Program.methodOwner? at equality
    cases found : program.findMethodDefinition method program.mixins.domain with
    | none => simp [found] at equality
    | some pair =>
        rcases pair with ⟨owner, definition⟩
        simp [found] at equality
        subst owner
        exact .owner (prologFindMethodDefinition_iff.mpr found)

inductive PrologMethodFormals (program : Program) (method : MethodId) :
    List ParameterId → Prop where
  | formals {mixin definition} :
      PrologFindMethodDefinition program method program.mixins.domain
        (some (mixin, definition)) →
      PrologMethodFormals program method definition.parameters

theorem prologMethodFormals_iff {program : Program} {method : MethodId}
    {formals : List ParameterId} :
    PrologMethodFormals program method formals ↔
      program.methodFormals? method = some formals := by
  constructor
  · rintro ⟨found⟩
    simp [Program.methodFormals?, prologFindMethodDefinition_iff.mp found]
  · intro equality
    unfold Program.methodFormals? at equality
    cases found : program.findMethodDefinition method program.mixins.domain with
    | none => simp [found] at equality
    | some pair =>
        rcases pair with ⟨mixin, definition⟩
        simp [found] at equality
        subst formals
        exact .formals (prologFindMethodDefinition_iff.mpr found)

end PrologBridge
end Newspeak
