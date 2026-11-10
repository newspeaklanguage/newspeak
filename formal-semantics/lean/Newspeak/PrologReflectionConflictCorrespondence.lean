import Newspeak.ReflectionCommands

/-! # Prolog correspondence for reflection write-location overlap -/

namespace Newspeak
namespace PrologBridge

inductive PrologReflectionLocationsOverlap :
    ReflectionWriteLocation → ReflectionWriteLocation → Prop where
  | same (location : ReflectionWriteLocation) :
      PrologReflectionLocationsOverlap location location
  | recordField (activation : ActivationId) (field : ActivationFieldLocation) :
      PrologReflectionLocationsOverlap (.activationRecord activation)
        (.activationField activation field)
  | fieldRecord (activation : ActivationId) (field : ActivationFieldLocation) :
      PrologReflectionLocationsOverlap (.activationField activation field)
        (.activationRecord activation)
  | dictionarySelector (mixin : MixinId) (selector : Selector) :
      PrologReflectionLocationsOverlap (.methodDictionary mixin)
        (.selector mixin selector)
  | selectorDictionary (mixin : MixinId) (selector : Selector) :
      PrologReflectionLocationsOverlap (.selector mixin selector)
        (.methodDictionary mixin)
  | graphRecord (activation : ActivationId) :
      PrologReflectionLocationsOverlap .activationGraph
        (.activationRecord activation)
  | recordGraph (activation : ActivationId) :
      PrologReflectionLocationsOverlap (.activationRecord activation)
        .activationGraph
  | graphField (activation : ActivationId) (field : ActivationFieldLocation) :
      PrologReflectionLocationsOverlap .activationGraph
        (.activationField activation field)
  | fieldGraph (activation : ActivationId) (field : ActivationFieldLocation) :
      PrologReflectionLocationsOverlap (.activationField activation field)
        .activationGraph

theorem prologReflectionLocationsOverlap_iff {left right} :
    PrologReflectionLocationsOverlap left right ↔
      ReflectionLocationsOverlap left right := by
  constructor <;> intro derivation <;> cases derivation
  all_goals constructor

structure PrologReflectionCommandWrites (command : ReflectionCommand)
    (locations : List ReflectionWriteLocation) : Prop where
  equality : command.writes = locations

theorem prologReflectionCommandWrites_iff {command : ReflectionCommand}
    {locations : List ReflectionWriteLocation} :
    PrologReflectionCommandWrites command locations ↔
      command.writes = locations := by
  constructor
  · exact fun relation => relation.equality
  · exact PrologReflectionCommandWrites.mk

def ReflectionCommandConflict (first second : ReflectionCommand) : Prop :=
  ∃ left, left ∈ first.writes ∧ ∃ right, right ∈ second.writes ∧
    ReflectionLocationsOverlap left right

def ReflectionConflictAt (transaction : List ReflectionCommand)
    (firstIndex secondIndex : Nat) : Prop :=
  firstIndex ≠ 0 ∧ secondIndex ≠ 0 ∧ firstIndex < secondIndex ∧
    ∃ first second,
      transaction[firstIndex.pred]? = some first ∧
      transaction[secondIndex.pred]? = some second ∧
      ReflectionCommandConflict first second

inductive PrologNaturalStrictLess : Nat → Nat → Prop where
  | zero (right : Nat) : PrologNaturalStrictLess 0 (right + 1)
  | successor {left right : Nat} :
      PrologNaturalStrictLess left right →
      PrologNaturalStrictLess (left + 1) (right + 1)

inductive PrologListNthOneBased {Element : Type} :
    List Element → Nat → Element → Prop where
  | head {element remaining} :
      PrologListNthOneBased (element :: remaining) 1 element
  | tail {element remaining index result} :
      PrologListNthOneBased remaining (index + 1) result →
      PrologListNthOneBased (element :: remaining) (index + 2) result

inductive PrologReflectionCommandConflict
    (first second : ReflectionCommand) : Prop where
  | conflict {left right} :
      PrologReflectionCommandWrites first first.writes →
      left ∈ first.writes →
      PrologReflectionCommandWrites second second.writes →
      right ∈ second.writes →
      PrologReflectionLocationsOverlap left right →
      PrologReflectionCommandConflict first second

theorem prologReflectionCommandConflict_iff {first second} :
    PrologReflectionCommandConflict first second ↔
      ReflectionCommandConflict first second := by
  constructor
  · rintro ⟨_, leftMember, _, rightMember, overlap⟩
    exact ⟨_, leftMember, _, rightMember,
      prologReflectionLocationsOverlap_iff.mp overlap⟩
  · rintro ⟨left, leftMember, right, rightMember, overlap⟩
    exact .conflict ⟨rfl⟩ leftMember ⟨rfl⟩ rightMember
      (prologReflectionLocationsOverlap_iff.mpr overlap)

inductive PrologReflectionConflictAt (transaction : List ReflectionCommand) :
    Nat → Nat → Prop where
  | conflict {firstIndex secondIndex first second} :
      firstIndex ≠ 0 → secondIndex ≠ 0 → firstIndex < secondIndex →
      transaction[firstIndex.pred]? = some first →
      transaction[secondIndex.pred]? = some second →
      PrologReflectionCommandConflict first second →
      PrologReflectionConflictAt transaction firstIndex secondIndex

theorem prologReflectionConflictAt_iff {transaction firstIndex secondIndex} :
    PrologReflectionConflictAt transaction firstIndex secondIndex ↔
      ReflectionConflictAt transaction firstIndex secondIndex := by
  constructor
  · rintro ⟨firstPositive, secondPositive, less, firstLookup,
      secondLookup, conflict⟩
    exact ⟨firstPositive, secondPositive, less, _, _, firstLookup,
      secondLookup, prologReflectionCommandConflict_iff.mp conflict⟩
  · rintro ⟨firstPositive, secondPositive, less, first, second,
      firstLookup, secondLookup, conflict⟩
    exact .conflict firstPositive secondPositive less firstLookup secondLookup
      (prologReflectionCommandConflict_iff.mpr conflict)

inductive PrologReflectionTransactionNonconflicting
    (transaction : List ReflectionCommand) : Prop where
  | witness : ReflectionTransactionNonconflicting transaction →
      PrologReflectionTransactionNonconflicting transaction

end PrologBridge
end Newspeak
