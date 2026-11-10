import Newspeak.ImplicitReceiver
import Newspeak.PrologLexicalBindingCorrespondence

/-! # Correspondence for application indices and implicit receivers -/

namespace Newspeak
namespace PrologBridge

inductive PrologApplicationIndicesFrom (p : Program) (heap : Heap)
    (target : ClassDeclId) : Nat → List ClassId → List Nat → Prop where
  | empty {position : Nat} :
      PrologApplicationIndicesFrom p heap target position [] []
  | top {position : Nat} {rest : List ClassId} {indices : List Nat} :
      PrologApplicationIndicesFrom p heap target (position + 1) rest indices →
      PrologApplicationIndicesFrom p heap target position (p.top :: rest) indices
  | hit {position : Nat} {classId : ClassId} {rest : List ClassId}
      {indices : List Nat} :
      classId ≠ p.top →
      p.namedClassDeclaration? heap classId = some target →
      PrologApplicationIndicesFrom p heap target (position + 1) rest indices →
      PrologApplicationIndicesFrom p heap target position (classId :: rest)
        (position :: indices)
  | different {position : Nat} {classId : ClassId} {rest : List ClassId}
      {other : ClassDeclId} {indices : List Nat} :
      classId ≠ p.top →
      p.namedClassDeclaration? heap classId = some other →
      other ≠ target →
      PrologApplicationIndicesFrom p heap target (position + 1) rest indices →
      PrologApplicationIndicesFrom p heap target position (classId :: rest)
        indices
  | absent {position : Nat} {classId : ClassId} {rest : List ClassId}
      {indices : List Nat} :
      classId ≠ p.top →
      p.namedClassDeclaration? heap classId = none →
      PrologApplicationIndicesFrom p heap target (position + 1) rest indices →
      PrologApplicationIndicesFrom p heap target position (classId :: rest)
        indices

theorem prologApplicationIndicesFrom_sound {p : Program} {heap : Heap}
    {target : ClassDeclId} {position : Nat} {chain : List ClassId}
    {indices : List Nat}
    (derivation :
      PrologApplicationIndicesFrom p heap target position chain indices) :
    p.applicationIndicesFrom heap target position chain = indices := by
  induction derivation with
  | empty => rfl
  | top _ ih => simp [Program.applicationIndicesFrom, ih]
  | hit notTop named _ ih =>
      simp [Program.applicationIndicesFrom, notTop, named, ih]
  | different notTop named different _ ih =>
      simp [Program.applicationIndicesFrom, notTop, named, different, ih]
  | absent notTop named _ ih =>
      simp [Program.applicationIndicesFrom, notTop, named, ih]

theorem prologApplicationIndicesFrom_computed (p : Program) (heap : Heap)
    (target : ClassDeclId) (position : Nat) (chain : List ClassId) :
    PrologApplicationIndicesFrom p heap target position chain
      (p.applicationIndicesFrom heap target position chain) := by
  induction chain generalizing position with
  | nil => exact .empty
  | cons classId rest ih =>
      by_cases top : classId = p.top
      · subst classId
        simpa [Program.applicationIndicesFrom] using
          PrologApplicationIndicesFrom.top (ih (position := position + 1))
      · cases named : p.namedClassDeclaration? heap classId with
        | none =>
            simpa [Program.applicationIndicesFrom, top, named] using
              PrologApplicationIndicesFrom.absent top named
                (ih (position := position + 1))
        | some declaration =>
            by_cases same : declaration = target
            · subst declaration
              simpa [Program.applicationIndicesFrom, top, named] using
                PrologApplicationIndicesFrom.hit top named
                  (ih (position := position + 1))
            · simpa [Program.applicationIndicesFrom, top, named, same] using
                PrologApplicationIndicesFrom.different top named same
                  (ih (position := position + 1))

theorem prologApplicationIndicesFrom_iff {p : Program} {heap : Heap}
    {target : ClassDeclId} {position : Nat} {chain : List ClassId}
    {indices : List Nat} :
    PrologApplicationIndicesFrom p heap target position chain indices ↔
      p.applicationIndicesFrom heap target position chain = indices := by
  constructor
  · exact prologApplicationIndicesFrom_sound
  · intro equality
    rw [← equality]
    exact prologApplicationIndicesFrom_computed p heap target position chain

inductive PrologApplicationIndices (p : Program) (heap : Heap)
    (receiverClass : ClassId) (target : ClassDeclId) : List Nat → Prop where
  | derive {chain : List ClassId} {indices : List Nat} :
      PrologClassChain p heap receiverClass chain →
      PrologApplicationIndicesFrom p heap target 0 chain indices →
      PrologApplicationIndices p heap receiverClass target indices

theorem prologApplicationIndices_iff {p : Program} {heap : Heap}
    {receiverClass : ClassId} {target : ClassDeclId} {indices : List Nat} :
    PrologApplicationIndices p heap receiverClass target indices ↔
      p.ApplicationIndices heap receiverClass target indices := by
  constructor
  · intro derivation
    cases derivation with
    | derive chain indices =>
        exact ⟨_, prologClassChain_iff.mp chain,
          prologApplicationIndicesFrom_iff.mp indices⟩
  · rintro ⟨chain, classChain, indices⟩
    exact .derive (prologClassChain_iff.mpr classChain)
      (prologApplicationIndicesFrom_iff.mpr indices)

inductive PrologImplicitReceiver (p : Program) (heap : Heap)
    (receiver : ObjRef) (currentClass : ClassId) (immediate : ClassDeclId)
    (selector : Selector) : ObjRef → Option ClassDeclId → Prop where
  | found {target : ClassDeclId} {depth : Nat} {selected : ObjRef} :
      PrologClassScan p immediate selector (some target) →
      PrologLexicalDepth p target immediate (some depth) →
      PrologEnclosingReceiver p heap receiver currentClass depth selected →
      PrologImplicitReceiver p heap receiver currentClass immediate selector
        selected (some target)
  | absent :
      PrologClassScan p immediate selector none →
      PrologImplicitReceiver p heap receiver currentClass immediate selector
        receiver none

theorem prologImplicitReceiver_iff {p : Program} {heap : Heap}
    {receiver selected : ObjRef} {currentClass : ClassId}
    {immediate : ClassDeclId} {selector : Selector}
    {target : Option ClassDeclId} :
    PrologImplicitReceiver p heap receiver currentClass immediate selector
      selected target ↔
    p.ImplicitReceiver heap receiver currentClass immediate selector
      selected target := by
  constructor
  · intro derivation
    cases derivation with
    | found scan depth enclosing =>
        exact .found (prologClassScan_iff.mp scan)
          (prologLexicalDepth_iff.mp depth)
          (prologEnclosingReceiver_iff.mp enclosing)
    | absent scan => exact .absent (prologClassScan_iff.mp scan)
  · intro derivation
    cases derivation with
    | found scan depth enclosing =>
        exact .found (prologClassScan_iff.mpr scan)
          (prologLexicalDepth_iff.mpr depth)
          (prologEnclosingReceiver_iff.mpr enclosing)
    | absent scan => exact .absent (prologClassScan_iff.mpr scan)

end PrologBridge
end Newspeak
