import Newspeak.ReflectionStackEditing

/-! # Prolog correspondence for pure debugger stack editing -/

namespace Newspeak
namespace PrologBridge

inductive PrologPromoteFrame :
    FrameTemplate → ControlTerm → FrameTemplate → Prop where
  | suspended {key record frames value} :
      PrologPromoteFrame ⟨key, record, .suspendedControl frames⟩ value
        ⟨key, record, .activeControl frames value⟩

theorem prologPromoteFrame_iff {frame promoted : FrameTemplate}
    {value : ControlTerm} :
    PrologPromoteFrame frame value promoted ↔
      promoteFrame frame value = some promoted := by
  constructor
  · rintro ⟨⟩
    rfl
  · cases frame with
    | mk key record control =>
        cases control <;> simp [promoteFrame]
        intro equality
        subst promoted
        exact .suspended

inductive PrologDemoteFrame : FrameTemplate → FrameTemplate → Prop where
  | active {key record frames term} :
      PrologDemoteFrame ⟨key, record, .activeControl frames term⟩
        ⟨key, record, .suspendedControl frames⟩

theorem prologDemoteFrame_iff {frame demoted : FrameTemplate} :
    PrologDemoteFrame frame demoted ↔ demoteFrame frame = some demoted := by
  constructor
  · rintro ⟨⟩
    rfl
  · cases frame with
    | mk key record control =>
        cases control <;> simp [demoteFrame]
        intro equality
        subst demoted
        exact .active

inductive PrologPromoteTopFrame :
    StackTemplate → ControlTerm → StackTemplate → Prop where
  | single {frame promoted value} :
      PrologPromoteFrame frame value promoted →
      PrologPromoteTopFrame [frame] value [promoted]
  | step {frame next remaining value promoted} :
      PrologPromoteTopFrame (next :: remaining) value promoted →
      PrologPromoteTopFrame (frame :: next :: remaining) value
        (frame :: promoted)

theorem prologPromoteTopFrame_iff {stack promoted : StackTemplate}
    {value : ControlTerm} :
    PrologPromoteTopFrame stack value promoted ↔
      promoteTopFrame stack value = some promoted := by
  constructor
  · intro derivation
    induction derivation with
    | single frameProof =>
        simp [promoteTopFrame, prologPromoteFrame_iff.mp frameProof]
    | step _ ih => simp [promoteTopFrame, ih]
  · intro result
    induction stack generalizing promoted with
    | nil => simp [promoteTopFrame] at result
    | cons frame remaining ih =>
        cases remaining with
        | nil =>
            simp [promoteTopFrame] at result
            rcases result with ⟨candidate, frameResult, rfl⟩
            exact .single (prologPromoteFrame_iff.mpr frameResult)
        | cons next later =>
            simp only [promoteTopFrame] at result
            cases tailResult : promoteTopFrame (next :: later) value with
            | none => simp [tailResult] at result
            | some candidate =>
                simp [tailResult] at result
                subst promoted
                exact .step (ih tailResult)

inductive PrologRemoveTopFrame : StackTemplate → StackTemplate → Prop where
  | single {frame} : PrologRemoveTopFrame [frame] []
  | step {frame next remaining shortened} :
      PrologRemoveTopFrame (next :: remaining) shortened →
      PrologRemoveTopFrame (frame :: next :: remaining) (frame :: shortened)

theorem prologRemoveTopFrame_iff {stack shortened : StackTemplate} :
    PrologRemoveTopFrame stack shortened ↔
      removeTopFrame stack = some shortened := by
  constructor
  · intro derivation
    induction derivation with
    | single => rfl
    | step _ ih => simp [removeTopFrame, ih]
  · intro result
    induction stack generalizing shortened with
    | nil => simp [removeTopFrame] at result
    | cons frame remaining ih =>
        cases remaining with
        | nil =>
            simp [removeTopFrame] at result
            subst shortened
            exact .single
        | cons next later =>
            simp only [removeTopFrame] at result
            cases tailResult : removeTopFrame (next :: later) with
            | none => simp [tailResult] at result
            | some candidate =>
                simp [tailResult] at result
                subst shortened
                exact .step (ih tailResult)

inductive PrologPopStackFrames :
    StackTemplate → Nat → ControlTerm → StackTemplate → Prop where
  | zero {stack value result} :
      PrologPromoteTopFrame stack value result →
      PrologPopStackFrames stack 0 value result
  | successor {stack count value shortened result} :
      PrologRemoveTopFrame stack shortened →
      PrologPopStackFrames shortened count value result →
      PrologPopStackFrames stack (count + 1) value result

theorem prologPopStackFrames_iff {stack result : StackTemplate}
    {count : Nat} {value : ControlTerm} :
    PrologPopStackFrames stack count value result ↔
      popStackFrames stack count value = some result := by
  constructor
  · intro derivation
    induction derivation with
    | zero promoted => exact prologPromoteTopFrame_iff.mp promoted
    | successor removed _ ih =>
        simp [popStackFrames, prologRemoveTopFrame_iff.mp removed, ih]
  · intro equality
    induction count generalizing stack with
    | zero => exact .zero (prologPromoteTopFrame_iff.mpr equality)
    | succ count ih =>
        simp only [popStackFrames] at equality
        cases removed : removeTopFrame stack with
        | none => simp [removed] at equality
        | some shortened =>
            simp [removed] at equality
            exact .successor (prologRemoveTopFrame_iff.mpr removed)
              (ih equality)

inductive PrologDemoteTopFrame : StackTemplate → StackTemplate → Prop where
  | single {frame demoted} :
      PrologDemoteFrame frame demoted →
      PrologDemoteTopFrame [frame] [demoted]
  | step {frame next remaining demoted} :
      PrologDemoteTopFrame (next :: remaining) demoted →
      PrologDemoteTopFrame (frame :: next :: remaining) (frame :: demoted)

theorem prologDemoteTopFrame_iff {stack demoted : StackTemplate} :
    PrologDemoteTopFrame stack demoted ↔
      demoteTopFrame stack = some demoted := by
  constructor
  · intro derivation
    induction derivation with
    | single frameProof =>
        simp [demoteTopFrame, prologDemoteFrame_iff.mp frameProof]
    | step _ ih => simp [demoteTopFrame, ih]
  · intro result
    induction stack generalizing demoted with
    | nil => simp [demoteTopFrame] at result
    | cons frame remaining ih =>
        cases remaining with
        | nil =>
            simp [demoteTopFrame] at result
            rcases result with ⟨candidate, frameResult, rfl⟩
            exact .single (prologDemoteFrame_iff.mpr frameResult)
        | cons next later =>
            simp only [demoteTopFrame] at result
            cases tailResult : demoteTopFrame (next :: later) with
            | none => simp [tailResult] at result
            | some candidate =>
                simp [tailResult] at result
                subst demoted
                exact .step (ih tailResult)

inductive PrologPushStackFrame :
    StackTemplate → FrameTemplate → StackTemplate → Prop where
  | active {stack key record frames term demoted} :
      PrologDemoteTopFrame stack demoted →
      PrologPushStackFrame stack
        ⟨key, record, .activeControl frames term⟩
        (demoted ++ [⟨key, record, .activeControl frames term⟩])

theorem prologPushStackFrame_iff {stack result : StackTemplate}
    {pushed : FrameTemplate} :
    PrologPushStackFrame stack pushed result ↔
      pushStackFrame stack pushed = some result := by
  constructor
  · rintro ⟨demoted⟩
    simp [pushStackFrame, prologDemoteTopFrame_iff.mp demoted]
  · cases pushed with
    | mk key record control =>
        cases control with
        | suspendedControl frames => simp [pushStackFrame]
        | activeControl frames term =>
            intro equality
            simp only [pushStackFrame] at equality
            cases demotedResult : demoteTopFrame stack with
            | none => simp [demotedResult] at equality
            | some demoted =>
                simp [demotedResult] at equality
                subst result
                exact .active (prologDemoteTopFrame_iff.mpr demotedResult)

inductive PrologStackTemplateRecordLocations :
    StackTemplate → List ReflectionWriteLocation → Prop where
  | empty : PrologStackTemplateRecordLocations [] []
  | retained {activation record control remaining locations} :
      PrologStackTemplateRecordLocations remaining locations →
      PrologStackTemplateRecordLocations
        (⟨.retain activation, record, control⟩ :: remaining)
        (.activationRecord activation :: locations)
  | fresh {key record control remaining locations} :
      PrologStackTemplateRecordLocations remaining locations →
      PrologStackTemplateRecordLocations
        (⟨.freshFrame key, record, control⟩ :: remaining) locations

theorem prologStackTemplateRecordLocations_iff
    {stack : StackTemplate} {locations : List ReflectionWriteLocation} :
    PrologStackTemplateRecordLocations stack locations ↔
      stackTemplateRecordLocations stack = locations := by
  constructor
  · intro derivation
    induction derivation with
    | empty => rfl
    | retained _ ih =>
        unfold stackTemplateRecordLocations at ih ⊢
        simp [ih]
    | fresh _ ih =>
        unfold stackTemplateRecordLocations at ih ⊢
        simp [ih]
  · intro equality
    induction stack generalizing locations with
    | nil =>
        simp [stackTemplateRecordLocations] at equality
        subst locations
        exact .empty
    | cons frame remaining ih =>
        cases frame with
        | mk key record control =>
            cases key with
            | retain activation =>
                simp [stackTemplateRecordLocations] at equality
                subst locations
                exact .retained (ih rfl)
            | freshFrame key =>
                simp [stackTemplateRecordLocations] at equality
                exact .fresh (ih equality)

end PrologBridge
end Newspeak
