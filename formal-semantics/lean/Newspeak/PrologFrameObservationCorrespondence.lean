import Newspeak.ReflectionFrameObservation

/-! # Prolog correspondence for per-frame debugger observations -/

namespace Newspeak
namespace PrologBridge

inductive PrologFrameCurrentTerm : FrameControl → DebuggerCurrentTerm → Prop where
  | active {frames term} :
      PrologFrameCurrentTerm (.activeControl frames term) (.active term)
  | suspended {frames} :
      PrologFrameCurrentTerm (.suspendedControl frames) .awaitResult

theorem prologFrameCurrentTerm_iff {control : FrameControl}
    {term : DebuggerCurrentTerm} :
    PrologFrameCurrentTerm control term ↔ control.currentTerm = term := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases control with
    | activeControl frames activeTerm =>
        simp [FrameControl.currentTerm] at equality
        subst term
        exact .active
    | suspendedControl frames =>
        simp [FrameControl.currentTerm] at equality
        subst term
        exact .suspended

/-- Proof-carrying Horn application of the retained active-term control map. -/
inductive PrologControlSiteApplication (controlMap : FrameControlMap)
    (frames : EvalStack) (term : ControlTerm) (location : ControlLocation) : Prop where
  | witness : controlMap.site frames term = location →
      PrologControlSiteApplication controlMap frames term location

/-- Proof-carrying Horn application of the retained resumption control map. -/
inductive PrologControlResumeApplication (controlMap : FrameControlMap)
    (frames : EvalStack) (location : ControlLocation) : Prop where
  | witness : controlMap.resumeSite frames = location →
      PrologControlResumeApplication controlMap frames location

inductive PrologFrameControlLocation (controlMap : FrameControlMap) :
    FrameControl → ControlLocation → Prop where
  | active {frames term location} :
      PrologControlSiteApplication controlMap frames term location →
      PrologFrameControlLocation controlMap (.activeControl frames term) location
  | suspended {frames location} :
      PrologControlResumeApplication controlMap frames location →
      PrologFrameControlLocation controlMap (.suspendedControl frames) location

theorem prologFrameControlLocation_iff {controlMap : FrameControlMap}
    {control : FrameControl} {location : ControlLocation} :
    PrologFrameControlLocation controlMap control location ↔
      control.controlLocation controlMap = location := by
  constructor
  · intro derivation
    cases derivation with
    | active application =>
        cases application with
        | witness equality => exact equality
    | suspended application =>
        cases application with
        | witness equality => exact equality
  · intro equality
    cases control with
    | activeControl frames term => exact .active (.witness equality)
    | suspendedControl frames => exact .suspended (.witness equality)

end PrologBridge
end Newspeak
