import Newspeak.ReflectionCommands

namespace Newspeak

/-- A debugger frame always has a current-term observation.  Suspended frames
    use the explicit internal waiting term rather than extending executable
    `ControlTerm` with a state the evaluator can never execute. -/
inductive DebuggerCurrentTerm where
  | active (term : ControlTerm)
  | awaitResult
deriving Repr

/-- Control maps retained with compiled/evaluated frame material.  Source
    evaluators normally return `sourcePoint`; compiled implementations may
    return the exact code image and program counter. -/
structure FrameControlMap where
  site : EvalStack → ControlTerm → ControlLocation
  resumeSite : EvalStack → ControlLocation

def FrameControl.currentTerm : FrameControl → DebuggerCurrentTerm
  | .activeControl _ term => .active term
  | .suspendedControl _ => .awaitResult

def FrameControl.controlLocation (controlMap : FrameControlMap) :
    FrameControl → ControlLocation
  | .activeControl frames term => controlMap.site frames term
  | .suspendedControl frames => controlMap.resumeSite frames

end Newspeak
