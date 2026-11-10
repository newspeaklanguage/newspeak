import Newspeak.ReflectionCommands

namespace Newspeak

/-- Promote a suspended template frame to the unique active top frame. -/
def promoteFrame (frame : FrameTemplate) (value : ControlTerm) :
    Option FrameTemplate :=
  match frame.control with
  | .suspendedControl frames =>
      some { frame with control := .activeControl frames value }
  | .activeControl _ _ => none

/-- Demote an active template frame before placing another frame above it. -/
def demoteFrame (frame : FrameTemplate) : Option FrameTemplate :=
  match frame.control with
  | .activeControl frames _ =>
      some { frame with control := .suspendedControl frames }
  | .suspendedControl _ => none

/-- Promote the last (top) frame of a bottom-to-top stack template. -/
def promoteTopFrame : StackTemplate → ControlTerm → Option StackTemplate
  | [], _ => none
  | [frame], value => (promoteFrame frame value).map fun promoted => [promoted]
  | frame :: next :: remaining, value => do
      let promoted ← promoteTopFrame (next :: remaining) value
      some (frame :: promoted)

/-- Remove the last (top) frame of a bottom-to-top stack template. -/
def removeTopFrame : StackTemplate → Option StackTemplate
  | [] => none
  | [_] => some []
  | frame :: next :: remaining => do
      let shortened ← removeTopFrame (next :: remaining)
      some (frame :: shortened)

/-- Equation `pop-stack-frames`.  Repeatedly remove `count` top frames, then
    promote the remaining top with the selected continuation value. -/
def popStackFrames : StackTemplate → Nat → ControlTerm →
    Option StackTemplate
  | stack, 0, value => promoteTopFrame stack value
  | stack, count + 1, value => do
      let shortened ← removeTopFrame stack
      popStackFrames shortened count value

/-- Demote the last (top) frame of a bottom-to-top stack template. -/
def demoteTopFrame : StackTemplate → Option StackTemplate
  | [] => none
  | [frame] => (demoteFrame frame).map fun demoted => [demoted]
  | frame :: next :: remaining => do
      let demoted ← demoteTopFrame (next :: remaining)
      some (frame :: demoted)

/-- Equation `push-stack-frame`.  Only an active prepared frame may become the
    new top; the former top is atomically demoted. -/
def pushStackFrame (stack : StackTemplate) (pushed : FrameTemplate) :
    Option StackTemplate :=
  match pushed.control with
  | .suspendedControl _ => none
  | .activeControl _ _ => do
      let demoted ← demoteTopFrame stack
      some (demoted ++ [pushed])

abbrev FrameTemplateRenaming := List (FrameTemplateKey × FrameTemplateKey)

def lookupFrameTemplateRenaming : FrameTemplateRenaming → FrameTemplateKey →
    Option FrameTemplateKey
  | [], _ => none
  | (source, target) :: remaining, key =>
      if source = key then some target
      else lookupFrameTemplateRenaming remaining key

def renameFrameTemplateKey (mapping : FrameTemplateRenaming)
    (key : FrameTemplateKey) : FrameTemplateKey :=
  (lookupFrameTemplateRenaming mapping key).getD key

def renameOptionalFrameTemplateKey (mapping : FrameTemplateRenaming) :
    Option FrameTemplateKey → Option FrameTemplateKey
  | none => none
  | some key => some (renameFrameTemplateKey mapping key)

def renameTemplateScopeEntries (mapping : FrameTemplateRenaming)
    (source : FiniteStore ActivationDeclId FrameTemplateKey) :
    List ActivationDeclId → FiniteStore ActivationDeclId FrameTemplateKey →
      FiniteStore ActivationDeclId FrameTemplateKey
  | [], result => result
  | declaration :: remaining, result =>
      match source declaration with
      | none => renameTemplateScopeEntries mapping source remaining result
      | some key => renameTemplateScopeEntries mapping source remaining
          (result.install declaration (renameFrameTemplateKey mapping key))

def renameTemplateScopes (mapping : FrameTemplateRenaming)
    (source : FiniteStore ActivationDeclId FrameTemplateKey) :
    FiniteStore ActivationDeclId FrameTemplateKey :=
  renameTemplateScopeEntries mapping source source.domain
    (FiniteStore.empty ActivationDeclId FrameTemplateKey)

def renameActivationRecordTemplate (mapping : FrameTemplateRenaming)
    (record : ActivationRecordTemplate) : ActivationRecordTemplate :=
  { record with
    continuation := renameOptionalFrameTemplateKey mapping record.continuation
    homeMethod := renameOptionalFrameTemplateKey mapping record.homeMethod
    activationScopes := renameTemplateScopes mapping record.activationScopes }

def renameFrameTemplate (mapping : FrameTemplateRenaming)
    (frame : FrameTemplate) : FrameTemplate :=
  { frame with
    key := renameFrameTemplateKey mapping frame.key
    activation := renameActivationRecordTemplate mapping frame.activation }

def freshFrameRenaming : StackTemplate → List FreshFrameId →
    Option FrameTemplateRenaming
  | [], [] => some []
  | frame :: frames, fresh :: freshKeys => do
      let remaining ← freshFrameRenaming frames freshKeys
      some ((frame.key, .freshFrame fresh) :: remaining)
  | _, _ => none

/-- Equation `copy-stack-frame-segment`, using zero-based `start` and an
    explicit `count`.  Only structural activation links are renamed; ordinary
    object values in parameters and locals remain shallow copies. -/
def copyStackFrameSegment (stack : StackTemplate) (start count : Nat)
    (freshKeys : List FreshFrameId) : Option StackTemplate := do
  let segment := (stack.drop start).take count
  if segment.length = count then
    let mapping ← freshFrameRenaming segment freshKeys
    some (segment.map (renameFrameTemplate mapping))
  else none

end Newspeak
