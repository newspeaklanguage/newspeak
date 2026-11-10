import Newspeak.MethodInvocation
import Newspeak.SynthesizedDeclarations

/-! # Correspondence for supporting sequential equations -/

namespace Newspeak
namespace PrologBridge

inductive PrologCalleeContinuation (heap : Heap) (current : ActivationId) :
    EvalStack → Option ActivationId → Prop where
  | nonTail {frames : EvalStack} {top : EvalFrame} :
      PrologCalleeContinuation heap current (.push frames top) (some current)
  | tail {activation : ActivationDef} :
      heap.activations current = some activation →
      PrologCalleeContinuation heap current .empty activation.continuation

theorem prologCalleeContinuation_iff {heap : Heap} {current : ActivationId}
    {frames : EvalStack} {result : Option ActivationId} :
    PrologCalleeContinuation heap current frames result ↔
      Program.CalleeContinuation heap current frames result := by
  constructor <;> intro derivation <;> cases derivation with
  | nonTail => exact .nonTail
  | tail present => exact .tail present

inductive PrologPrimaryFactoryBody (selector : Selector)
    (parameters : List ParameterId) : List Statement → Prop where
  | body : PrologPrimaryFactoryBody selector parameters
      [.return (.newInstanceCurrent selector parameters)]

theorem prologPrimaryFactoryBody_iff {selector : Selector}
    {parameters : List ParameterId} {body : List Statement} :
    PrologPrimaryFactoryBody selector parameters body ↔
      primaryFactoryBody selector parameters = body := by
  constructor
  · intro derivation; cases derivation; rfl
  · intro equality; rw [← equality]; exact .body

end PrologBridge
end Newspeak
