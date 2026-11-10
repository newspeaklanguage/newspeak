import Newspeak.Enclosing

namespace Newspeak
namespace Program

/-- Equation (6.9): the receiver and declaration selected by the derived
    ECOOP-style presentation of implicit sends. -/
inductive ImplicitReceiver (p : Program) (heap : Heap)
    (receiver : ObjRef) (currentClass : ClassId) (immediate : ClassDeclId)
    (selector : Selector) : ObjRef → Option ClassDeclId → Prop where
  | found {target : ClassDeclId} {depth : Nat} {selected : ObjRef} :
      p.ClassScan immediate selector (some target) →
      p.LexicalDepth target immediate (some depth) →
      p.EnclosingReceiver heap receiver currentClass depth selected →
      ImplicitReceiver p heap receiver currentClass immediate selector
        selected (some target)
  | absent :
      p.ClassScan immediate selector none →
      ImplicitReceiver p heap receiver currentClass immediate selector
        receiver none

end Program
end Newspeak
