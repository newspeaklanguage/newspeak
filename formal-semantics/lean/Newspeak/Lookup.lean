import Newspeak.WellFormed

namespace Newspeak

structure LookupResult where
  method : MethodDef
  definingClass : ClassId
deriving Repr, DecidableEq, BEq

inductive LookupMode where
  | unrestricted
  | publicOnly
  | protectedAccess
deriving Repr, DecidableEq, BEq

namespace Program

def lookupAtNonTop (p : Program) (h : Heap) (mode : LookupMode)
    (c : ClassId) (s : Selector) : Option (Option LookupResult) :=
  match p.direct h c s with
  | none => none
  | some method =>
      match mode, method.access with
      | .unrestricted, _ => some (some ⟨method, c⟩)
      | .publicOnly, .publicAccess => some (some ⟨method, c⟩)
      | .publicOnly, .protectedAccess => some none
      | .publicOnly, .privateAccess => none
      | .protectedAccess, .publicAccess => some (some ⟨method, c⟩)
      | .protectedAccess, .protectedAccess => some (some ⟨method, c⟩)
      | .protectedAccess, .privateAccess => none

/-- Lookup over an already established finite class chain.  The outer option
    returned by `lookupAtNonTop` distinguishes "keep searching" from the
    protected barrier that terminates public lookup with failure. -/
def lookupOnChain (p : Program) (h : Heap) (mode : LookupMode) (s : Selector) :
    List ClassId → Option LookupResult
  | [] => none
  | c :: tail =>
      if c = p.top then
        none
      else
        match lookupAtNonTop p h mode c s with
        | some result => result
        | none => lookupOnChain p h mode s tail

/-- Relational lookup is intentionally defined through the unique class chain.
    Later files prove that this graph presentation agrees with syntax-directed
    rules corresponding to U-Top/U-Here/U-Super and their access variants. -/
def Lookup (p : Program) (h : Heap) (mode : LookupMode) (s : Selector)
    (start : ClassId) (result : Option LookupResult) : Prop :=
  ∃ chain, p.ClassChain h start chain ∧
    p.lookupOnChain h mode s chain = result

end Program
end Newspeak
