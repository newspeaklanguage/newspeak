import Newspeak.Heap

namespace Newspeak
namespace Program

/-- A finite superclass chain beginning at `c` and ending in `Top`.
    It is the direct Lean counterpart of Equation (5.1). -/
inductive ClassChain (p : Program) (h : Heap) : ClassId → List ClassId → Prop where
  | top : ClassChain p h p.top [p.top]
  | step {c parent : ClassId} {tail : List ClassId} :
      c ≠ p.top →
      p.superclass? h c = some parent →
      ClassChain p h parent tail →
      ClassChain p h c (c :: tail)

def ChainsEndAtTop (p : Program) (h : Heap) : Prop :=
  ∀ c, p.IsLiveClass h c → ∃ chain, p.ClassChain h c chain

/-- The structural portion of program well-formedness needed by lookup. -/
structure LookupWellFormed (p : Program) (h : Heap) : Prop where
  topHasNoClassRecord : h.classes p.top = none
  objectIsLive : p.IsLiveClass h p.object
  classHasMixin : ∀ c cd, h.classes c = some cd → ∃ md, p.mixins cd.mixin = some md
  superclassIsLive : ∀ c parent,
    p.superclass? h c = some parent → p.IsLiveClass h parent
  chainsEndAtTop : p.ChainsEndAtTop h

theorem ClassChain.head_eq {p : Program} {h : Heap} {c : ClassId}
    {chain : List ClassId} (hc : p.ClassChain h c chain) :
    chain.head? = some c := by
  cases hc <;> rfl

theorem ClassChain.last_eq_top {p : Program} {h : Heap} {c : ClassId}
    {chain : List ClassId} (hc : p.ClassChain h c chain) :
    chain.getLast? = some p.top := by
  induction hc with
  | top => rfl
  | step _ _ htail ih =>
      cases htail with
      | top => simp
      | step => simpa using ih

theorem ClassChain.unique {p : Program} {h : Heap} {c : ClassId}
    {xs ys : List ClassId} (hx : p.ClassChain h c xs)
    (hy : p.ClassChain h c ys) : xs = ys := by
  induction hx generalizing ys with
  | top =>
      cases hy with
      | top => rfl
      | step hne _ _ => exact (hne rfl).elim
  | @step c parent tail hne hparent htail ih =>
      cases hy with
      | top => exact (hne rfl).elim
      | @step _ parent' tail' _ hparent' htail' =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          have ht : tail = tail' := ih htail'
          rw [ht]

end Program
end Newspeak
