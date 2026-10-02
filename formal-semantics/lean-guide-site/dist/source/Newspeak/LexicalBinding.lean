import Newspeak.LookupRules

namespace Newspeak
namespace Program

/-- Innermost-first binding over the elaborator's complete static scope chain,
    corresponding to Equation (6.7). -/
def bindIn (p : Program) (selector : Selector) :
    List ScopeDecl → Option ScopeDecl
  | [] => none
  | decl :: rest =>
      if p.declares decl selector then
        some decl
      else
        p.bindIn selector rest

def bind (p : Program) (site : SiteId) (selector : Selector) :
    Option ScopeDecl :=
  p.bindIn selector (p.scopeChain site)

def bindClass? (p : Program) (site : SiteId) (selector : Selector) :
    Option ClassDeclId :=
  match p.bind site selector with
  | some (.classDecl decl) => some decl
  | _ => none

/-- The finite lexical-class chain beginning at `decl`.  The root constructor
    corresponds to an undefined lexical parent; the step constructor follows
    exactly one `lexParent` edge. -/
inductive LexicalClassChain (p : Program) :
    ClassDeclId → List ClassDeclId → Prop where
  | root {decl : ClassDeclId} :
      p.lexParent decl = none →
      LexicalClassChain p decl [decl]
  | step {decl parent : ClassDeclId} {tail : List ClassDeclId} :
      p.lexParent decl = some parent →
      LexicalClassChain p parent tail →
      LexicalClassChain p decl (decl :: tail)

/-- The executable ECOOP-style class scan of Equation (6.8), evaluated over
    an established finite lexical-class chain. -/
def scanOnClassChain (p : Program) (selector : Selector) :
    List ClassDeclId → Option ClassDeclId
  | [] => none
  | decl :: rest =>
      if p.declares (.classDecl decl) selector then
        some decl
      else
        p.scanOnClassChain selector rest

def ClassScan (p : Program) (start : ClassDeclId) (selector : Selector)
    (result : Option ClassDeclId) : Prop :=
  ∃ chain,
    p.LexicalClassChain start chain ∧
    p.scanOnClassChain selector chain = result

def NoBinding (p : Program) (selector : Selector)
    (decls : List ScopeDecl) : Prop :=
  ∀ decl, decl ∈ decls → p.declares decl selector = false

/-- The precise static hypothesis described informally after Equation (6.9):
    nearer activation/object-literal scopes do not bind the selector, and the
    remaining class scopes are exactly the `lexParent` chain from `firstClass`.
-/
structure ClassBindingContext (p : Program) (site : SiteId)
    (selector : Selector) (firstClass : ClassDeclId) where
  nearerScopes : List ScopeDecl
  classChain : List ClassDeclId
  scopeChain_eq :
    p.scopeChain site =
      nearerScopes ++ classChain.map ScopeDecl.classDecl
  nearerScopesDoNotBind : p.NoBinding selector nearerScopes
  lexicalChain : p.LexicalClassChain firstClass classChain

theorem LexicalClassChain.unique {p : Program} {start : ClassDeclId}
    {xs ys : List ClassDeclId} (hx : p.LexicalClassChain start xs)
    (hy : p.LexicalClassChain start ys) : xs = ys := by
  induction hx generalizing ys with
  | root hnone =>
      cases hy with
      | root => rfl
      | step hsome _ => simp [hnone] at hsome
  | @step decl parent tail hparent htail ih =>
      cases hy with
      | root hnone => simp [hnone] at hparent
      | @step _ parent' tail' hparent' htail' =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          have ht : tail = tail' := ih htail'
          rw [ht]

theorem bindIn_append_of_noBinding {p : Program} {selector : Selector}
    {nearer remaining : List ScopeDecl} (h : p.NoBinding selector nearer) :
    p.bindIn selector (nearer ++ remaining) = p.bindIn selector remaining := by
  induction nearer with
  | nil => rfl
  | cons decl rest ih =>
      have hdecl : p.declares decl selector = false := h decl (by simp)
      have hrest : p.NoBinding selector rest := by
        intro d hd
        exact h d (by simp [hd])
      simp [bindIn, hdecl, ih hrest]

theorem bindIn_classScopes {p : Program} {selector : Selector}
    (classes : List ClassDeclId) :
    p.bindIn selector (classes.map ScopeDecl.classDecl) =
      (p.scanOnClassChain selector classes).map ScopeDecl.classDecl := by
  induction classes with
  | nil => rfl
  | cons decl rest ih =>
      by_cases h : p.declares (.classDecl decl) selector = true
      · simp [bindIn, scanOnClassChain, h]
      · simp [bindIn, scanOnClassChain, h, ih]

theorem bindClass_eq_scanOnContext {p : Program} {site : SiteId}
    {selector : Selector} {firstClass : ClassDeclId}
    (context : p.ClassBindingContext site selector firstClass) :
    p.bindClass? site selector =
      p.scanOnClassChain selector context.classChain := by
  unfold bindClass? bind
  rw [context.scopeChain_eq]
  rw [bindIn_append_of_noBinding context.nearerScopesDoNotBind]
  rw [bindIn_classScopes]
  cases p.scanOnClassChain selector context.classChain <;> rfl

/-- Machine-checked, result-general form of Equation (6.9), including the
    absence case that falls back to self dispatch. -/
theorem binding_equivalence_result {p : Program} {site : SiteId}
    {selector : Selector} {firstClass : ClassDeclId}
    {result : Option ClassDeclId}
    (context : p.ClassBindingContext site selector firstClass) :
    p.bindClass? site selector = result ↔
      p.ClassScan firstClass selector result := by
  constructor
  · intro hbind
    exact ⟨context.classChain, context.lexicalChain,
      (bindClass_eq_scanOnContext context).symm.trans hbind⟩
  · rintro ⟨otherChain, hotherChain, hscan⟩
    have hchains : context.classChain = otherChain :=
      LexicalClassChain.unique context.lexicalChain hotherChain
    rw [bindClass_eq_scanOnContext context, hchains, hscan]

/-- Machine-checked form of Equation (6.9) for a selected declaration. -/
theorem binding_equivalence {p : Program} {site : SiteId}
    {selector : Selector} {firstClass target : ClassDeclId}
    (context : p.ClassBindingContext site selector firstClass) :
    p.bindClass? site selector = some target ↔
      p.ClassScan firstClass selector (some target) :=
  binding_equivalence_result context

end Program
end Newspeak
