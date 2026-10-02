import Newspeak.Dispatch

namespace Newspeak
namespace Program

def ClassMember (p : Program) (h : Heap) (candidate receiverClass : ClassId) :
    Prop :=
  ∃ chain, p.ClassChain h receiverClass chain ∧ candidate ∈ chain

/-- Static lexical ancestry, corresponding to Equation (5.3). -/
inductive LexicalAncestor (p : Program) :
    ClassDeclId → Nat → ClassDeclId → Prop where
  | zero {start : ClassDeclId} :
      LexicalAncestor p start 0 start
  | step {start parent target : ClassDeclId} {depth : Nat} :
      p.lexParent start = some parent →
      LexicalAncestor p parent depth target →
      LexicalAncestor p start (depth + 1) target

theorem lexicalAncestor_deterministic {p : Program} {start : ClassDeclId}
    {depth : Nat} {r₁ r₂ : ClassDeclId}
    (h₁ : p.LexicalAncestor start depth r₁)
    (h₂ : p.LexicalAncestor start depth r₂) : r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | zero =>
      cases h₂
      rfl
  | @step start parent target depth hparent htail ih =>
      cases h₂ with
      | @step _ parent' target' _ hparent' htail' =>
          have hp : parent = parent' := by
            rw [hparent] at hparent'
            injection hparent'
          subst parent'
          exact ih htail'

/-- Enclosing receiver traversal from section 5.  `one` is deliberately a
    separate constructor: it reads the enclosing object from the current
    runtime class application and does not recompute an application from the
    receiver's dynamic class. -/
inductive EnclosingReceiver (p : Program) (h : Heap) :
    ObjRef → ClassId → Nat → ObjRef → Prop where
  | zero {receiver : ObjRef} {currentClass receiverClass : ClassId} :
      h.classOf receiver = some receiverClass →
      p.ClassMember h currentClass receiverClass →
      EnclosingReceiver p h receiver currentClass 0 receiver
  | one {receiver : ObjRef} {currentClass receiverClass : ClassId}
      {classDef : ClassDef} :
      h.classOf receiver = some receiverClass →
      p.ClassMember h currentClass receiverClass →
      h.classes currentClass = some classDef →
      EnclosingReceiver p h receiver currentClass 1 classDef.enclosingObject
  | step {receiver previous : ObjRef} {currentClass previousClass : ClassId}
      {currentDecl ancestorDecl : ClassDeclId} {application : ClassId}
      {applicationDef : ClassDef} {depth : Nat} :
      EnclosingReceiver p h receiver currentClass (depth + 1) previous →
      p.namedClassDeclaration? h currentClass = some currentDecl →
      p.LexicalAncestor currentDecl (depth + 1) ancestorDecl →
      h.classOf previous = some previousClass →
      p.NearestApplication h previousClass ancestorDecl (some application) →
      h.classes application = some applicationDef →
      EnclosingReceiver p h receiver currentClass (depth + 2)
        applicationDef.enclosingObject

theorem enclosingReceiver_deterministic {p : Program} {h : Heap}
    {receiver : ObjRef} {currentClass : ClassId} {depth : Nat}
    {r₁ r₂ : ObjRef}
    (e₁ : p.EnclosingReceiver h receiver currentClass depth r₁)
    (e₂ : p.EnclosingReceiver h receiver currentClass depth r₂) : r₁ = r₂ := by
  induction e₁ generalizing r₂ with
  | zero =>
      cases e₂
      rfl
  | one _ _ hc₁ =>
      cases e₂ with
      | one _ _ hc₂ =>
          have hclassDef := by
            rw [hc₁] at hc₂
            injection hc₂
          cases hclassDef
          rfl
  | step eprev hnamed hancestor hclass happ hdef ih =>
      cases e₂ with
      | step eprev' hnamed' hancestor' hclass' happ' hdef' =>
          have hprevious := ih eprev'
          cases hprevious
          have hcurrentDecl := by
            rw [hnamed] at hnamed'
            injection hnamed'
          cases hcurrentDecl
          have hancestorDecl :=
            lexicalAncestor_deterministic hancestor hancestor'
          cases hancestorDecl
          have hpreviousClass := by
            rw [hclass] at hclass'
            injection hclass'
          cases hpreviousClass
          have happId := by
            have hr := nearestApplication_deterministic happ happ'
            exact Option.some.inj hr
          cases happId
          have happDef := by
            rw [hdef] at hdef'
            injection hdef'
          cases happDef
          rfl

end Program
end Newspeak
