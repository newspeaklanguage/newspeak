import Newspeak.LexicalBinding

namespace Newspeak
namespace Program

def classBodyDeclaration? (p : Program) (h : Heap)
    (classId : ClassId) : Option ClassBodyDecl := do
  let classDef ← h.classes classId
  let mixinDef ← p.mixins classDef.mixin
  some mixinDef.declaration

def namedClassDeclaration? (p : Program) (h : Heap)
    (classId : ClassId) : Option ClassDeclId :=
  match p.classBodyDeclaration? h classId with
  | some (.namedClass decl) => some decl
  | _ => none

/-- Most-specific application of a named class declaration along a runtime
    class chain, corresponding to Equations (5.4) and (5.5). -/
def nearestApplicationOnChain (p : Program) (h : Heap)
    (target : ClassDeclId) : List ClassId → Option ClassId
  | [] => none
  | classId :: rest =>
      if classId = p.top then
        none
      else if p.namedClassDeclaration? h classId = some target then
        some classId
      else
        p.nearestApplicationOnChain h target rest

def NearestApplication (p : Program) (h : Heap) (receiverClass : ClassId)
    (target : ClassDeclId) (result : Option ClassId) : Prop :=
  ∃ chain,
    p.ClassChain h receiverClass chain ∧
    p.nearestApplicationOnChain h target chain = result

theorem nearestApplication_deterministic {p : Program} {h : Heap}
    {receiverClass : ClassId} {target : ClassDeclId}
    {r₁ r₂ : Option ClassId}
    (h₁ : p.NearestApplication h receiverClass target r₁)
    (h₂ : p.NearestApplication h receiverClass target r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨chain₁, hc₁, hr₁⟩
  rcases h₂ with ⟨chain₂, hc₂, hr₂⟩
  have hchain : chain₁ = chain₂ := ClassChain.unique hc₁ hc₂
  subst chain₂
  rw [← hr₁, ← hr₂]

def TargetApplication (p : Program) (h : Heap) (receiver : ObjRef)
    (target : ClassDeclId) (result : Option ClassId) : Prop :=
  ∃ receiverClass,
    h.classOf receiver = some receiverClass ∧
    p.NearestApplication h receiverClass target result

theorem targetApplication_deterministic {p : Program} {h : Heap}
    {receiver : ObjRef} {target : ClassDeclId} {r₁ r₂ : Option ClassId}
    (h₁ : p.TargetApplication h receiver target r₁)
    (h₂ : p.TargetApplication h receiver target r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨class₁, hc₁, ha₁⟩
  rcases h₂ with ⟨class₂, hc₂, ha₂⟩
  have hclass : class₁ = class₂ := by
    rw [hc₁] at hc₂
    injection hc₂
  subst class₂
  exact nearestApplication_deterministic ha₁ ha₂

def lexicalDepthOnChain (target : ClassDeclId) :
    List ClassDeclId → Option Nat
  | [] => none
  | decl :: rest =>
      if decl = target then
        some 0
      else
        (lexicalDepthOnChain target rest).map Nat.succ

def LexicalDepth (p : Program) (target start : ClassDeclId)
    (result : Option Nat) : Prop :=
  ∃ chain,
    p.LexicalClassChain start chain ∧
    lexicalDepthOnChain target chain = result

theorem lexicalDepth_deterministic {p : Program} {target start : ClassDeclId}
    {r₁ r₂ : Option Nat} (h₁ : p.LexicalDepth target start r₁)
    (h₂ : p.LexicalDepth target start r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨chain₁, hc₁, hr₁⟩
  rcases h₂ with ⟨chain₂, hc₂, hr₂⟩
  have hchain : chain₁ = chain₂ := LexicalClassChain.unique hc₁ hc₂
  subst chain₂
  rw [← hr₁, ← hr₂]

end Program
end Newspeak
