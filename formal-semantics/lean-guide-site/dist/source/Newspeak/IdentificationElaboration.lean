import Newspeak.StaticElaboration
import Newspeak.SourceIdentification

namespace Newspeak

def spanPair (span : SourceSpan) : Nat × Nat :=
  (span.startOffset, span.endOffset)

def findIdentifiedNode (span : SourceSpan) (constructorKind : String)
    (sort : SourceNodeSort) : List IdentifiedSourceNode → Option SourceNodeId
  | [] => none
  | node :: remaining =>
      if node.span == some (spanPair span) &&
          node.key.constructorKind == constructorKind && node.sort == sort then
        some node.identity
      else findIdentifiedNode span constructorKind sort remaining

def findExpressionSite (nodes : List IdentifiedSourceNode)
    (span : SourceSpan) (constructorKind : String) : Option SiteId := do
  match ← findIdentifiedNode span constructorKind .expression nodes with
  | .expression site => some site
  | .declaration _ => none

def findDeclarationIdentity (nodes : List IdentifiedSourceNode)
    (span : SourceSpan) (constructorKind : String) : Option DeclId := do
  match ← findIdentifiedNode span constructorKind .declaration nodes with
  | .declaration declaration => some declaration
  | .expression _ => none

/-- Cantor pairing gives disjoint, stable sub-identities for synthetic nodes
    attached to one retained source site. -/
def pairedSyntheticIndex (site : SiteId) (tag : Nat) : Nat :=
  let diagonal := site.index + tag
  (diagonal * (diagonal + 1)) / 2 + tag

def syntheticActivationDeclaration (site : SiteId) (tag : Nat) :
    ActivationDeclId :=
  ⟨2 * pairedSyntheticIndex site tag + 1⟩

def syntheticParameterIdentity (site : SiteId) (tag : Nat) : ParameterId :=
  ⟨pairedSyntheticIndex site tag⟩

def syntheticSiteIdentity (site : SiteId) (tag : Nat) : SiteId :=
  ⟨pairedSyntheticIndex site tag⟩

def cascadeDescriptorAt (site : SiteId) (tag : Nat)
    (immediateClass : Option ClassDeclId) : CascadeDescriptor :=
  { closureDeclaration := syntheticActivationDeclaration site tag
    receiverParameter := syntheticParameterIdentity site tag
    receiverSelector := ⟨"cascadeReceiver"⟩
    immediateClass := immediateClass }

def elaborationIdentitiesFrom (output : IdentificationOutput) :
    ElaborationIdentities :=
  { expressionSite := fun span kind =>
      findExpressionSite output.nodes span kind
    closureDeclaration := fun span => do
      let site ← findExpressionSite output.nodes span "closure"
      pure (syntheticActivationDeclaration site 0)
    classDeclaration := fun span => do
      let declaration ← findDeclarationIdentity output.nodes span "classDeclaration"
      pure ⟨declaration.index⟩
    objectLiteralDeclaration := fun span => do
      let site ← findExpressionSite output.nodes span "objectLiteral"
      pure ⟨site.index⟩
    cascadeDescriptor := fun span immediate => do
      let site ←
        match findExpressionSite output.nodes span "cascade" with
        | some site => some site
        | none => findExpressionSite output.nodes span "setter"
      pure (cascadeDescriptorAt site 1 immediate)
    tupleDescriptor := fun span immediate => do
      let site ← findExpressionSite output.nodes span "tuple"
      pure (site, cascadeDescriptorAt site 2 immediate)
    variablePatternSite := fun span =>
      findExpressionSite output.nodes span "variablePattern"
    keywordPatternDescriptors := fun span immediate => do
      let site ← findExpressionSite output.nodes span "keywordPattern"
      let keywordSite := syntheticSiteIdentity site 3
      let componentSite := syntheticSiteIdentity site 4
      pure (keywordSite, cascadeDescriptorAt site 3 immediate,
        componentSite, cascadeDescriptorAt site 4 immediate) }

def elaborationServicesFrom (output : IdentificationOutput)
    (isUnarySelector : Selector → Bool)
    (defaultSuperclass : ElaborationContext → CoreExpr) (fuel : Nat) :
    ElaborationServices :=
  { identities := elaborationIdentitiesFrom output
    isUnarySelector := isUnarySelector
    defaultSuperclass := defaultSuperclass
    fuel := fuel }

end Newspeak
