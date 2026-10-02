import Newspeak.PEG
import Newspeak.Id

namespace Newspeak

inductive SourceNodeSort where
  | declaration
  | expression
deriving Repr, DecidableEq, BEq

/-- Stable editor key: source-unit identity, structural path, constructor kind,
    and the declared name when the node has one. -/
structure SourceNodeKey where
  sourceUnit : String
  path : List Nat
  constructorKind : String
  declaredName : Option String
deriving Repr, DecidableEq, BEq

structure UnidentifiedSourceNode where
  key : SourceNodeKey
  sort : SourceNodeSort
  span : Option (Nat × Nat) := none
deriving Repr, DecidableEq, BEq

inductive SourceNodeId where
  | declaration (identity : DeclId)
  | expression (identity : SiteId)
deriving Repr, DecidableEq, BEq

def sameSourceNodeId : SourceNodeId → SourceNodeId → Bool
  | .declaration ⟨left⟩, .declaration ⟨right⟩ => left == right
  | .expression ⟨left⟩, .expression ⟨right⟩ => left == right
  | _, _ => false

@[simp] theorem sameSourceNodeId_eq_true_iff (left right : SourceNodeId) :
    sameSourceNodeId left right = true ↔ left = right := by
  cases left with
  | declaration leftIdentity =>
      cases leftIdentity with
      | mk leftIndex =>
          cases right with
          | declaration rightIdentity =>
              cases rightIdentity with
              | mk rightIndex => simp [sameSourceNodeId]
          | expression rightIdentity => simp [sameSourceNodeId]
  | expression leftIdentity =>
      cases leftIdentity with
      | mk leftIndex =>
          cases right with
          | declaration rightIdentity => simp [sameSourceNodeId]
          | expression rightIdentity =>
              cases rightIdentity with
              | mk rightIndex => simp [sameSourceNodeId]

@[simp] theorem sameSourceNodeId_eq_false_iff (left right : SourceNodeId) :
    sameSourceNodeId left right = false ↔ left ≠ right := by
  cases left with
  | declaration leftIdentity =>
      cases leftIdentity with
      | mk leftIndex =>
          cases right with
          | declaration rightIdentity =>
              cases rightIdentity with
              | mk rightIndex => simp [sameSourceNodeId]
          | expression rightIdentity => simp [sameSourceNodeId]
  | expression leftIdentity =>
      cases leftIdentity with
      | mk leftIndex =>
          cases right with
          | declaration rightIdentity => simp [sameSourceNodeId]
          | expression rightIdentity =>
              cases rightIdentity with
              | mk rightIndex => simp [sameSourceNodeId]

def SourceNodeId.hasSort : SourceNodeId → SourceNodeSort → Bool
  | .declaration _, .declaration => true
  | .expression _, .expression => true
  | _, _ => false

structure IdentificationSupply where
  nextDeclaration : Nat
  nextExpression : Nat
deriving Repr, DecidableEq, BEq

abbrev IdentityRetentionMap := FiniteStore SourceNodeKey SourceNodeId

structure IdentifiedSourceNode where
  key : SourceNodeKey
  sort : SourceNodeSort
  span : Option (Nat × Nat)
  identity : SourceNodeId
deriving Repr, DecidableEq, BEq

structure IdentificationOutput where
  nodes : List IdentifiedSourceNode
  retention : IdentityRetentionMap

def freshSourceNodeId (supply : IdentificationSupply) (position : Nat) :
    SourceNodeSort → SourceNodeId
  | .declaration => .declaration ⟨supply.nextDeclaration + position⟩
  | .expression => .expression ⟨supply.nextExpression + position⟩

def selectedSourceNodeId (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (position : Nat)
    (node : UnidentifiedSourceNode) : SourceNodeId :=
  (retained node.key).getD (freshSourceNodeId supply position node.sort)

def identifySourceNodesFrom (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) :
    Nat → List UnidentifiedSourceNode → List IdentifiedSourceNode
  | _, [] => []
  | position, node :: remaining =>
      let identity := selectedSourceNodeId retained supply position node
      { key := node.key, sort := node.sort, span := node.span,
        identity := identity } ::
        identifySourceNodesFrom retained supply (position + 1) remaining

def SourceNodeCorresponds (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (position : Nat)
    (source : UnidentifiedSourceNode) (identified : IdentifiedSourceNode) : Prop :=
  identified.key = source.key ∧ identified.sort = source.sort ∧
    identified.span = source.span ∧
    identified.identity = selectedSourceNodeId retained supply position source

inductive SourceNodesCorrespond (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) :
    Nat → List UnidentifiedSourceNode → List IdentifiedSourceNode → Prop where
  | nil (position) : SourceNodesCorrespond retained supply position [] []
  | cons {position source identified sources identifiedNodes}
      (head : SourceNodeCorresponds retained supply position source identified)
      (tail : SourceNodesCorrespond retained supply (position + 1)
        sources identifiedNodes) :
      SourceNodesCorrespond retained supply position
        (source :: sources) (identified :: identifiedNodes)

def SourceNodeRetentionPreserved (retained : IdentityRetentionMap)
    (source : UnidentifiedSourceNode) (identified : IdentifiedSourceNode) : Prop :=
  ∀ identity, retained source.key = some identity →
    identified.identity = identity

inductive SourceNodeRetentionsPreserved (retained : IdentityRetentionMap) :
    List UnidentifiedSourceNode → List IdentifiedSourceNode → Prop where
  | nil : SourceNodeRetentionsPreserved retained [] []
  | cons {source identified sources identifiedNodes}
      (head : SourceNodeRetentionPreserved retained source identified)
      (tail : SourceNodeRetentionsPreserved retained sources identifiedNodes) :
      SourceNodeRetentionsPreserved retained
        (source :: sources) (identified :: identifiedNodes)

theorem SourceNodeCorresponds.retains
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {position : Nat} {source : UnidentifiedSourceNode}
    {identified : IdentifiedSourceNode}
    (corresponds : SourceNodeCorresponds retained supply position source identified) :
    SourceNodeRetentionPreserved retained source identified := by
  intro identity retainedIdentity
  rw [corresponds.2.2.2]
  simp [selectedSourceNodeId, retainedIdentity]

theorem SourceNodesCorrespond.retains
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {position : Nat} {sources : List UnidentifiedSourceNode}
    {identified : List IdentifiedSourceNode}
    (correspond : SourceNodesCorrespond retained supply position sources identified) :
    SourceNodeRetentionsPreserved retained sources identified := by
  induction correspond with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons head.retains ih

theorem identifySourceNodesFrom_length
    (retained : IdentityRetentionMap) (supply : IdentificationSupply)
    (position : Nat) (nodes : List UnidentifiedSourceNode) :
    (identifySourceNodesFrom retained supply position nodes).length = nodes.length := by
  induction nodes generalizing position with
  | nil => rfl
  | cons node remaining ih =>
      simp [identifySourceNodesFrom, ih]

theorem identifySourceNodesFrom_corresponds
    (retained : IdentityRetentionMap) (supply : IdentificationSupply) :
    ∀ (position : Nat) (nodes : List UnidentifiedSourceNode),
      SourceNodesCorrespond retained supply position nodes
        (identifySourceNodesFrom retained supply position nodes) := by
  intro position nodes
  induction nodes generalizing position with
  | nil => exact .nil position
  | cons node remaining ih =>
      apply SourceNodesCorrespond.cons
      · simp [SourceNodeCorresponds, selectedSourceNodeId]
      · exact ih (position + 1)

def extendIdentityRetention (retained : IdentityRetentionMap)
    (nodes : List IdentifiedSourceNode) : IdentityRetentionMap :=
  nodes.foldl (fun current node =>
    current.install node.key node.identity) retained

def sourceNodeIdentitiesDistinct : List IdentifiedSourceNode → Bool
  | [] => true
  | node :: remaining =>
      !remaining.any (fun other => sameSourceNodeId node.identity other.identity) &&
        sourceNodeIdentitiesDistinct remaining

theorem sourceNodeIdentitiesDistinct_eq_true_iff
    (nodes : List IdentifiedSourceNode) :
    sourceNodeIdentitiesDistinct nodes = true ↔
      (nodes.map IdentifiedSourceNode.identity).Nodup := by
  induction nodes with
  | nil => simp [sourceNodeIdentitiesDistinct]
  | cons node remaining ih =>
      simp [sourceNodeIdentitiesDistinct, ih, ne_comm]

def identifiedSourceNodesOK (nodes : List IdentifiedSourceNode) : Bool :=
  sourceNodeIdentitiesDistinct nodes &&
    nodes.all (fun node => node.identity.hasSort node.sort)

def IdentifiedSourceNodesOK (nodes : List IdentifiedSourceNode) : Prop :=
  identifiedSourceNodesOK nodes = true

/-- Stable identification is partial exactly where retained identities are
    ill-sorted or collide.  Fresh identities come from their sort-specific
    frontier and source position; the final guard independently checks the
    injectivity and sort conditions required by `idsOK`. -/
def identifySourceNodes (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (nodes : List UnidentifiedSourceNode) :
    Option IdentificationOutput :=
  let identified := identifySourceNodesFrom retained supply 0 nodes
  match identifiedSourceNodesOK identified with
  | true =>
      some
        { nodes := identified
          retention := extendIdentityRetention retained identified }
  | false => none

theorem identifySourceNodes_success_idsOK
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {nodes : List UnidentifiedSourceNode} {output : IdentificationOutput}
    (success : identifySourceNodes retained supply nodes = some output) :
    IdentifiedSourceNodesOK output.nodes := by
  let identified := identifySourceNodesFrom retained supply 0 nodes
  cases valid : identifiedSourceNodesOK identified <;>
    simp [identifySourceNodes, identified, valid] at success
  subst output
  exact valid

theorem identifySourceNodes_success_identity_injective
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {nodes : List UnidentifiedSourceNode} {output : IdentificationOutput}
    (success : identifySourceNodes retained supply nodes = some output) :
    (output.nodes.map IdentifiedSourceNode.identity).Nodup := by
  have valid := identifySourceNodes_success_idsOK success
  simp only [IdentifiedSourceNodesOK, identifiedSourceNodesOK,
    Bool.and_eq_true] at valid
  exact (sourceNodeIdentitiesDistinct_eq_true_iff output.nodes).mp valid.1

theorem identifySourceNodes_success_sorts
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {nodes : List UnidentifiedSourceNode} {output : IdentificationOutput}
    (success : identifySourceNodes retained supply nodes = some output) :
    output.nodes.all (fun node => node.identity.hasSort node.sort) = true := by
  have valid := identifySourceNodes_success_idsOK success
  simp only [IdentifiedSourceNodesOK, identifiedSourceNodesOK,
    Bool.and_eq_true] at valid
  exact valid.2

theorem identifySourceNodes_deterministic
    {retained : IdentityRetentionMap} {supply : IdentificationSupply}
    {nodes : List UnidentifiedSourceNode}
    {first second : IdentificationOutput}
    (firstResult : identifySourceNodes retained supply nodes = some first)
    (secondResult : identifySourceNodes retained supply nodes = some second) :
    first = second := by
  rw [firstResult] at secondResult
  injection secondResult

end Newspeak
