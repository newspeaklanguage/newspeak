import Newspeak.SurfaceNodes
import Newspeak.PrologStaticElaborationCorrespondence

/-!
# Structural correspondence for stable source-node identification

Retained identities win when their structural key is present; otherwise the
sort-specific fresh-identity function is used.  The recursive relation keeps
the source order and extends the retention map in that same order, exactly as
the executable identification pass does.
-/

namespace Newspeak
namespace PrologBridge

inductive PrologSurfaceCompilationUnitNodes (unit : SurfaceCompilationUnit) :
    List UnidentifiedSourceNode → Prop where
  | witness : PrologSurfaceCompilationUnitNodes unit
      (surfaceCompilationUnitNodes unit)

theorem prologSurfaceCompilationUnitNodes_iff {unit nodes} :
    PrologSurfaceCompilationUnitNodes unit nodes ↔
      surfaceCompilationUnitNodes unit = nodes := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst nodes; exact .witness

inductive PrologFreshSourceNodeId (supply : IdentificationSupply)
    (position : Nat) (sort : SourceNodeSort) : SourceNodeId → Prop where
  | witness : PrologFreshSourceNodeId supply position sort
      (freshSourceNodeId supply position sort)

theorem prologFreshSourceNodeId_iff {supply position sort identity} :
    PrologFreshSourceNodeId supply position sort identity ↔
      freshSourceNodeId supply position sort = identity := by
  constructor <;> intro premise
  · cases premise; rfl
  · subst identity; exact .witness

inductive PrologSelectedSourceNodeId (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (position : Nat)
    (node : UnidentifiedSourceNode) : SourceNodeId → Prop where
  | retained {identity : SourceNodeId} :
      retained node.key = some identity →
      PrologSelectedSourceNodeId retained supply position node identity
  | fresh {identity : SourceNodeId} :
      retained node.key = none →
      PrologFreshSourceNodeId supply position node.sort identity →
      PrologSelectedSourceNodeId retained supply position node identity

theorem prologSelectedSourceNodeId_iff
    {retained supply position node identity} :
    PrologSelectedSourceNodeId retained supply position node identity ↔
      selectedSourceNodeId retained supply position node = identity := by
  constructor
  · intro selected
    cases selected with
    | retained found => simp [selectedSourceNodeId, found]
    | fresh absent fresh =>
        cases fresh
        simp [selectedSourceNodeId, absent]
  · intro equal
    cases found : retained node.key with
    | none =>
        exact PrologSelectedSourceNodeId.fresh found
          (prologFreshSourceNodeId_iff.mpr
            (by simpa [selectedSourceNodeId, found] using equal))
    | some retainedIdentity =>
        have identityEqual : retainedIdentity = identity := by
          simpa [selectedSourceNodeId, found] using equal
        cases identityEqual
        exact PrologSelectedSourceNodeId.retained found

inductive PrologIdentifySourceNodesFrom (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) :
    Nat → List UnidentifiedSourceNode → List IdentifiedSourceNode → Prop where
  | nil (position : Nat) :
      PrologIdentifySourceNodesFrom retained supply position [] []
  | cons {position : Nat} {source : UnidentifiedSourceNode}
      {sources : List UnidentifiedSourceNode} {identity : SourceNodeId}
      {identified : List IdentifiedSourceNode} :
      PrologSelectedSourceNodeId retained supply position source identity →
      PrologIdentifySourceNodesFrom retained supply (position + 1) sources
        identified →
      PrologIdentifySourceNodesFrom retained supply position (source :: sources)
        ({ key := source.key, sort := source.sort, span := source.span,
           identity := identity } :: identified)

theorem PrologIdentifySourceNodesFrom.sound
    {retained supply position sources identified}
    (derivation : PrologIdentifySourceNodesFrom retained supply position
      sources identified) :
    identifySourceNodesFrom retained supply position sources = identified := by
  induction derivation with
  | nil => rfl
  | cons selected remaining ih =>
      simp [identifySourceNodesFrom, prologSelectedSourceNodeId_iff.mp selected,
        ih]

theorem prologIdentifySourceNodesFrom_complete
    (retained : IdentityRetentionMap) (supply : IdentificationSupply) :
    ∀ (position : Nat) (sources : List UnidentifiedSourceNode),
      PrologIdentifySourceNodesFrom retained supply position sources
        (identifySourceNodesFrom retained supply position sources) := by
  intro position sources
  induction sources generalizing position with
  | nil => exact .nil position
  | cons source remaining ih =>
      exact .cons
        (prologSelectedSourceNodeId_iff.mpr rfl)
        (ih (position + 1))

theorem prologIdentifySourceNodesFrom_iff
    {retained supply position sources identified} :
    PrologIdentifySourceNodesFrom retained supply position sources identified ↔
      identifySourceNodesFrom retained supply position sources = identified := by
  constructor
  · exact PrologIdentifySourceNodesFrom.sound
  · intro equal
    subst identified
    exact prologIdentifySourceNodesFrom_complete retained supply position sources

inductive PrologIdentifiedSourceNodeListOK
    (nodes : List IdentifiedSourceNode) : Prop where
  | checked : identifiedSourceNodesOK nodes = true →
      PrologIdentifiedSourceNodeListOK nodes

theorem prologIdentifiedSourceNodeListOK_iff {nodes} :
    PrologIdentifiedSourceNodeListOK nodes ↔
      identifiedSourceNodesOK nodes = true := by
  constructor <;> intro premise
  · cases premise with | checked proof => exact proof
  · exact .checked premise

inductive PrologExtendIdentityRetention :
    IdentityRetentionMap → List IdentifiedSourceNode →
      IdentityRetentionMap → Prop where
  | nil (retained : IdentityRetentionMap) :
      PrologExtendIdentityRetention retained [] retained
  | cons {retained next extended : IdentityRetentionMap}
      {node : IdentifiedSourceNode} {remaining : List IdentifiedSourceNode} :
      next = retained.install node.key node.identity →
      PrologExtendIdentityRetention next remaining extended →
      PrologExtendIdentityRetention retained (node :: remaining) extended

theorem PrologExtendIdentityRetention.sound
    {retained nodes extended}
    (derivation : PrologExtendIdentityRetention retained nodes extended) :
    extendIdentityRetention retained nodes = extended := by
  induction derivation with
  | nil => rfl
  | cons installed remaining ih =>
      subst installed
      simpa [extendIdentityRetention, List.foldl] using ih

theorem prologExtendIdentityRetention_complete :
    ∀ (retained : IdentityRetentionMap) (nodes : List IdentifiedSourceNode),
      PrologExtendIdentityRetention retained nodes
        (extendIdentityRetention retained nodes) := by
  intro retained nodes
  induction nodes generalizing retained with
  | nil => exact .nil retained
  | cons node remaining ih =>
      exact .cons rfl (ih (retained.install node.key node.identity))

theorem prologExtendIdentityRetention_iff {retained nodes extended} :
    PrologExtendIdentityRetention retained nodes extended ↔
      extendIdentityRetention retained nodes = extended := by
  constructor
  · exact PrologExtendIdentityRetention.sound
  · intro equal
    subst extended
    exact prologExtendIdentityRetention_complete retained nodes

inductive PrologIdentifySourceNodes (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (nodes : List UnidentifiedSourceNode) :
    IdentificationOutput → Prop where
  | identified {identified : List IdentifiedSourceNode}
      {extended : IdentityRetentionMap} :
      PrologIdentifySourceNodesFrom retained supply 0 nodes identified →
      PrologIdentifiedSourceNodeListOK identified →
      PrologExtendIdentityRetention retained identified extended →
      PrologIdentifySourceNodes retained supply nodes
        ⟨identified, extended⟩

theorem prologIdentifySourceNodes_iff {retained supply nodes output} :
    PrologIdentifySourceNodes retained supply nodes output ↔
      identifySourceNodes retained supply nodes = some output := by
  constructor
  · intro derivation
    cases derivation with
    | identified fromNodes valid extended =>
        have fromEqual := fromNodes.sound
        have validEqual := prologIdentifiedSourceNodeListOK_iff.mp valid
        have extendedEqual := extended.sound
        simp [identifySourceNodes, fromEqual, validEqual, extendedEqual]
  · intro success
    let identified := identifySourceNodesFrom retained supply 0 nodes
    cases valid : identifiedSourceNodesOK identified with
    | false => simp [identifySourceNodes, identified, valid] at success
    | true =>
        simp [identifySourceNodes, identified, valid] at success
        cases success
        exact .identified
          (prologIdentifySourceNodesFrom_complete retained supply 0 nodes)
          (.checked valid)
          (prologExtendIdentityRetention_complete retained identified)

inductive PrologSurfaceIdentification (retained : IdentityRetentionMap)
    (supply : IdentificationSupply) (unit : SurfaceCompilationUnit) :
    IdentificationOutput → Prop where
  | result {nodes : List UnidentifiedSourceNode}
      {identification : IdentificationOutput} :
      PrologSurfaceCompilationUnitNodes unit nodes →
      PrologIdentifySourceNodes retained supply nodes identification →
      PrologSurfaceIdentification retained supply unit identification

theorem prologSurfaceIdentification_iff {retained supply unit identification} :
    PrologSurfaceIdentification retained supply unit identification ↔
      identifySurfaceCompilationUnit retained supply unit =
        some identification := by
  constructor
  · intro derivation
    cases derivation with
    | result nodes identified =>
        unfold identifySurfaceCompilationUnit
        rw [prologSurfaceCompilationUnitNodes_iff.mp nodes]
        exact prologIdentifySourceNodes_iff.mp identified
  · intro success
    exact .result .witness (prologIdentifySourceNodes_iff.mpr success)

end PrologBridge
end Newspeak
