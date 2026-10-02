import Newspeak.ReflectionDebugger

namespace Newspeak

abbrev TemplateKeyMap := List (FrameTemplateKey × ActivationId)

def lookupTemplateKey : TemplateKeyMap → FrameTemplateKey → Option ActivationId
  | [], _ => none
  | (candidate, activation) :: remaining, key =>
      if candidate = key then some activation else lookupTemplateKey remaining key

structure TemplateKeyResolution where
  bindings : TemplateKeyMap
  nextActivation : Nat

def freshTemplateBindingsAbsent (heap : Heap) : TemplateKeyMap → Bool
  | [] => true
  | (key, activation) :: remaining =>
      let current := match key with
        | .retain _ => true
        | .freshFrame _ => (heap.activations activation).isNone
      current && freshTemplateBindingsAbsent heap remaining

def retainedTemplateBindingsPreserveIdentity : TemplateKeyMap → Bool
  | [] => true
  | (key, activation) :: remaining =>
      let current := match key with
        | .retain retained => if retained = activation then true else false
        | .freshFrame _ => true
      current && retainedTemplateBindingsPreserveIdentity remaining

def resolveTemplateKeysAux (heap : Heap) :
    Nat → List FrameTemplateKey → List FrameTemplateKey → List ActivationId →
      Option TemplateKeyResolution
  | next, [], _, _ => some ⟨[], next⟩
  | next, key :: remaining, seenKeys, seenActivations => do
      if FiniteStore.containsKey seenKeys key then none
      else
        let activation ← match key with
          | .retain retained => do
              let _ ← heap.activations retained
              some retained
          | .freshFrame _ =>
              let fresh : ActivationId := ⟨next⟩
              if heap.activations fresh = none then some fresh else none
        if FiniteStore.containsKey seenActivations activation then none
        else
          let next' := match key with
            | .retain _ => next
            | .freshFrame _ => next + 1
          let tail ← resolveTemplateKeysAux heap next' remaining
            (key :: seenKeys) (activation :: seenActivations)
          some ⟨(key, activation) :: tail.bindings, tail.nextActivation⟩

def resolveTemplateKeys (state : AllocationState) (template : StackTemplate) :
    Option TemplateKeyResolution := do
  let resolution ← resolveTemplateKeysAux state.heap state.nextActivation
    (template.map FrameTemplate.key) [] []
  if (resolution.bindings.map Prod.fst).Nodup ∧
      (resolution.bindings.map Prod.snd).Nodup ∧
      freshTemplateBindingsAbsent state.heap resolution.bindings = true ∧
      retainedTemplateBindingsPreserveIdentity resolution.bindings = true then
    some resolution
  else none

theorem resolveTemplateKeys_properties {state : AllocationState}
    {template : StackTemplate} {resolution : TemplateKeyResolution}
    (result : resolveTemplateKeys state template = some resolution) :
    (resolution.bindings.map Prod.fst).Nodup ∧
      (resolution.bindings.map Prod.snd).Nodup ∧
      freshTemplateBindingsAbsent state.heap resolution.bindings = true ∧
      retainedTemplateBindingsPreserveIdentity resolution.bindings = true := by
  unfold resolveTemplateKeys at result
  cases auxiliaryResult : resolveTemplateKeysAux state.heap state.nextActivation
      (List.map FrameTemplate.key template) [] [] with
  | none => simp [auxiliaryResult] at result
  | some candidate =>
      simp only [auxiliaryResult] at result
      by_cases valid :
          (candidate.bindings.map Prod.fst).Nodup ∧
          (candidate.bindings.map Prod.snd).Nodup ∧
          freshTemplateBindingsAbsent state.heap candidate.bindings = true ∧
          retainedTemplateBindingsPreserveIdentity candidate.bindings = true
      · simp [valid] at result
        subst resolution
        exact valid
      · simp [valid] at result

def FreshTemplateBindingsAreFresh (heap : Heap)
    (bindings : TemplateKeyMap) : Prop :=
  ∀ key activation,
    (FrameTemplateKey.freshFrame key, activation) ∈ bindings →
    heap.activations activation = none

def RetainedTemplateBindingsPreserveIdentity
    (bindings : TemplateKeyMap) : Prop :=
  ∀ retained activation,
    (FrameTemplateKey.retain retained, activation) ∈ bindings →
    activation = retained

theorem freshTemplateBindingsAbsent_sound (heap : Heap)
    (bindings : TemplateKeyMap)
    (checked : freshTemplateBindingsAbsent heap bindings = true) :
    FreshTemplateBindingsAreFresh heap bindings := by
  induction bindings with
  | nil => simp [FreshTemplateBindingsAreFresh]
  | cons binding remaining ih =>
      rcases binding with ⟨bindingKey, bindingActivation⟩
      cases bindingKey with
      | retain retained =>
          simp only [freshTemplateBindingsAbsent, Bool.true_and] at checked
          intro key activation member
          rcases List.mem_cons.mp member with equal | tail
          · cases equal
          · exact ih checked key activation tail
      | freshFrame fresh =>
          simp only [freshTemplateBindingsAbsent, Bool.and_eq_true] at checked
          intro key activation member
          rcases List.mem_cons.mp member with equal | tail
          · cases equal
            cases activationResult : heap.activations bindingActivation with
            | none => rfl
            | some definition => simp [activationResult] at checked
          · exact ih checked.2 key activation tail

theorem retainedTemplateBindingsPreserveIdentity_sound
    (bindings : TemplateKeyMap)
    (checked : retainedTemplateBindingsPreserveIdentity bindings = true) :
    RetainedTemplateBindingsPreserveIdentity bindings := by
  induction bindings with
  | nil => simp [RetainedTemplateBindingsPreserveIdentity]
  | cons binding remaining ih =>
      rcases binding with ⟨bindingKey, bindingActivation⟩
      cases bindingKey with
      | freshFrame fresh =>
          simp only [retainedTemplateBindingsPreserveIdentity,
            Bool.true_and] at checked
          intro retained activation member
          rcases List.mem_cons.mp member with equal | tail
          · cases equal
          · exact ih checked retained activation tail
      | retain retained =>
          simp only [retainedTemplateBindingsPreserveIdentity,
            Bool.and_eq_true] at checked
          intro query activation member
          rcases List.mem_cons.mp member with equal | tail
          · injection equal with keyEqual activationEqual
            have queryEqual : query = retained :=
              FrameTemplateKey.retain.inj keyEqual
            subst query
            by_cases identity : retained = bindingActivation
            · exact activationEqual.trans identity.symm
            · simp [identity] at checked
          · exact ih checked.2 query activation tail

theorem resolvedTemplateKeys_are_fresh_and_distinct
    {state : AllocationState} {template : StackTemplate}
    {resolution : TemplateKeyResolution}
    (result : resolveTemplateKeys state template = some resolution) :
    (resolution.bindings.map Prod.snd).Nodup ∧
      FreshTemplateBindingsAreFresh state.heap resolution.bindings ∧
      RetainedTemplateBindingsPreserveIdentity resolution.bindings := by
  have properties := resolveTemplateKeys_properties result
  exact ⟨properties.2.1,
    freshTemplateBindingsAbsent_sound _ _ properties.2.2.1,
    retainedTemplateBindingsPreserveIdentity_sound _ properties.2.2.2⟩

def resolveOptionalTemplateKey (bindings : TemplateKeyMap) :
    Option FrameTemplateKey → Option (Option ActivationId)
  | none => some none
  | some key => (lookupTemplateKey bindings key).map some

def resolveTemplateScopeEntries (bindings : TemplateKeyMap)
    (source : FiniteStore ActivationDeclId FrameTemplateKey) :
    List ActivationDeclId → FiniteStore ActivationDeclId ActivationId →
      Option (FiniteStore ActivationDeclId ActivationId)
  | [], destination => some destination
  | declaration :: remaining, destination => do
      let key ← source declaration
      let activation ← lookupTemplateKey bindings key
      resolveTemplateScopeEntries bindings source remaining
        (destination.install declaration activation)

def resolveTemplateScopes (bindings : TemplateKeyMap)
    (source : FiniteStore ActivationDeclId FrameTemplateKey) :
    Option (FiniteStore ActivationDeclId ActivationId) :=
  resolveTemplateScopeEntries bindings source source.domain
    (FiniteStore.empty ActivationDeclId ActivationId)

def resolveActivationRecordTemplate (bindings : TemplateKeyMap)
    (template : ActivationRecordTemplate) : Option ActivationDef := do
  let continuation ← resolveOptionalTemplateKey bindings template.continuation
  let homeMethod ← resolveOptionalTemplateKey bindings template.homeMethod
  let scopes ← resolveTemplateScopes bindings template.activationScopes
  some
    { objectClass := template.objectClass
      provenance := template.provenance
      parameters := template.parameters
      locals := template.locals
      currentReceiver := template.currentReceiver
      currentClass := template.currentClass
      continuation := continuation
      homeMethod := homeMethod
      continuable := template.continuable
      activationScopes := scopes
      objectLiteralScopes := template.objectLiteralScopes }

structure ResolvedFrameImage where
  activation : ActivationId
  control : FrameControl

/-- Decoder requiring every lower image to be suspended and the unique top
    image to carry the active term. -/
def decodeControlImageAux (built : ActivationStack) :
    List ResolvedFrameImage → Option (ActivationStack × ControlTerm)
  | [] => none
  | [image] => match image.control with
      | .activeControl frames term =>
          some (.push built ⟨image.activation, frames⟩, term)
      | .suspendedControl _ => none
  | image :: remaining => match image.control with
      | .activeControl _ _ => none
      | .suspendedControl frames =>
          decodeControlImageAux (.push built ⟨image.activation, frames⟩) remaining

def decodeControlImage (images : List ResolvedFrameImage) :
    Option (ActivationStack × ControlTerm) :=
  decodeControlImageAux .empty images

def installResolvedFrameTemplates (bindings : TemplateKeyMap) :
    Heap → StackTemplate → Option (Heap × List ResolvedFrameImage)
  | heap, [] => some (heap, [])
  | heap, frame :: remaining => do
      let activation ← lookupTemplateKey bindings frame.key
      let definition ← resolveActivationRecordTemplate bindings frame.activation
      let installed := heap.installActivation activation definition
      let tail ← installResolvedFrameTemplates bindings installed remaining
      some (tail.1, ⟨activation, frame.control⟩ :: tail.2)

def resolvedTemplateActivationIds (bindings : TemplateKeyMap)
    (template : StackTemplate) : Option (List ActivationId) :=
  template.mapM fun frame => lookupTemplateKey bindings frame.key

/-- Concrete atomic materialization of a complete debugger stack image. -/
def materializeStackTemplate : StackTemplateMaterializer :=
  fun _program state oldStack template => do
    let resolution ← resolveTemplateKeys state template
    let newIds ← resolvedTemplateActivationIds resolution.bindings template
    let removed := oldStack.activationIds.filter fun activation =>
      !(FiniteStore.containsKey newIds activation)
    let retired := state.heap.retireRemovedActivations removed
    let installed ← installResolvedFrameTemplates resolution.bindings retired template
    let decoded ← decodeControlImage installed.2
    let allocation :=
      { state with
        heap := installed.1
        nextActivation := resolution.nextActivation }
    some (allocation, decoded.1, decoded.2)

theorem decodeControlImageAux_nonempty {built stack : ActivationStack}
    {images : List ResolvedFrameImage} {term : ControlTerm}
    (result : decodeControlImageAux built images = some (stack, term)) :
    stack.Nonempty := by
  induction images generalizing built stack term with
  | nil => simp [decodeControlImageAux] at result
  | cons image remaining ih =>
      cases remaining with
      | nil =>
          cases controlResult : image.control with
          | activeControl frames activeTerm =>
              simp [decodeControlImageAux, controlResult] at result
              rw [← result.1]
              trivial
          | suspendedControl frames =>
              simp [decodeControlImageAux, controlResult] at result
      | cons next later =>
          cases controlResult : image.control with
          | activeControl frames activeTerm =>
              simp [decodeControlImageAux, controlResult] at result
          | suspendedControl frames =>
              apply ih
              simpa [decodeControlImageAux, controlResult] using result

theorem decodeControlImage_nonempty {images : List ResolvedFrameImage}
    {stack : ActivationStack} {term : ControlTerm}
    (result : decodeControlImage images = some (stack, term)) :
    stack.Nonempty :=
  decodeControlImageAux_nonempty result

theorem materializeStackTemplate_nonempty
    {program : Program} {state after : AllocationState}
    {oldStack newStack : ActivationStack} {template : StackTemplate}
    {term : ControlTerm}
    (result : materializeStackTemplate program state oldStack template =
      some (after, newStack, term)) :
    newStack.Nonempty := by
  unfold materializeStackTemplate at result
  cases resolutionResult : resolveTemplateKeys state template with
  | none =>
      rw [resolutionResult] at result
      contradiction
  | some resolution =>
      rw [resolutionResult] at result
      dsimp at result
      cases idsResult : resolvedTemplateActivationIds resolution.bindings template with
      | none =>
          rw [idsResult] at result
          contradiction
      | some ids =>
          rw [idsResult] at result
          dsimp at result
          let removed := oldStack.activationIds.filter fun activation =>
            !(FiniteStore.containsKey ids activation)
          let retired := state.heap.retireRemovedActivations removed
          cases installResult : installResolvedFrameTemplates resolution.bindings retired template with
          | none =>
              dsimp [removed, retired] at installResult
              rw [installResult] at result
              contradiction
          | some installed =>
              dsimp [removed, retired] at installResult
              rw [installResult] at result
              dsimp at result
              cases decodeResult : decodeControlImage installed.2 with
              | none =>
                  rw [decodeResult] at result
                  contradiction
              | some decoded =>
                  rcases decoded with ⟨decodedStack, decodedTerm⟩
                  rw [decodeResult] at result
                  dsimp at result
                  have tupleEqual := Option.some.inj result
                  have stackEqual : decodedStack = newStack :=
                    congrArg (fun triple => triple.2.1) tupleEqual
                  subst newStack
                  exact decodeControlImage_nonempty decodeResult

end Newspeak
