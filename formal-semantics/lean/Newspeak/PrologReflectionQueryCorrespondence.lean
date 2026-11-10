import Newspeak.ReflectionQueries
import Newspeak.PrologLookupCorrespondence

namespace Newspeak
namespace PrologBridge

/-! Direct Horn-clause readings of the target and result equations for every
reflection query constructor.  Unlike the older proof-carrying application in
`PrologReflectionCorrespondence`, these relations expose every lookup premise. -/

inductive PrologReflectionQueryTarget (world : ActorWorld) :
    ReflectionQuery → MirrorTarget → Prop where
  | inspectVM {mirror} :
      PrologReflectionQueryTarget world (.inspectVM mirror) (.vmTarget world.vm)
  | inspectProgram {mirror} :
      PrologReflectionQueryTarget world (.inspectProgram mirror) .programTarget
  | inspectMixin {mirror mixin} :
      PrologReflectionQueryTarget world (.inspectMixin mirror mixin) (.mixinTarget mixin)
  | inspectMethod {mirror method} :
      PrologReflectionQueryTarget world (.inspectMethod mirror method) (.methodTarget method)
  | inspectClass {mirror classId} :
      PrologReflectionQueryTarget world (.inspectClass mirror classId) (.classTarget classId)
  | inspectObject {mirror object} :
      PrologReflectionQueryTarget world (.inspectObject mirror object) (.objectTarget object)
  | inspectActivation {mirror activation} :
      PrologReflectionQueryTarget world (.inspectActivation mirror activation)
        (.activationTarget activation)
  | inspectActor {mirror actor} :
      PrologReflectionQueryTarget world (.inspectActor mirror actor) (.actorTarget actor)
  | enumerateInstancesOf {mirror classId} :
      PrologReflectionQueryTarget world (.enumerateInstancesOf mirror classId)
        (.classTarget classId)
  | enumerateApplicationsOf {mirror mixin} :
      PrologReflectionQueryTarget world (.enumerateApplicationsOf mirror mixin)
        (.mixinTarget mixin)

theorem prologReflectionQueryTarget_iff {world query target} :
    PrologReflectionQueryTarget world query target ↔
      query.authorizationTarget world = target := by
  constructor
  · intro derivation
    cases derivation <;> rfl
  · intro equality
    cases query <;> simp [ReflectionQuery.authorizationTarget] at equality <;>
      subst target <;> constructor

inductive PrologReflectionQueryResult (world : ActorWorld) :
    ReflectionQuery → ReflectionQueryResult → Prop where
  | inspectVM {mirror} :
      PrologReflectionQueryResult world (.inspectVM mirror)
        (.vm world.vm world.programVersion)
  | inspectProgram {mirror} :
      PrologReflectionQueryResult world (.inspectProgram mirror) (.program world.program)
  | inspectMixin {mirror mixin definition} :
      world.program.mixins mixin = some definition →
      PrologReflectionQueryResult world (.inspectMixin mirror mixin) (.mixin definition)
  | inspectMethod {mirror method mixin definition body} :
      world.program.findMethodDefinition method world.program.mixins.domain =
        some (mixin, definition) →
      world.program.methodBodies method = some body →
      PrologReflectionQueryResult world (.inspectMethod mirror method)
        (.method ⟨mixin, definition, body, world.program.methodLocals method⟩)
  | inspectClass {mirror classId location heap definition} :
      world.locateClassId classId = some location →
      world.heapAt location = some heap →
      heap.classes classId = some definition →
      PrologReflectionQueryResult world (.inspectClass mirror classId)
        (.class ⟨location, definition⟩)
  | inspectObject {mirror object location heap classId} :
      world.locateObjectReference object = some location →
      world.heapAt location = some heap →
      heap.classOf object = some classId →
      PrologReflectionQueryResult world (.inspectObject mirror object)
        (.object ⟨location, classId⟩)
  | inspectActivation {mirror activation location heap definition} :
      world.locateActivationId activation = some location →
      world.heapAt location = some heap →
      heap.activations activation = some definition →
      PrologReflectionQueryResult world (.inspectActivation mirror activation)
        (.activation ⟨location, definition⟩)
  | inspectActor {mirror actor allocation} :
      world.actorAllocations actor = some allocation →
      PrologReflectionQueryResult world (.inspectActor mirror actor)
        (.actor ⟨allocation, world.runStates actor⟩)
  | enumerateInstancesOf {mirror classId location} :
      world.locateClassId classId = some location →
      PrologReflectionQueryResult world (.enumerateInstancesOf mirror classId)
        (.instances (world.allCohortInstancesOf classId))
  | enumerateApplicationsOf {mirror mixin definition} :
      world.program.mixins mixin = some definition →
      PrologReflectionQueryResult world (.enumerateApplicationsOf mirror mixin)
        (.applications (world.allCohortApplicationsOf mixin))

theorem prologReflectionQueryResult_iff {world query result} :
    PrologReflectionQueryResult world query result ↔
      query.execute world = some result := by
  constructor
  · intro derivation
    cases derivation with
    | inspectVM | inspectProgram => rfl
    | inspectMixin lookup => simp [ReflectionQuery.execute, lookup]
    | inspectMethod owner body => simp [ReflectionQuery.execute, owner, body]
    | inspectClass location heap definition =>
        simp [ReflectionQuery.execute, location, heap, definition]
    | inspectObject location heap classId =>
        simp [ReflectionQuery.execute, location, heap, classId]
    | inspectActivation location heap definition =>
        simp [ReflectionQuery.execute, location, heap, definition]
    | inspectActor allocation => simp [ReflectionQuery.execute, allocation]
    | enumerateInstancesOf location => simp [ReflectionQuery.execute, location]
    | enumerateApplicationsOf definition => simp [ReflectionQuery.execute, definition]
  · intro execution
    cases query with
    | inspectVM mirror =>
        simp [ReflectionQuery.execute] at execution
        subst result
        exact .inspectVM
    | inspectProgram mirror =>
        simp [ReflectionQuery.execute] at execution
        subst result
        exact .inspectProgram
    | inspectMixin mirror mixin =>
        simp only [ReflectionQuery.execute] at execution
        cases lookup : world.program.mixins mixin with
        | none => simp [lookup] at execution
        | some definition =>
            simp [lookup] at execution
            subst result
            exact .inspectMixin lookup
    | inspectMethod mirror method =>
        simp only [ReflectionQuery.execute] at execution
        cases owner : world.program.findMethodDefinition method world.program.mixins.domain with
        | none => simp [owner] at execution
        | some pair =>
            rcases pair with ⟨mixin, definition⟩
            cases body : world.program.methodBodies method with
            | none => simp [owner, body] at execution
            | some statements =>
                simp [owner, body] at execution
                subst result
                exact .inspectMethod owner body
    | inspectClass mirror classId =>
        simp only [ReflectionQuery.execute] at execution
        cases location : world.locateClassId classId with
        | none => simp [location] at execution
        | some place =>
            cases heap : world.heapAt place with
            | none => simp [location, heap] at execution
            | some storage =>
                cases definition : storage.classes classId with
                | none => simp [location, heap, definition] at execution
                | some classDef =>
                    simp [location, heap, definition] at execution
                    subst result
                    exact .inspectClass location heap definition
    | inspectObject mirror object =>
        simp only [ReflectionQuery.execute] at execution
        cases location : world.locateObjectReference object with
        | none => simp [location] at execution
        | some place =>
            cases heap : world.heapAt place with
            | none => simp [location, heap] at execution
            | some storage =>
                cases classId : storage.classOf object with
                | none => simp [location, heap, classId] at execution
                | some classValue =>
                    simp [location, heap, classId] at execution
                    subst result
                    exact .inspectObject location heap classId
    | inspectActivation mirror activation =>
        simp only [ReflectionQuery.execute] at execution
        cases location : world.locateActivationId activation with
        | none => simp [location] at execution
        | some place =>
            cases heap : world.heapAt place with
            | none => simp [location, heap] at execution
            | some storage =>
                cases definition : storage.activations activation with
                | none => simp [location, heap, definition] at execution
                | some activationDef =>
                    simp [location, heap, definition] at execution
                    subst result
                    exact .inspectActivation location heap definition
    | inspectActor mirror actor =>
        simp only [ReflectionQuery.execute] at execution
        cases allocation : world.actorAllocations actor with
        | none => simp [allocation] at execution
        | some state =>
            simp [allocation] at execution
            subst result
            exact .inspectActor allocation
    | enumerateInstancesOf mirror classId =>
        simp only [ReflectionQuery.execute] at execution
        cases location : world.locateClassId classId with
        | none => simp [location] at execution
        | some place =>
            simp [location] at execution
            subst result
            exact .enumerateInstancesOf location
    | enumerateApplicationsOf mirror mixin =>
        simp only [ReflectionQuery.execute] at execution
        cases definition : world.program.mixins mixin with
        | none => simp [definition] at execution
        | some mixinDef =>
            simp [definition] at execution
            subst result
            exact .enumerateApplicationsOf definition

end PrologBridge
end Newspeak
