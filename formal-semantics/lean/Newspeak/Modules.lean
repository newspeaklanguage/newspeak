import Newspeak.ObjectLiteralsAndNestedClasses

namespace Newspeak
namespace Program

/-- A module definition is exactly an instantiable class created by a
    top-level named-class expression.  Requiring the factory in the class
    record excludes the declaration's metaclass. -/
def ModuleDefinition (program : Program) (heap : Heap)
    (classId : ClassId) : Prop :=
  ∃ definition declaration factory,
    heap.classes classId = some definition ∧
    definition.primaryFactory = some factory ∧
    definition.origin = .expression (.namedClass declaration) ∧
    program.classOwner declaration = .topOwner

def ModuleInstance (program : Program) (heap : Heap)
    (object : ObjRef) : Prop :=
  ∃ classId,
    heap.classOf object = some classId ∧
    program.ModuleDefinition heap classId

/-- The primitive base cases of Newspeak value status.  The later structural
    greatest fixed point may add instances whose immutable contents are also
    values; it cannot remove atomic objects or module definitions. -/
inductive PrimitiveValueObject (program : Program) (heap : Heap) :
    ObjRef → Prop where
  | atom (payload : AtomPayload) :
      PrimitiveValueObject program heap (program.atoms payload)
  | moduleDefinition {classId : ClassId} :
      program.ModuleDefinition heap classId →
      PrimitiveValueObject program heap (.classObject classId)

theorem moduleDefinition_iff_instantiable_topLevelExpression
    (program : Program) (heap : Heap) (classId : ClassId) :
    program.ModuleDefinition heap classId ↔
      ∃ definition declaration factory,
        heap.classes classId = some definition ∧
        definition.primaryFactory = some factory ∧
        definition.origin = .expression (.namedClass declaration) ∧
        program.classOwner declaration = .topOwner := by
  rfl

theorem ModuleDefinition.isClass
    {program : Program} {heap : Heap} {classId : ClassId}
    (moduleDefinition : program.ModuleDefinition heap classId) :
    ∃ definition, heap.classes classId = some definition := by
  rcases moduleDefinition with
    ⟨definition, declaration, factory, present, _factory, _origin, _owner⟩
  exact ⟨definition, present⟩

theorem ModuleDefinition.hasFactory
    {program : Program} {heap : Heap} {classId : ClassId}
    (moduleDefinition : program.ModuleDefinition heap classId) :
    ∃ definition factory,
      heap.classes classId = some definition ∧
      definition.primaryFactory = some factory := by
  rcases moduleDefinition with
    ⟨definition, declaration, factory, present, factoryPresent, _origin,
      _owner⟩
  exact ⟨definition, factory, present, factoryPresent⟩

theorem ModuleDefinition.isPrimitiveValueObject
    {program : Program} {heap : Heap} {classId : ClassId}
    (moduleDefinition : program.ModuleDefinition heap classId) :
    program.PrimitiveValueObject heap (.classObject classId) :=
  .moduleDefinition moduleDefinition

theorem moduleInstance_iff_classIsModuleDefinition
    (program : Program) (heap : Heap) (object : ObjRef) :
    program.ModuleInstance heap object ↔
      ∃ classId,
        heap.classOf object = some classId ∧
        program.ModuleDefinition heap classId := by
  rfl

end Program
end Newspeak
