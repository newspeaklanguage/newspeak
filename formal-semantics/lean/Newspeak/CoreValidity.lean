import Newspeak.TopLevel

namespace Newspeak

def Program.knowsClassDeclaration (program : Program)
    (declaration : ClassDeclId) : Bool :=
  (program.classBodies declaration).isSome ||
    (program.mixinApplications declaration).isSome

def Program.knowsClosureDeclaration (program : Program)
    (declaration : ActivationDeclId) : Bool :=
  (program.closureBodies declaration).isSome

def optionalClassDeclarationKnown (program : Program) :
    Option ClassDeclId → Bool
  | none => true
  | some declaration => program.knowsClassDeclaration declaration

mutual
  def coreExpressionAnnotationsOK (program : Program) :
      Nat → Bool → CoreExpr → Bool
    | 0, _, _ => false
    | fuel + 1, allowSuper, expression =>
      match expression with
      | .value _ | .selfValue | .atom _ | .readLocal _ _
      | .readSlot _ _ | .currentRead _ | .newInstanceCurrent _ _ => true
      | .ordinarySend receiver _ arguments
      | .eventualSend receiver _ arguments =>
          coreExpressionAnnotationsOK program fuel allowSuper receiver &&
            arguments.all (coreExpressionAnnotationsOK program fuel allowSuper)
      | .implicitSend selector arguments annotation immediate =>
          (match annotation with
           | none => true
           | some scope => program.declares scope selector) &&
          optionalClassDeclarationKnown program immediate &&
          arguments.all (coreExpressionAnnotationsOK program fuel allowSuper)
      | .selfSend _ arguments immediate =>
          program.knowsClassDeclaration immediate &&
            arguments.all (coreExpressionAnnotationsOK program fuel allowSuper)
      | .outerSend _ arguments target immediate =>
          program.knowsClassDeclaration target &&
          program.knowsClassDeclaration immediate &&
            arguments.all (coreExpressionAnnotationsOK program fuel allowSuper)
      | .superSend _ arguments =>
          allowSuper &&
            arguments.all (coreExpressionAnnotationsOK program fuel allowSuper)
      | .closureLiteral declaration =>
          program.knowsClosureDeclaration declaration
      | .cascadeClosure descriptor clauses =>
          program.knowsClosureDeclaration descriptor.closureDeclaration &&
            coreClauseAnnotationsOK program fuel allowSuper clauses
      | .writeLocal _ _ value | .writeSlot _ _ value
      | .currentWrite _ value | .lazyRead _ value =>
          coreExpressionAnnotationsOK program fuel allowSuper value
      | .classBody declaration superclass =>
          (program.classBodies declaration).isSome &&
            coreExpressionAnnotationsOK program fuel allowSuper superclass
      | .mixinApply declaration superclass mixinSource =>
          (program.mixinApplications declaration).isSome &&
          coreExpressionAnnotationsOK program fuel allowSuper superclass &&
          coreExpressionAnnotationsOK program fuel allowSuper mixinSource
      | .objectLiteral declaration superclass =>
          (program.objectLiterals declaration).isSome &&
            coreExpressionAnnotationsOK program fuel allowSuper superclass
      | .tuple _ descriptor elements =>
          program.knowsClosureDeclaration descriptor.closureDeclaration &&
            elements.all (coreExpressionAnnotationsOK program fuel allowSuper)
      | .pattern pattern annotation immediate =>
          (match annotation with
           | none => true
           | some scope => program.declares scope ⟨"Pattern"⟩) &&
          optionalClassDeclarationKnown program immediate &&
          corePatternAnnotationsOK program fuel allowSuper pattern
      | .cascade descriptor receiver clauses =>
          program.knowsClosureDeclaration descriptor.closureDeclaration &&
          coreExpressionAnnotationsOK program fuel allowSuper receiver &&
          coreClauseAnnotationsOK program fuel allowSuper clauses
      | .nestedClass declaration classExpression =>
          program.knowsClassDeclaration declaration &&
            coreExpressionAnnotationsOK program fuel allowSuper classExpression

  def corePatternAnnotationsOK (program : Program) :
      Nat → Bool → CorePattern → Bool
    | 0, _, _ => false
    | fuel + 1, allowSuper, pattern =>
      match pattern with
      | .wildcard => true
      | .literal expression =>
          coreExpressionAnnotationsOK program fuel allowSuper expression
      | .variable site => (program.patternVariable site).isSome
      | .nested nested => corePatternAnnotationsOK program fuel allowSuper nested
      | .keyword _ keywordDescriptor _ componentDescriptor pairs =>
          program.knowsClosureDeclaration
            keywordDescriptor.closureDeclaration &&
          program.knowsClosureDeclaration
            componentDescriptor.closureDeclaration &&
          pairs.all fun pair =>
            corePatternAnnotationsOK program fuel allowSuper pair.2

  def coreClauseAnnotationsOK (program : Program) :
      Nat → Bool → List (Selector × List CoreExpr) → Bool
    | 0, _, _ => false
    | _, _, [] => true
    | fuel + 1, allowSuper, (_, arguments) :: remaining =>
        arguments.all (coreExpressionAnnotationsOK program fuel allowSuper) &&
          coreClauseAnnotationsOK program fuel allowSuper remaining
end

def coreStatementAnnotationsOK (program : Program) (fuel : Nat)
    (allowSuper : Bool) : Statement → Bool
  | .expression expression | .return expression =>
      coreExpressionAnnotationsOK program fuel allowSuper expression

def coreStatementsAnnotationsOK (program : Program) (fuel : Nat)
    (allowSuper : Bool) (statements : List Statement) : Bool :=
  statements.all (coreStatementAnnotationsOK program fuel allowSuper)

def Program.DeclarationMixinInjective (program : Program) : Prop :=
  ∀ {first second mixin},
    program.declMixin first = some mixin →
    program.declMixin second = some mixin → first = second

def Program.declarationMixinInjectiveOK (program : Program) : Bool :=
  program.declMixin.domain.all fun first =>
    program.declMixin.domain.all fun second =>
      match program.declMixin first, program.declMixin second with
      | some firstMixin, some secondMixin =>
          decide (firstMixin ≠ secondMixin) || decide (first = second)
      | _, _ => true

theorem Program.declarationMixinInjectiveOK_sound
    {program : Program}
    (checked : program.declarationMixinInjectiveOK = true) :
    program.DeclarationMixinInjective := by
  intro first second mixin firstFound secondFound
  have firstMember := FiniteStore.mem_domain_of_lookup_eq_some firstFound
  have secondMember := FiniteStore.mem_domain_of_lookup_eq_some secondFound
  have firstCheck := (List.all_eq_true.mp checked) first firstMember
  have pairCheck := (List.all_eq_true.mp firstCheck) second secondMember
  simp [firstFound, secondFound] at pairCheck
  exact pairCheck

def Program.topLevelExpressionOK (program : Program) : Nat → CoreExpr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      match expression with
      | .atom _ | .closureLiteral _ => true
      | .tuple _ _ elements =>
          elements.all (program.topLevelExpressionOK fuel)
      | .objectLiteral declaration _ =>
          decide (program.objectLiteralOwner declaration = .topOwner)
      | .classBody declaration _ | .mixinApply declaration _ _ =>
          decide (program.classOwner declaration = .topOwner)
      | .ordinarySend receiver _ arguments =>
          program.topLevelExpressionOK fuel receiver &&
            arguments.all (program.topLevelExpressionOK fuel)
      | _ => false

theorem Program.topLevelExpressionOK_sound
    {program : Program} {fuel : Nat} {expression : CoreExpr}
    (checked : program.topLevelExpressionOK fuel expression = true) :
    program.TopLevelExpression expression := by
  induction fuel generalizing expression with
  | zero => simp [Program.topLevelExpressionOK] at checked
  | succ fuel ih =>
      cases expression <;>
        simp only [Program.topLevelExpressionOK] at checked
      case atom payload => exact .atom payload
      case closureLiteral declaration => exact .closure declaration
      case tuple site descriptor elements =>
        exact .tuple fun element member =>
          ih ((List.all_eq_true.mp checked) element member)
      case objectLiteral declaration superclass =>
        exact .objectLiteral (of_decide_eq_true checked)
      case classBody declaration superclass =>
        exact .classBody (of_decide_eq_true checked)
      case mixinApply declaration superclass source =>
        exact .mixinApply (of_decide_eq_true checked)
      case ordinarySend receiver selector arguments =>
        have parts := Bool.and_eq_true_iff.mp checked
        exact .ordinarySend (ih parts.1) fun argument member =>
          ih ((List.all_eq_true.mp parts.2) argument member)
      all_goals simp_all

def localDeclarationAnnotationsOK (program : Program) (fuel : Nat) :
    LocalDeclaration → Bool
  | .immutable _ initializer | .mutableInitialized _ initializer
  | .lazyImmutable _ initializer | .lazyMutable _ initializer =>
      coreExpressionAnnotationsOK program fuel true initializer
  | .mutableUninitialized _ => true

def localDeclarationGroupAnnotationsOK (program : Program) (fuel : Nat) :
    LocalDeclarationGroup → Bool
  | .sequential declaration =>
      localDeclarationAnnotationsOK program fuel declaration
  | .simultaneous declarations =>
      declarations.all (localDeclarationAnnotationsOK program fuel)

def slotDeclarationAnnotationsOK (program : Program) (fuel : Nat) :
    SlotDeclaration → Bool
  | .immutable _ initializer _ | .mutableInitialized _ initializer _ =>
      coreExpressionAnnotationsOK program fuel true initializer
  | .mutableUninitialized _ => true

def slotDeclarationGroupAnnotationsOK (program : Program) (fuel : Nat) :
    SlotDeclarationGroup → Bool
  | .sequential declarations | .simultaneous declarations =>
      declarations.all (slotDeclarationAnnotationsOK program fuel)

def messageTemplateAnnotationsOK (program : Program) (fuel : Nat)
    (message : MessageTemplate) : Bool :=
  message.arguments.all (coreExpressionAnnotationsOK program fuel true)

def Program.programAnnotationsOK (program : Program) (fuel : Nat) : Bool :=
  program.methodBodies.domain.all (fun method =>
    match program.methodBodies method with
    | none => false
    | some body =>
        (program.methodLocals method).all
          (localDeclarationGroupAnnotationsOK program fuel) &&
        coreStatementsAnnotationsOK program fuel true body) &&
  program.closureBodies.domain.all (fun closure =>
    match program.closureBodies closure with
    | none => false
    | some body =>
        (program.closureLocals closure).all
          (localDeclarationGroupAnnotationsOK program fuel) &&
        coreStatementsAnnotationsOK program fuel true body) &&
  program.mixins.domain.all (fun mixin =>
    match program.mixins mixin with
    | none => false
    | some definition =>
        definition.initializerGroups.all
          (slotDeclarationGroupAnnotationsOK program fuel) &&
        coreStatementsAnnotationsOK program fuel true
          definition.initializerBody) &&
  program.patternVariable.domain.all (fun site =>
    match program.patternVariable site with
    | none => false
    | some expression =>
        coreExpressionAnnotationsOK program fuel true expression) &&
  program.classBodies.domain.all (fun declaration =>
    match program.classBodies declaration with
    | none => false
    | some descriptor =>
        messageTemplateAnnotationsOK program fuel descriptor.superclassMessage) &&
  program.mixinApplications.domain.all (fun declaration =>
    match program.mixinApplications declaration with
    | none => false
    | some descriptor =>
        messageTemplateAnnotationsOK program fuel descriptor.superclassMessage &&
        messageTemplateAnnotationsOK program fuel descriptor.mixinMessage) &&
  program.objectLiterals.domain.all (fun declaration =>
    match program.objectLiterals declaration with
    | none => false
    | some descriptor =>
        messageTemplateAnnotationsOK program fuel descriptor.superclassMessage) &&
  program.actorSeeds.domain.all (fun mixin =>
    match program.actorSeeds mixin with
    | none => false
    | some descriptor =>
        messageTemplateAnnotationsOK program fuel descriptor.superclassMessage)

def annotatedCoreValidCheck (program : Program) (expression : CoreExpr)
    (fuel : Nat) : Bool :=
  program.declarationMixinInjectiveOK &&
    program.programAnnotationsOK fuel &&
    coreExpressionAnnotationsOK program fuel false expression &&
    program.topLevelExpressionOK fuel expression

structure AnnotatedCoreValid (program : Program) (expression : CoreExpr)
    (fuel : Nat) : Prop where
  declarationMixinInjective : program.DeclarationMixinInjective
  programAnnotations : program.programAnnotationsOK fuel = true
  annotations : coreExpressionAnnotationsOK program fuel false expression = true
  topLevel : program.TopLevelExpression expression

theorem annotatedCoreValidCheck_sound
    {program : Program} {expression : CoreExpr} {fuel : Nat}
    (checked : annotatedCoreValidCheck program expression fuel = true) :
    AnnotatedCoreValid program expression fuel := by
  simp only [annotatedCoreValidCheck, Bool.and_eq_true] at checked
  exact
    { declarationMixinInjective :=
        program.declarationMixinInjectiveOK_sound checked.1.1.1
      programAnnotations := checked.1.1.2
      annotations := checked.1.2
      topLevel := program.topLevelExpressionOK_sound checked.2 }

theorem AnnotatedCoreValid.topLevelExpression
    {program : Program} {expression : CoreExpr} {fuel : Nat}
    (valid : AnnotatedCoreValid program expression fuel) :
    program.TopLevelExpression expression :=
  valid.topLevel

end Newspeak
