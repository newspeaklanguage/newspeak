import Newspeak.CompleteStaticChecking
import Newspeak.PEGCertificateSoundness
import Newspeak.V5Bytecode

namespace Newspeak

/-!
# Metacircular components and artifact admission

The parser, elaborator, compiler, and Simulator are selected ordinary Newspeak
objects.  This file deliberately adds no transition for replacing them:
ordinary evaluation and reflection already mutate their classes, methods, and
slots.  What changes at a use boundary is the artifact admitted from the
currently selected objects.  Admission records the proof obligations that
connect replaceable code to the fixed language semantics.
-/

inductive MetacircularRole where
  | parser
  | elaborator
  | compiler
  | simulator
deriving Repr, DecidableEq, BEq

structure MetacircularComponents (heap : Heap) where
  object : MetacircularRole → ObjectId
  live : ∀ role, ∃ definition,
    heap.objects (object role) = some definition

def MetacircularComponents.reference {heap : Heap}
    (components : MetacircularComponents heap)
    (role : MetacircularRole) : ObjRef :=
  .ordinaryObject (components.object role)

theorem MetacircularComponents.reference_is_live
    {heap : Heap} (components : MetacircularComponents heap)
    (role : MetacircularRole) :
    heap.IsLiveObject (components.reference role) := by
  rcases components.live role with ⟨definition, present⟩
  exact ⟨definition.classId, by simp [MetacircularComponents.reference,
    Heap.classOf, present]⟩

structure ParserArtifactAdmission where
  grammar : PEGGrammar
  decoders : NewspeakLexicalDecoders
  grammarWellFormed : PEGGrammarWellFormed grammar

def newspeakParserArtifactAdmission
    (classes : NewspeakCharacterClasses)
    (decoders : NewspeakLexicalDecoders) : ParserArtifactAdmission :=
  { grammar := newspeakGrammar classes
    decoders := decoders
    grammarWellFormed := newspeakGrammar_wellFormed classes }

structure ElaborationArtifactAdmission
    (derivation : ProgramDerivationServices) : Prop where
  coreSound : ∀ {unit identification program expression},
    derivation.surfaceOK unit identification = true →
    derivation.deriveProgram unit identification = some (program, expression) →
    AnnotatedCoreValid program expression derivation.coreFuel

theorem checkedCompleteElaborationAdmission
    (config : DirectDerivationConfig)
    (artifactConfig : EmbeddedArtifactConfig) (coreFuel : Nat) :
    ElaborationArtifactAdmission
      (checkedCompleteProgramDerivationServices config artifactConfig coreFuel) :=
  { coreSound := by
      intro unit identification program expression checked derived
      exact completeSurfaceStaticOK_coreValid checked derived }

structure FrontEndArtifactAdmission where
  parser : ParserArtifactAdmission
  derivation : ProgramDerivationServices
  elaboration : ElaborationArtifactAdmission derivation

theorem FrontEndArtifactAdmission.accepted_coreValid
    (admission : FrontEndArtifactAdmission)
    {unit : SurfaceCompilationUnit} {identification : IdentificationOutput}
    {program : Program} {expression : CoreExpr}
    (checked : admission.derivation.surfaceOK unit identification = true)
    (derived : admission.derivation.deriveProgram unit identification =
      some (program, expression)) :
    AnnotatedCoreValid program expression admission.derivation.coreFuel :=
  admission.elaboration.coreSound checked derived

structure InstalledFrontEndArtifacts (heap : Heap) where
  components : MetacircularComponents heap
  admission : FrontEndArtifactAdmission

/-- An installed compiler/Simulator pair is admitted only together with its
    semantic refinement certificate. The compiler and Simulator remain the
    ordinary objects named by `components`; their private code and bytecode
    representation are parameters of this boundary. -/
structure CompiledArtifactAdmission
    (State CodeAddress ProgramCounter : Type)
    (machine : SimulatorMachine State CodeAddress ProgramCounter)
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) (version : Nat) (reifier : ErrorReifier program) where
  certificate : SimulatorRefinementCertificate State CodeAddress ProgramCounter
    machine decode program version reifier

theorem CompiledArtifactAdmission.instruction_refines
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (admission : CompiledArtifactAdmission State CodeAddress ProgramCounter
      machine decode program version reifier)
    {simulatorBefore simulatorAfter : State}
    {semanticBefore : SequentialConfig}
    (represents : machine.Represents decode program version simulatorBefore
      semanticBefore)
    (instruction : machine.step simulatorBefore simulatorAfter) :
    ∃ semanticAfter,
      program.SequentialExecution reifier semanticBefore semanticAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter :=
  admission.certificate.instructionSound represents instruction

theorem CompiledArtifactAdmission.execution_refines
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (admission : CompiledArtifactAdmission State CodeAddress ProgramCounter
      machine decode program version reifier)
    {simulatorBefore simulatorAfter : State}
    {semanticBefore : SequentialConfig}
    (represents : machine.Represents decode program version simulatorBefore
      semanticBefore)
    (execution : SimulatorExecution machine.step simulatorBefore simulatorAfter) :
    ∃ semanticAfter,
      program.SequentialExecution reifier semanticBefore semanticAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter :=
  SimulatorExecution.sound admission.certificate represents execution

theorem CompiledArtifactAdmission.semanticStep_implemented
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (admission : CompiledArtifactAdmission State CodeAddress ProgramCounter
      machine decode program version reifier)
    {semanticBefore semanticAfter : SequentialConfig} {simulatorBefore : State}
    (represents : machine.Represents decode program version simulatorBefore
      semanticBefore)
    (semanticStep : program.SequentialStepWithTopLevel reifier semanticBefore
      semanticAfter) :
    ∃ simulatorAfter,
      NonemptySimulatorExecution machine.step simulatorBefore simulatorAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter :=
  admission.certificate.semanticStepComplete represents semanticStep

theorem CompiledArtifactAdmission.fullSpeed_exact
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (admission : CompiledArtifactAdmission State CodeAddress ProgramCounter
      machine decode program version reifier)
    {simulator : State} {config : SequentialConfig}
    (represents : machine.Represents decode program version simulator config) :
    machine.resumeAtFullSpeed simulator = some config :=
  admission.certificate.fullSpeedExact represents

structure InstalledCompiledArtifacts
    (State CodeAddress ProgramCounter : Type)
    (machine : SimulatorMachine State CodeAddress ProgramCounter)
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) (version : Nat) (reifier : ErrorReifier program)
    (heap : Heap) where
  components : MetacircularComponents heap
  admission : CompiledArtifactAdmission State CodeAddress ProgramCounter
    machine decode program version reifier

/-- Admission for one concrete compilation result.  It connects a checked
    annotated-core expression to both the ordinary top-level semantic entry
    and the initial state emitted for the installed Simulator. -/
structure CompiledProgramAdmission
    (State CodeAddress ProgramCounter : Type)
    (machine : SimulatorMachine State CodeAddress ProgramCounter)
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) (version : Nat) (reifier : ErrorReifier program) where
  artifact : CompiledArtifactAdmission State CodeAddress ProgramCounter
    machine decode program version reifier
  expression : CoreExpr
  coreFuel : Nat
  coreValid : AnnotatedCoreValid program expression coreFuel
  sourceAllocation : AllocationState
  semanticInitial : SequentialConfig
  enters : program.TopLevelEntry sourceAllocation expression semanticInitial
  simulatorInitial : State
  representsInitial : machine.Represents decode program version simulatorInitial
    semanticInitial

theorem CompiledProgramAdmission.execution_refines_annotatedCore
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (admission : CompiledProgramAdmission State CodeAddress ProgramCounter
      machine decode program version reifier)
    {simulatorAfter : State}
    (execution : SimulatorExecution machine.step admission.simulatorInitial
      simulatorAfter) :
    ∃ semanticAfter,
      program.SequentialExecution reifier admission.semanticInitial semanticAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter :=
  admission.artifact.execution_refines admission.representsInitial execution

abbrev V5CompiledArtifactAdmission (State : Type)
    (machine : SimulatorMachine State V5.MethodArtifact Nat)
    (program : Program) (version : Nat) (reifier : ErrorReifier program) :=
  CompiledArtifactAdmission State V5.MethodArtifact Nat machine V5.frameDecoder
    program version reifier

end Newspeak
