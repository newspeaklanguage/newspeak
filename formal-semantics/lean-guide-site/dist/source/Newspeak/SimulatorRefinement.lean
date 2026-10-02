import Newspeak.TopLevel
import Newspeak.ReflectionCommands

namespace Newspeak

/-!
# Simulator / bytecode refinement boundary

The Newspeak Simulator is an ordinary Newspeak bytecode interpreter, so its
private bytecode instruction set is deliberately not baked into the language
semantics.  This module fixes the observable contract that every installed
compiler/Simulator pair must certify: each program counter denotes the exact
semantic control suspended in that frame, finite Simulator execution weakly
simulates the complete sequential semantics, and a full-speed handoff resumes
from that same represented configuration.
-/

/-- A debugger-visible Simulator frame.  `code` and `pc` are intentionally
    parameters: reflective compiler replacement may install a different code
    representation without changing the semantic contract. -/
structure SimulatorFrameObservation (CodeAddress ProgramCounter : Type) where
  activation : ActivationId
  code : CodeAddress
  pc : ProgramCounter
  operands : EvalStack

/-- Complete observation supplied by the Simulator/debugger API.  Frames are
    ordered bottom-to-top, matching debugger stack images. -/
structure SimulatorObservation (CodeAddress ProgramCounter : Type) where
  allocation : AllocationState
  frames : List (SimulatorFrameObservation CodeAddress ProgramCounter)
  control : ControlTerm
  programVersion : Nat

abbrev SimulatorFrameDecoder (CodeAddress ProgramCounter : Type) :=
  Program → CodeAddress → ProgramCounter → EvalStack → Option FrameControl

/-- Every non-top frame must decode to suspended control and retain the same
    activation identity and evaluation stack. -/
inductive LowerSimulatorFramesRepresent {CodeAddress ProgramCounter : Type}
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) :
    ActivationStack → List (SimulatorFrameObservation CodeAddress ProgramCounter) →
      Prop where
  | empty : LowerSimulatorFramesRepresent decode program .empty []
  | push {stack observations frame observed}
      (rest : LowerSimulatorFramesRepresent decode program stack observations)
      (activation : observed.activation = frame.activation)
      (control : decode program observed.code observed.pc observed.operands =
        some (.suspendedControl frame.frames)) :
      LowerSimulatorFramesRepresent decode program (.push stack frame)
        (observations ++ [observed])

/-- The top PC decodes to the currently executing semantic term; lower PCs
    decode to suspended continuations.  Empty semantic stacks are represented
    by an empty frame list (for example after Top-Halt). -/
inductive SimulatorObservationRepresents {CodeAddress ProgramCounter : Type}
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) (version : Nat) :
    SimulatorObservation CodeAddress ProgramCounter → SequentialConfig → Prop where
  | empty {observation config} :
      observation.allocation = config.allocation →
      observation.frames = [] →
      config.stack = .empty →
      observation.control = config.control →
      observation.programVersion = version →
      SimulatorObservationRepresents decode program version observation config
  | active {observation config rest current lower top} :
      observation.allocation = config.allocation →
      config.stack = .push rest current →
      observation.frames = lower ++ [top] →
      LowerSimulatorFramesRepresent decode program rest lower →
      top.activation = current.activation →
      decode program top.code top.pc top.operands =
        some (.activeControl current.frames config.control) →
      observation.control = config.control →
      observation.programVersion = version →
      SimulatorObservationRepresents decode program version observation config

/-- Reflexive-transitive closure of the complete sequential semantics. -/
inductive Program.SequentialExecution (program : Program)
    (reifier : ErrorReifier program) : SequentialConfig → SequentialConfig → Prop where
  | refl (config : SequentialConfig) :
      program.SequentialExecution reifier config config
  | step {before middle after : SequentialConfig} :
      program.SequentialStepWithTopLevel reifier before middle →
      program.SequentialExecution reifier middle after →
      program.SequentialExecution reifier before after

theorem Program.SequentialExecution.trans {program : Program}
    {reifier : ErrorReifier program} {first second third : SequentialConfig}
    (left : program.SequentialExecution reifier first second)
    (right : program.SequentialExecution reifier second third) :
    program.SequentialExecution reifier first third := by
  induction left with
  | refl => exact right
  | step one remaining inductionHypothesis =>
      exact .step one (inductionHypothesis right)

/-- At least one semantic step, used for instruction-completeness statements
    that must not be discharged by stuttering. -/
inductive Program.NonemptySequentialExecution (program : Program)
    (reifier : ErrorReifier program) : SequentialConfig → SequentialConfig → Prop where
  | single {before after} :
      program.SequentialStepWithTopLevel reifier before after →
      program.NonemptySequentialExecution reifier before after
  | trans {before middle after} :
      program.SequentialStepWithTopLevel reifier before middle →
      program.NonemptySequentialExecution reifier middle after →
      program.NonemptySequentialExecution reifier before after

inductive SimulatorExecution {State : Type} (step : State → State → Prop) :
    State → State → Prop where
  | refl (state : State) : SimulatorExecution step state state
  | step {before middle after} :
      step before middle → SimulatorExecution step middle after →
      SimulatorExecution step before after

inductive NonemptySimulatorExecution {State : Type}
    (step : State → State → Prop) : State → State → Prop where
  | single {before after} : step before after →
      NonemptySimulatorExecution step before after
  | trans {before middle after} : step before middle →
      NonemptySimulatorExecution step middle after →
      NonemptySimulatorExecution step before after

/-- Observable API of one installed Simulator.  `resumeAtFullSpeed` is the
    critical implementation boundary: it extracts exactly the native
    sequential configuration denoted by the current bytecode frames and PCs. -/
structure SimulatorMachine (State CodeAddress ProgramCounter : Type) where
  step : State → State → Prop
  observe : State → Option (SimulatorObservation CodeAddress ProgramCounter)
  resumeAtFullSpeed : State → Option SequentialConfig

def SimulatorMachine.Represents
    {State CodeAddress ProgramCounter : Type}
    (machine : SimulatorMachine State CodeAddress ProgramCounter)
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) (version : Nat) (state : State)
    (config : SequentialConfig) : Prop :=
  ∃ observation,
    machine.observe state = some observation ∧
      SimulatorObservationRepresents decode program version observation config

/-- Proof obligations for one compiler/Simulator artifact.  Soundness permits
    bytecode-level stuttering; completeness requires nonempty Simulator work
    for each semantic step.  The final field rules out any semantic gap at the
    transition back to the native full-speed engine. -/
structure SimulatorRefinementCertificate
    (State CodeAddress ProgramCounter : Type)
    (machine : SimulatorMachine State CodeAddress ProgramCounter)
    (decode : SimulatorFrameDecoder CodeAddress ProgramCounter)
    (program : Program) (version : Nat) (reifier : ErrorReifier program) where
  instructionSound : ∀ {simulatorBefore simulatorAfter semanticBefore},
    machine.Represents decode program version simulatorBefore semanticBefore →
    machine.step simulatorBefore simulatorAfter →
    ∃ semanticAfter,
      program.SequentialExecution reifier semanticBefore semanticAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter
  semanticStepComplete : ∀ {semanticBefore semanticAfter simulatorBefore},
    machine.Represents decode program version simulatorBefore semanticBefore →
    program.SequentialStepWithTopLevel reifier semanticBefore semanticAfter →
    ∃ simulatorAfter,
      NonemptySimulatorExecution machine.step simulatorBefore simulatorAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter
  fullSpeedExact : ∀ {simulator config},
    machine.Represents decode program version simulator config →
    machine.resumeAtFullSpeed simulator = some config

theorem SimulatorExecution.sound
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (certificate : SimulatorRefinementCertificate State CodeAddress
      ProgramCounter machine decode program version reifier)
    {simulatorBefore simulatorAfter : State} {semanticBefore : SequentialConfig}
    (represents :
      machine.Represents decode program version simulatorBefore semanticBefore)
    (execution : SimulatorExecution machine.step simulatorBefore simulatorAfter) :
    ∃ semanticAfter,
      program.SequentialExecution reifier semanticBefore semanticAfter ∧
      machine.Represents decode program version simulatorAfter semanticAfter := by
  induction execution generalizing semanticBefore with
  | refl => exact ⟨semanticBefore, .refl semanticBefore, represents⟩
  | step instruction remaining inductionHypothesis =>
      rcases certificate.instructionSound represents instruction with
        ⟨middle, semanticPrefix, middleRepresents⟩
      rcases inductionHypothesis middleRepresents with
        ⟨semanticAfter, semanticSuffix, finalRepresents⟩
      exact ⟨semanticAfter, semanticPrefix.trans semanticSuffix,
        finalRepresents⟩

theorem SimulatorRefinementCertificate.fullSpeed_preserves_configuration
    {State CodeAddress ProgramCounter : Type}
    {machine : SimulatorMachine State CodeAddress ProgramCounter}
    {decode : SimulatorFrameDecoder CodeAddress ProgramCounter}
    {program : Program} {version : Nat} {reifier : ErrorReifier program}
    (certificate : SimulatorRefinementCertificate State CodeAddress
      ProgramCounter machine decode program version reifier)
    {simulator : State} {config : SequentialConfig}
    (represents : machine.Represents decode program version simulator config) :
    machine.resumeAtFullSpeed simulator = some config :=
  certificate.fullSpeedExact represents

end Newspeak
