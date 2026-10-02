import Newspeak.SimulatorRefinement

namespace Newspeak

namespace V5

inductive SendKind where
  | ordinary
  | self
  | implicitReceiver
  | super
  | eventual
  | outer (depth : Nat)
deriving Repr, DecidableEq

inductive ReturnValue where
  | nil
  | falseObject
  | trueObject
  | self
  | top
deriving Repr, DecidableEq

/-- Logical V5 instructions.  Short and wide encodings intentionally decode
    to the same constructor; encoding size remains visible in `Decoded`. -/
inductive Instruction where
  | branchBack (delta : Nat)
  | branch (delta : Nat)
  | branchIfTrue (delta : Nat)
  | branchIfFalse (delta : Nat)
  | send (kind : SendKind) (selectorIndex arity : Nat)
  | commonSend (index : Nat)
  | pushParameter (index : Nat)
  | pushLocal (index : Nat)
  | popIntoLocal (index : Nat)
  | storeIntoLocal (index : Nat)
  | pushIndirectLocal (index vectorLocal : Nat)
  | popIntoIndirectLocal (index vectorLocal : Nat)
  | storeIntoIndirectLocal (index vectorLocal : Nat)
  | pushLiteral (index : Nat)
  | pushNil
  | pushFalse
  | pushTrue
  | pushSelf
  | pushMixin
  | pop
  | dup
  | pushInteger (value : Int)
  | pushNewArray (size : Nat)
  | pushNewArrayWithElements (size : Nat)
  | pushEnclosingObject (depth : Nat)
  | pushClosure (copiedCount arity bodySize : Nat)
  | localReturn (value : ReturnValue)
  | nonLocalReturn (value : ReturnValue)
deriving Repr, DecidableEq

structure Decoded where
  instruction : Instruction
  size : Nat
deriving Repr, DecidableEq

def byteAt (bytes : List Nat) (index : Nat) : Option Nat := do
  let byte ← bytes[index]?
  guard (byte < 256)
  some byte

def littleEndian16 (low high : Nat) : Nat := low + 256 * high

def signed16 (low high : Nat) : Int :=
  let unsigned := littleEndian16 low high
  if unsigned < 32768 then Int.ofNat unsigned
  else Int.ofNat unsigned - 65536

def decodeExtendedSendOperands (low packed : Nat) : Nat × Nat :=
  (low + 256 * (packed % 16), packed / 16)

/-- Complete decoder for every live V5 opcode in the local V5 specification.
    Dead/corrupt opcodes and truncated operands return `none`. -/
def decodeAt (bytes : List Nat) (pc : Nat) : Option Decoded := do
  let opcode ← byteAt bytes pc
  if opcode < 16 then
    some ⟨.branchBack opcode, 1⟩
  else if opcode < 32 then
    some ⟨.branch (opcode - 16), 1⟩
  else if opcode < 48 then
    some ⟨.branchIfTrue (opcode - 32), 1⟩
  else if opcode < 64 then
    some ⟨.branchIfFalse (opcode - 48), 1⟩
  else if opcode < 80 then
    some ⟨.send .ordinary (opcode % 8) ((opcode - 64) / 8), 1⟩
  else if opcode < 96 then
    some ⟨.send .self (opcode % 8) ((opcode - 80) / 8), 1⟩
  else if opcode < 112 then
    some ⟨.send .implicitReceiver (opcode % 8) ((opcode - 96) / 8), 1⟩
  else if opcode < 120 then
    some ⟨.pushParameter (opcode - 112), 1⟩
  else if opcode < 128 then
    some ⟨.pushLocal (opcode - 120), 1⟩
  else if opcode < 136 then
    some ⟨.popIntoLocal (opcode - 128), 1⟩
  else if opcode < 144 then
    some ⟨.storeIntoLocal (opcode - 136), 1⟩
  else if opcode < 152 then
    some ⟨.pushLiteral (opcode - 144), 1⟩
  else match opcode with
    | 152 => some ⟨.pushNil, 1⟩
    | 153 => some ⟨.pushFalse, 1⟩
    | 154 => some ⟨.pushTrue, 1⟩
    | 155 => some ⟨.pushSelf, 1⟩
    | 156 => some ⟨.pushMixin, 1⟩
    | 158 => some ⟨.pop, 1⟩
    | 159 => some ⟨.dup, 1⟩
    | 160 => some ⟨.pushInteger (-1), 1⟩
    | 161 => some ⟨.pushInteger 0, 1⟩
    | 162 => some ⟨.pushInteger 1, 1⟩
    | 163 => some ⟨.pushInteger 2, 1⟩
    | 166 => some ⟨.localReturn .nil, 1⟩
    | 167 => some ⟨.localReturn .falseObject, 1⟩
    | 168 => some ⟨.localReturn .trueObject, 1⟩
    | 169 => some ⟨.localReturn .self, 1⟩
    | 170 => some ⟨.localReturn .top, 1⟩
    | 171 => some ⟨.nonLocalReturn .nil, 1⟩
    | 172 => some ⟨.nonLocalReturn .falseObject, 1⟩
    | 173 => some ⟨.nonLocalReturn .trueObject, 1⟩
    | 174 => some ⟨.nonLocalReturn .self, 1⟩
    | 175 => some ⟨.nonLocalReturn .top, 1⟩
    | opcode =>
        if opcode < 208 then
          some ⟨.commonSend (opcode - 176), 1⟩
        else match opcode with
          | 222 => do
              let size ← byteAt bytes (pc + 1)
              some ⟨.pushNewArray size, 2⟩
          | 223 => do
              let size ← byteAt bytes (pc + 1)
              some ⟨.pushNewArrayWithElements size, 2⟩
          | 228 => do
              let index ← byteAt bytes (pc + 1)
              some ⟨.pushParameter index, 2⟩
          | 229 => do
              let index ← byteAt bytes (pc + 1)
              some ⟨.pushLocal index, 2⟩
          | 230 => do
              let index ← byteAt bytes (pc + 1)
              some ⟨.popIntoLocal index, 2⟩
          | 231 => do
              let index ← byteAt bytes (pc + 1)
              some ⟨.storeIntoLocal index, 2⟩
          | 233 => do
              let depth ← byteAt bytes (pc + 1)
              guard (0 < depth)
              some ⟨.pushEnclosingObject depth, 2⟩
          | 239 => do
              let low ← byteAt bytes (pc + 1)
              let packed ← byteAt bytes (pc + 2)
              let operands := decodeExtendedSendOperands low packed
              some ⟨.send .eventual operands.1 operands.2, 3⟩
          | 240 | 241 | 242 | 243 => do
              let low ← byteAt bytes (pc + 1)
              let high ← byteAt bytes (pc + 2)
              let delta := littleEndian16 low high
              let instruction := match opcode with
                | 240 => Instruction.branchBack delta
                | 241 => Instruction.branch delta
                | 242 => Instruction.branchIfTrue delta
                | _ => Instruction.branchIfFalse delta
              some ⟨instruction, 3⟩
          | 245 | 246 | 247 => do
              let index ← byteAt bytes (pc + 1)
              let vector ← byteAt bytes (pc + 2)
              let instruction := match opcode with
                | 245 => Instruction.pushIndirectLocal index vector
                | 246 => Instruction.popIntoIndirectLocal index vector
                | _ => Instruction.storeIntoIndirectLocal index vector
              some ⟨instruction, 3⟩
          | 248 => do
              let low ← byteAt bytes (pc + 1)
              let high ← byteAt bytes (pc + 2)
              some ⟨.pushLiteral (littleEndian16 low high), 3⟩
          | 249 => do
              let low ← byteAt bytes (pc + 1)
              let high ← byteAt bytes (pc + 2)
              some ⟨.pushInteger (signed16 low high), 3⟩
          | 250 | 251 | 252 | 253 => do
              let low ← byteAt bytes (pc + 1)
              let packed ← byteAt bytes (pc + 2)
              let operands := decodeExtendedSendOperands low packed
              let kind := match opcode with
                | 250 => SendKind.ordinary
                | 251 => SendKind.self
                | 252 => SendKind.super
                | _ => SendKind.implicitReceiver
              some ⟨.send kind operands.1 operands.2, 3⟩
          | 254 => do
              let low ← byteAt bytes (pc + 1)
              let packed ← byteAt bytes (pc + 2)
              let depth ← byteAt bytes (pc + 3)
              let operands := decodeExtendedSendOperands low packed
              some ⟨.send (.outer depth) operands.1 operands.2, 4⟩
          | 255 => do
              let counts ← byteAt bytes (pc + 1)
              let low ← byteAt bytes (pc + 2)
              let high ← byteAt bytes (pc + 3)
              some ⟨.pushClosure (counts / 16) (counts % 16)
                (littleEndian16 low high), 4⟩
          | _ => none

theorem decodeAt_deterministic {bytes : List Nat} {pc : Nat}
    {first second : Decoded}
    (left : decodeAt bytes pc = some first)
    (right : decodeAt bytes pc = some second) : first = second := by
  rw [left] at right
  exact Option.some.inj right

theorem decodeExtendedSendOperands_bounds {low packed : Nat}
    (lowByte : low < 256) (packedByte : packed < 256) :
    (decodeExtendedSendOperands low packed).1 ≤ 4095 ∧
      (decodeExtendedSendOperands low packed).2 ≤ 15 := by
  simp [decodeExtendedSendOperands]
  omega

/-- PCs obtained by parsing forward from byte zero.  This is deliberately a
    property of the byte stream, not of the control-flow graph: branch targets
    and closure bodies are checked separately by the compiler artifact. -/
inductive InstructionBoundary (bytes : List Nat) : Nat → Prop where
  | entry : InstructionBoundary bytes 0
  | next {pc : Nat} {decoded : Decoded} :
      InstructionBoundary bytes pc →
      decodeAt bytes pc = some decoded →
      InstructionBoundary bytes (pc + decoded.size)

/-- A compiled V5 method carries the semantic PC map needed by the debugger.
    Opcode decoding alone cannot recover a source/core continuation: that map
    is an output of the installed compiler and therefore part of the
    replaceable compiler/Simulator artifact. -/
structure MethodArtifact where
  bytes : List Nat
  controlPoints : List Nat
  controlAt : Nat → EvalStack → FrameControl

/-- The artifact decoder accepts exactly declared control points whose first
    byte begins a live, non-truncated V5 instruction. -/
def frameDecoder : SimulatorFrameDecoder MethodArtifact Nat :=
  fun _program artifact pc operands =>
    if pc ∈ artifact.controlPoints then
      (decodeAt artifact.bytes pc).map fun _ => artifact.controlAt pc operands
    else none

/-- Static obligations discharged by one compiler-emitted method artifact.
    The source map contains every in-range parsed boundary and no spurious or
    undecodable PC. -/
structure MethodArtifact.WellFormed (artifact : MethodArtifact) : Prop where
  controlPointsNodup : artifact.controlPoints.Nodup
  controlPointSound : ∀ {pc}, pc ∈ artifact.controlPoints →
    InstructionBoundary artifact.bytes pc ∧
      ∃ decoded, decodeAt artifact.bytes pc = some decoded
  controlPointComplete : ∀ {pc},
    InstructionBoundary artifact.bytes pc → pc < artifact.bytes.length →
      pc ∈ artifact.controlPoints

theorem frameDecoder_eq_some_iff (artifact : MethodArtifact) (program : Program)
    (pc : Nat) (operands : EvalStack) (control : FrameControl) :
    frameDecoder program artifact pc operands = some control ↔
      pc ∈ artifact.controlPoints ∧
      (∃ decoded, decodeAt artifact.bytes pc = some decoded) ∧
      artifact.controlAt pc operands = control := by
  by_cases member : pc ∈ artifact.controlPoints
  · cases decodes : decodeAt artifact.bytes pc with
    | none => simp [frameDecoder, member, decodes]
    | some decoded => simp [frameDecoder, member, decodes]
  · simp [frameDecoder, member]

theorem MethodArtifact.WellFormed.frameDecoder_defined_iff_boundary
    {artifact : MethodArtifact} (valid : artifact.WellFormed)
    (program : Program) (pc : Nat) (inRange : pc < artifact.bytes.length)
    (operands : EvalStack) :
    (∃ control, frameDecoder program artifact pc operands = some control) ↔
      InstructionBoundary artifact.bytes pc := by
  constructor
  · rintro ⟨control, decoded⟩
    have member := (frameDecoder_eq_some_iff artifact program pc operands control).mp
      decoded
    exact (valid.controlPointSound member.1).1
  · intro boundary
    have member := valid.controlPointComplete boundary inRange
    rcases (valid.controlPointSound member).2 with ⟨decoded, decodes⟩
    exact ⟨artifact.controlAt pc operands,
      (frameDecoder_eq_some_iff artifact program pc operands _).mpr
        ⟨member, ⟨decoded, decodes⟩, rfl⟩⟩

end V5

end Newspeak
