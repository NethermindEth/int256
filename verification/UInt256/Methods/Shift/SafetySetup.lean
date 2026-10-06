import Extracted
import UInt256.Methods.Shift.Contract
import CIL.Safety.NumericHomes

namespace UInt256Proof.Shift.Safety
open CIL.Safety

/-- Find the extracted numeric shift body, including beneath a public wrapper.
    Its actual instructions and metadata remain checked by the execution proofs. -/
def shiftIndex : Nat := Extracted.program.findIdx fun body =>
  match body.localKinds with
  | [.word32, .word32, .word32, .word64, .word64, .word64, .word64] => true
  | _ => false

def shiftBody : CIL.Method := Extracted.program[shiftIndex]?.getD
  { code := [], locals := [], returnsValue := false }
/-- Discover count and operand sections independently. Every use still checks
    the fetched instruction; intervening output initialization must be executed. -/
def shiftSnapshotPc : Nat :=
  (shiftBody.code.findIdx fun op => match op with | .field _ => true | _ => false) - 1

def shiftPc (inlineAddress : Nat) : Nat :=
  if inlineAddress < 27 then
    inlineAddress + (shiftBody.code.findIdx fun op =>
      match op with | .setLocal 0 => true | _ => false) + 1 - 4
  else shiftSnapshotPc + (inlineAddress - 27)

def shiftCountEnd : Nat := shiftPc 23 + 4

/-- Direction discovery selects proof data only; actual fetched instructions
    and the public left/right binding are still checked by the kernel. -/
def shiftDirection : Direction :=
  match shiftBody.code[shiftPc 46]? with
  | some CIL.Op.shrUn => .right
  | _ => .left

def shiftValue (direction : Direction) (word : BitVec 256) (count : Nat) : BitVec 256 :=
  match direction with
  | .left => word <<< count
  | .right => word >>> count

def shiftSpecs : List NumericLocalSpec := numericSpecs shiftBody

theorem shift_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame shiftBody args memory = .ok (frame, result) ∧
      NumericHomes result memory.nextIdentity shiftSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  numeric_frame_setup shiftBody shiftSpecs (by rfl) (by rfl) (by rfl) memory args wellFormed

#print axioms shift_frame_setup
end UInt256Proof.Shift.Safety
