import CIL.ExecutionLemmas
import CIL.Safety.InstructionMemory
import UInt256.Representation

open CIL UInt256Model
namespace UInt256Model.Bitwise

inductive Binary where
  | and | or | xor
  deriving DecidableEq

def applyBinary (operation : Binary) (left right : BitVec 256) : BitVec 256 :=
  match operation with
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

end UInt256Model.Bitwise
