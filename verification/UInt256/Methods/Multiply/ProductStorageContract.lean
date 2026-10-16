import UInt256.Safety.OutputAccess
import CIL.Safety.AccessBelow
namespace UInt256Proof.Multiply.ProductStorage
open CIL.Safety UInt256Model.Safety
def Contract (program : CIL.Program) (index : Nat) : Prop :=
  ∀ (memory : Memory) (inputs : List Reference) (output : Reference)
  (w0 w1 w2 w3 : BitVec 64)
  (_call : CallingConditions program memory inputs [output]),
  ∃ fuel result,
    invoke program fuel index
      [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]
      memory = .ok (result, []) ∧
    CallingConditions program result inputs [output] ∧
    (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
    AccessBelow memory.nextIdentity memory result ∧
    inputValue result output = BitVec.ofNat 256
      (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
    (∃ bytes, read result output 32 1 = .ok bytes)

end UInt256Proof.Multiply.ProductStorage
