import UInt256.Methods.StorageScalar

namespace UInt256Proof
open CIL.Safety UInt256Model.Safety

/-- A compiled storage helper writes four limbs and preserves the caller footprint. -/
def StoreLimbsContract (program : CIL.Program) (index : Nat) : Prop :=
  ∀ (memory : Memory) (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64),
    CallingConditions program memory inputs [output] →
    ∃ fuel final,
      invoke program fuel index (StorageScalar.arguments output w0 w1 w2 w3) memory = .ok (final, []) ∧
      CallingConditions program final inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory final ∧
      inputValue final output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read final output 32 1 = .ok bytes)

end UInt256Proof
