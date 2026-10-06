import UInt256.Safety.Contract
import UInt256.Safety.ArgumentValues

namespace UInt256Model.Safety
open CIL.Safety

/-- A complete initialized output snapshot, usable by a caller that reads the result. -/
def InitializedBinaryContract (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (left right output : Reference),
    CallingConditions program memory [left, right] [output] →
    ∃ fuel final,
      InvocationCertificate program method (binaryArguments left right output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

theorem InitializedBinaryContract.to_wrapping {operation : BitVec 256 → BitVec 256 → BitVec 256}
    {program : CIL.Program} {method : Nat} (proof : InitializedBinaryContract operation program method) :
    WrappingBinaryContract operation program method := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, loaded, authority, outside⟩ := proof memory left right output call
  exact ⟨fuel, final, certificate, inputValue_of_encoded_read loaded, authority, outside⟩

#print axioms InitializedBinaryContract.to_wrapping
end UInt256Model.Safety
