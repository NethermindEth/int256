import Extracted
import UInt256.Methods.Subtract.Vector256Entry

namespace UInt256Proof.Subtract

/-- AVX2 SubtractUnderflow: exact initial-operand borrow, wrapping difference, writable output, caller bytes kept. -/
theorem underflow_profile_correctness :
    UInt256Model.Safety.ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat))
      Extracted.program 0 :=
  Vector256.subtract_underflow_contract Extracted.program Extracted.profile true true rfl rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩
#print axioms underflow_profile_correctness
end UInt256Proof.Subtract
