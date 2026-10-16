import Extracted
import UInt256.Methods.Subtract.Vector256Entry

namespace UInt256Proof.Subtract

/-- AVX2 Subtract: wrapping difference of the initial operands, checked return, writable output, caller bytes kept. -/
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  Vector256.subtract_contract Extracted.program Extracted.profile true true rfl rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩
#print axioms profile_correctness
end UInt256Proof.Subtract
