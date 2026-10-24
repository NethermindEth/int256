import Extracted
import UInt256.Methods.Add.Vector256Entry

namespace UInt256Proof.Add

/-- AVX2 AddOverflow: exact initial-operand carry, wrapping sum, writable output, caller bytes kept. -/
theorem overflow_profile_correctness :
    UInt256Model.Safety.ReportingBinaryContract (· + ·)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) Extracted.program 0 :=
  Vector256.add_overflow_contract Extracted.program Extracted.profile true rfl rfl rfl rfl
    ⟨rfl, rfl, rfl, rfl⟩
#print axioms overflow_profile_correctness
end UInt256Proof.Add
