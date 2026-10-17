import Extracted
import UInt256.Methods.Add.Vector256Masked

namespace UInt256Proof.Fixture.Reporting.AddOverflow_x64_avx2_bmi1_EquivalentMask

/-- PrepareAdd masks the permuted carries with a constant lane vector instead of a zero blend. -/
theorem correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) Extracted.program 0 :=
  UInt256Proof.Add.Vector256.Masked.add_overflow_contract Extracted.program Extracted.profile
    rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.Reporting.AddOverflow_x64_avx2_bmi1_EquivalentMask
