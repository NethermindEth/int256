import Extracted
import UInt256.Methods.Subtract.Vector256Blended

namespace UInt256Proof.Fixture.Reporting.SubtractUnderflow_x64_avx2_bmi1_EquivalentMask

/-- The incoming borrows come from a zero blend instead of an and-mask; the body is five instructions shorter. -/
theorem correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left - right)
      (fun left right => decide (left.toNat < right.toNat)) Extracted.program 0 :=
  UInt256Proof.Subtract.Vector256.Blended.subtract_underflow_contract Extracted.program Extracted.profile true
    rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.Reporting.SubtractUnderflow_x64_avx2_bmi1_EquivalentMask
