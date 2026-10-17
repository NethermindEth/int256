import Extracted
import UInt256.Methods.Subtract.Vector256Blended

namespace UInt256Proof.Fixture.SIMD.Subtract_x64_avx2_EquivalentMask

/-- The incoming borrows come from a zero blend instead of an and-mask; the body is five instructions shorter. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  UInt256Proof.Subtract.Vector256.Blended.subtract_contract Extracted.program Extracted.profile false
    rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Subtract_x64_avx2_EquivalentMask
