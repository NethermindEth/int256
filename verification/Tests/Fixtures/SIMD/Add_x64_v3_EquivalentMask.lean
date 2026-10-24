import Extracted
import UInt256.Methods.Add.Vector256Masked

namespace UInt256Proof.Fixture.SIMD.Add_x64_v3_EquivalentMask

/-- PrepareAdd masks the permuted carries with a constant lane vector instead of a zero blend. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  UInt256Proof.Add.Vector256.Masked.add_contract Extracted.program Extracted.profile
    rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_x64_v3_EquivalentMask
