import Extracted
import UInt256.Methods.Add.Vector256Entry

namespace UInt256Proof.Add

/-- AVX2 Add: wrapping sum of the initial operands, checked return, writable output, caller bytes kept. -/
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  Vector256.add_contract Extracted.program Extracted.profile true rfl rfl rfl rfl
    ⟨rfl, rfl, rfl, rfl⟩
#print axioms profile_correctness
end UInt256Proof.Add
