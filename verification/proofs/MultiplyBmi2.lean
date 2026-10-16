import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.WordHardwareSafety
namespace UInt256Proof.Multiply
open Entry
private def acceleratedContext : Context :=
  scalarContext ⟨0,1,2,3,4,5,6,7,8⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem accelerated_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  multiply_checked_contract acceleratedContext
    (hardware_word_contract false Extracted.profile rfl (by intro h; simp_all) Extracted.program 8 rfl)
    (Full.scalar_top_contract Extracted.profile Extracted.program 1 8 4 6 rfl rfl rfl)
#print axioms accelerated_correctness
end UInt256Proof.Multiply
