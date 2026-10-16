import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top

namespace UInt256Proof.Multiply
open Entry
private def context : Context :=
  scalarContext ⟨0,1,2,3,4,5,6,7,8⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  multiply_checked_contract context (scalar_word_contract context rfl rfl rfl)
    (Full.full_avx512_top Extracted.profile Extracted.program 1 8 4 6 rfl rfl rfl rfl rfl rfl)
#print axioms profile_correctness
end UInt256Proof.Multiply