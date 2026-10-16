import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top

namespace UInt256Proof.Multiply
open Entry
private def context : Context :=
  ⟨⟨0,1,2,3,4,5,6,0,7⟩, Extracted.profile, Extracted.program, rfl, rfl, rfl, rfl, rfl, rfl, ProductStorage.vector_contract Extracted.profile rfl Extracted.program 6 rfl⟩

theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  multiply_checked_contract context (hardware_word_contract false Extracted.profile rfl (by intro h; cases h) Extracted.program 7 rfl)
    (Full.full_avx2_top Extracted.profile Extracted.program 1 7 4 6 rfl rfl rfl)
#print axioms profile_correctness
end UInt256Proof.Multiply