import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import Extracted
import UInt256.Methods.Multiply.EntryContract

namespace UInt256Proof.OperatorMultiplyUInt256UInt256
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem profile_correctness : UInt256Model.Safety.AggregateReturn.BinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.AggregateReturn.binary_checked (· * ·) Extracted.profile Extracted.program 0 1 rfl
    (initialized_result context (hardware_word_contract false Extracted.profile rfl (by intro h; cases h) Extracted.program 9 rfl) (Full.full_avx512_top Extracted.profile Extracted.program 2 9 5 7 rfl rfl rfl rfl rfl rfl))
#print axioms profile_correctness
end UInt256Proof.OperatorMultiplyUInt256UInt256
