import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import Extracted
import UInt256.Methods.Multiply.EntryContract

namespace UInt256Proof.OperatorMultiplyUInt256UInt256
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
private def context : Context :=
  ⟨⟨1,2,3,4,5,6,7,0,8⟩, Extracted.profile, Extracted.program, rfl, rfl, rfl, rfl, rfl, rfl, ProductStorage.vector_contract Extracted.profile rfl Extracted.program 7 rfl⟩
theorem profile_correctness : UInt256Model.Safety.AggregateReturn.BinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.AggregateReturn.binary_checked (· * ·) Extracted.profile Extracted.program 0 1 rfl
    (initialized_result context (scalar_word_contract context rfl rfl rfl) (Full.full_avx512_top Extracted.profile Extracted.program 2 8 5 7 rfl rfl rfl rfl rfl rfl))
#print axioms profile_correctness
end UInt256Proof.OperatorMultiplyUInt256UInt256
