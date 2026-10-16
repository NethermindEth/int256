import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.EntryPrimitiveSafety

namespace UInt256Proof.OperatorMultiplyUInt256UInt32
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
private def primitiveContext : PrimitiveContext := ⟨context, 0, 10, 11, true, false, rfl, rfl, rfl⟩
theorem profile_correctness : UInt256Model.Safety.OrderedScalarContract false CIL.Value.i32 (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  primitive32_with_contracts primitiveContext rfl (hardware_word_contract false Extracted.profile rfl (by intro h; cases h) Extracted.program 9 rfl) (Full.full_avx2_top Extracted.profile Extracted.program 2 9 5 7 rfl rfl rfl)

#print axioms profile_correctness
end UInt256Proof.OperatorMultiplyUInt256UInt32
