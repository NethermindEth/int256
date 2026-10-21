import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import Extracted
import UInt256.Safety.EmbeddingTransport
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.EntryPrimitiveSafety

namespace UInt256Proof.OperatorMultiplyUInt64UInt256
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
-- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
private abbrev embedded : CIL.Program := Extracted.program.set 2 (Full.fullBody Extracted.profile 9 5 7)
private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program 2 (Full.fullBody Extracted.profile 9 5 7) := by cil_embed
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile embedded rfl rfl rfl rfl rfl rfl rfl rfl rfl
private def primitiveContext : PrimitiveContext := ⟨context, 0, 10, 11, false, true, rfl, rfl, rfl⟩
theorem profile_correctness : UInt256Model.Safety.OrderedScalarContract true CIL.Value.i64 (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Model.Safety.OrderedScalarContract.of_embeds fullEmbeds <|
  primitive64_with_contracts primitiveContext rfl (hardware_word_contract false Extracted.profile rfl (by intro h; cases h) embedded 9 rfl) (Full.full_avx512_top Extracted.profile embedded 2 9 5 7 rfl rfl rfl rfl rfl rfl)

#print axioms profile_correctness
end UInt256Proof.OperatorMultiplyUInt64UInt256
