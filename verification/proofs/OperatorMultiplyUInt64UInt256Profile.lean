import Extracted
import UInt256.Safety.EmbeddingTransport
import UInt256.Methods.Multiply.ProfileLayout
import UInt256.Methods.Multiply.EntryPrimitiveSafety

namespace UInt256Proof.OperatorMultiplyUInt64UInt256
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
-- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
private abbrev embedded : CIL.Program := Extracted.program.set 2 (Full.fullBody Extracted.profile (profileIndices Extracted.profile 1).word 5 7)
private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program 2 (Full.fullBody Extracted.profile (profileIndices Extracted.profile 1).word 5 7) := by cil_embed
private def context : Context :=
  profileContext (profileIndices Extracted.profile 1) Extracted.profile embedded rfl rfl rfl rfl rfl rfl rfl rfl
private def primitiveContext : PrimitiveContext := ⟨context, 0, (profileIndices Extracted.profile 1).word + 1, (profileIndices Extracted.profile 1).word + 2, false, true, rfl, rfl, rfl⟩
theorem profile_correctness : UInt256Model.Safety.OrderedScalarContract true CIL.Value.i64 (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Model.Safety.OrderedScalarContract.of_embeds fullEmbeds <|
  primitive64_with_contracts primitiveContext rfl (profile_word_contract context rfl) (profile_top_contract context rfl)
#print axioms profile_correctness
end UInt256Proof.OperatorMultiplyUInt64UInt256
