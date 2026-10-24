import Extracted
import UInt256.Safety.EmbeddingTransport
import UInt256.Methods.Multiply.ProfileLayout
import UInt256.Safety.BinaryForwarder

namespace UInt256Proof.MultiplyInstance
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
-- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
private abbrev embedded : CIL.Program := Extracted.program.set 2 (Full.fullBody Extracted.profile (profileIndices Extracted.profile 1).word 5 7)
private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program 2 (Full.fullBody Extracted.profile (profileIndices Extracted.profile 1).word 5 7) := by cil_embed
private def context : Context :=
  profileContext (profileIndices Extracted.profile 1) Extracted.profile embedded rfl rfl rfl rfl rfl rfl rfl rfl
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.WrappingBinaryContract.of_embeds fullEmbeds <|
  UInt256Model.Safety.forward_wrapping_binary embedded 0 1 Extracted.method0 (· * ·)
    rfl rfl rfl rfl rfl rfl rfl
    (multiply_checked_contract context (profile_word_contract context rfl) (profile_top_contract context rfl))
#print axioms profile_correctness
end UInt256Proof.MultiplyInstance
