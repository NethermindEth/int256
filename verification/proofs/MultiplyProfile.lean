import Extracted
import UInt256.Safety.EmbeddingTransport
import UInt256.Methods.Multiply.ProfileLayout

namespace UInt256Proof.Multiply
open Entry
-- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
private abbrev embedded : CIL.Program := Extracted.program.set 1 (Full.fullBody Extracted.profile (profileIndices Extracted.profile 0).word 4 6)
private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program 1 (Full.fullBody Extracted.profile (profileIndices Extracted.profile 0).word 4 6) := by cil_embed
private def context : Context :=
  profileContext (profileIndices Extracted.profile 0) Extracted.profile embedded rfl rfl rfl rfl rfl rfl rfl rfl
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.WrappingBinaryContract.of_embeds fullEmbeds <|
  multiply_checked_contract context (profile_word_contract context rfl) (profile_top_contract context rfl)
#print axioms profile_correctness
end UInt256Proof.Multiply
