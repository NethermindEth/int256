import Extracted
import UInt256.Safety.EmbeddingTransport
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top

namespace UInt256Proof.Multiply
open Entry
-- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
private abbrev embedded : CIL.Program := Extracted.program.set 1 (Full.fullBody Extracted.profile 8 4 6)
private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program 1 (Full.fullBody Extracted.profile 8 4 6) := by cil_embed
private def context : Context :=
  scalarContext ⟨0,1,2,3,4,5,6,7,8⟩ Extracted.profile embedded rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.WrappingBinaryContract.of_embeds fullEmbeds <|
  multiply_checked_contract context (hardware_word_contract false Extracted.profile rfl (by intro h; cases h) embedded 8 rfl)
    (Full.full_avx512_top Extracted.profile embedded 1 8 4 6 rfl rfl rfl rfl rfl rfl)
#print axioms profile_correctness
end UInt256Proof.Multiply