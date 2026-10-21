import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import Extracted
import UInt256.Safety.EmbeddingTransport
import UInt256.Methods.Multiply.EntryContract
import UInt256.Safety.BinaryForwarder

namespace UInt256Proof.MultiplyInstance
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
-- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
private abbrev embedded : CIL.Program := Extracted.program.set 2 (Full.fullBody Extracted.profile 9 5 7)
private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program 2 (Full.fullBody Extracted.profile 9 5 7) := by cil_embed
private def context : Context :=
  scalarContext ⟨1,2,3,4,5,6,7,8,9⟩ Extracted.profile embedded rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.WrappingBinaryContract.of_embeds fullEmbeds <|
  UInt256Model.Safety.forward_wrapping_binary embedded 0 1 Extracted.method0 (· * ·)
    rfl rfl rfl rfl rfl rfl rfl
    (multiply_checked_contract context (hardware_word_contract false Extracted.profile rfl (by intro h; cases h) embedded 9 rfl) (Full.full_avx2_top Extracted.profile embedded 2 9 5 7 rfl rfl rfl))
#print axioms profile_correctness
end UInt256Proof.MultiplyInstance
