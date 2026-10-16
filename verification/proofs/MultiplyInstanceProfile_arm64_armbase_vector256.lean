import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Safety.BinaryForwarder

namespace UInt256Proof.MultiplyInstance
open UInt256Proof.Multiply UInt256Proof.Multiply.Entry
private def context : Context :=
  ⟨⟨1,2,3,4,5,6,7,0,8⟩, Extracted.profile, Extracted.program, rfl, rfl, rfl, rfl, rfl, rfl, ProductStorage.vector_contract Extracted.profile rfl Extracted.program 7 rfl⟩
theorem profile_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  UInt256Model.Safety.forward_wrapping_binary Extracted.program 0 1 Extracted.method0 (· * ·)
    rfl rfl rfl rfl rfl rfl rfl
    (multiply_checked_contract context (hardware_word_contract true Extracted.profile rfl (by intro _; rfl) Extracted.program 8 rfl) (Full.scalar_top_contract Extracted.profile Extracted.program 2 8 5 7 rfl rfl rfl))
#print axioms profile_correctness
end UInt256Proof.MultiplyInstance
