import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.WordForwarder
namespace UInt256Proof.Multiply.FixtureHelper
open Entry Calls CIL.Safety
private def context : Context :=
  scalarContext ⟨0,1,2,3,4,5,6,7,8⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 := by
  apply multiply_checked_contract context
    (forward_word_contract Extracted.profile Extracted.program 8 9 rfl ?_)
    (Full.scalar_top_contract Extracted.profile Extracted.program 1 8 4 6 rfl rfl rfl)
  intro memory a b output wf writable
  obtain ⟨final, invoked, valid, loaded, authority, outside⟩ :=
    scalar_word_invoke Extracted.profile rfl rfl Extracted.program 9 rfl memory a b output wf writable
  exact ⟨9, final, invoked, valid, loaded, authority, fun id _ offset bound => outside id offset bound⟩
#print axioms correctness
end UInt256Proof.Multiply.FixtureHelper
