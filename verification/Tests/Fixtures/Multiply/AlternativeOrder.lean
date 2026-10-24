import Extracted
import UInt256.Methods.Multiply.EntryContract
namespace UInt256Proof.Multiply.FixtureAlternative
open Entry CIL.Safety
private def context : Context true :=
  scalarContext ⟨0,1,2,3,4,5,6,7,8⟩ Extracted.profile Extracted.program rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  scalar_correctness context rfl rfl rfl rfl rfl
#print axioms correctness
end UInt256Proof.Multiply.FixtureAlternative

