import UInt256.Methods.Multiply.EntrySafetyInvoke
import UInt256.Methods.Multiply.FullSafetyScalarTop
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem software_multiply_scalar_invoke (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel multiplyIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  multiply_invoke software_word_invoke full_scalar_top memory left right output call

#print axioms software_multiply_scalar_invoke
end UInt256Proof.Multiply.Safety
