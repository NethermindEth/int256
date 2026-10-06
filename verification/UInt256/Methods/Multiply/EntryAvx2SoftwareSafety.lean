import UInt256.Methods.Multiply.EntrySafetyInvoke
import UInt256.Methods.Multiply.FullSafetyAvx2Top
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem software_multiply_avx2_invoke (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel multiplyIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  multiply_invoke software_word_invoke full_avx2_top memory left right output call

#print axioms software_multiply_avx2_invoke
end UInt256Proof.Multiply.Safety
