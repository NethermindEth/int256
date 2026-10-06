import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem software_full_avx512_invoke (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel fullIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  full_invoke software_word_invoke full_avx512_top memory left right output call

#print axioms software_full_avx512_invoke
end UInt256Proof.Multiply.Safety
