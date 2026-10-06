import UInt256.Methods.Multiply.BothTwoSafety
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem software_both_two_invoke (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0)
    (rightUpper : inputLimb memory right 2 = 0 ∧ inputLimb memory right 3 = 0) :
    ∃ fuel final,
      invoke Extracted.program fuel bothTwoIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  both_two_invoke software_word_invoke memory left right output call leftUpper rightUpper

#print axioms software_both_two_invoke
end UInt256Proof.Multiply.Safety
