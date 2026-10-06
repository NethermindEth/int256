import UInt256.Methods.Multiply.LeftTwoSafety
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem software_left_two_invoke (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (leftUpper : inputLimb memory left 2 = 0 ∧ inputLimb memory left 3 = 0) :
    ∃ fuel final,
      invoke Extracted.program fuel leftTwoIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  left_two_invoke software_word_invoke memory left right output call leftUpper

#print axioms software_left_two_invoke
end UInt256Proof.Multiply.Safety
