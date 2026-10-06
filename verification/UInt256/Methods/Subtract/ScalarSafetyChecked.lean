import UInt256.Methods.Subtract.ScalarSmallChecked
import UInt256.Methods.Subtract.ScalarGeneral

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem ScalarResult.as_subtract {original final : Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    SubtractResult original final values left right output :=
  ⟨result.wellFormed, result.modular_difference,
    by simpa only [scalar_flag_underflow, subtractUnderflow] using result.flag,
    result.writable, result.footprint⟩

theorem scalar_checked (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ SubtractResult memory final values left right output := by
  by_cases small : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call small
  · obtain ⟨fuel, final, values, executed, result⟩ := scalar_general_checked memory left right output call small
    exact ⟨fuel, final, values, executed, result.as_subtract⟩

#print axioms ScalarResult.as_subtract
#print axioms scalar_checked
end UInt256Proof.Subtract.Safety
