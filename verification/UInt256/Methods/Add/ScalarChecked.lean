import UInt256.Methods.Add.ScalarSmallChecked
import UInt256.Methods.Add.ScalarFinish

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem ScalarResult.as_add {original final : CIL.Safety.Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    AddResult original final values left right output :=
  ⟨result.wellFormed, result.modular_sum, by simpa only [scalar_flag_overflow] using result.flag,
    result.writable, result.footprint⟩

/-- All scalar helper branches: actual finite execution, initial-operand sum,
    mathematical overflow and caller storage preservation under valid overlap. -/
theorem scalar_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  by_cases rightSmall : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call rightSmall
  · by_cases leftSmall : inputLimb memory left 1 ||| inputLimb memory left 2 |||
        inputLimb memory left 3 = BitVec.ofNat 64 0
    · exact scalar_left_small_checked memory left right output call rightSmall leftSmall
    · obtain ⟨fuel, final, values, invoked, result⟩ :=
        scalar_general_checked memory left right output call rightSmall leftSmall
      exact ⟨fuel, final, values, invoked, result.as_add⟩

#print axioms ScalarResult.as_add
#print axioms scalar_checked

end UInt256Proof.Safety
