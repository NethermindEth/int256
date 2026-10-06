import UInt256.Methods.Equality.ScalarSafety
import UInt256.Methods.Equality.Lemmas

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem input_limb_value (memory : Memory) (reference : Reference) :
    UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
  UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

/-- The execution reduction is equivalent to equality of independently decoded
    initial values, including when their input views partially overlap. -/
theorem scalar_difference_zero (memory : Memory) (left right : Reference) :
    scalarDifference memory left right = 0 ↔ inputValue memory left = inputValue memory right := by
  have equal := xor_or_zero_value (inputLimb memory left) (inputLimb memory right)
  rw [input_limb_value, input_limb_value] at equal
  exact equal

theorem scalar_run_value (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel scalarIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  simpa only [scalar_difference_zero] using scalar_run memory left right frame call

#print axioms scalar_difference_zero
#print axioms scalar_run_value

end UInt256Proof.Equality.Safety
