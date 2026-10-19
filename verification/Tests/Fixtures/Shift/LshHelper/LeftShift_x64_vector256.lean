import Extracted
import UInt256.Methods.Shift.HelperVariant
import UInt256.Methods.Shift.ScalarWrapper

namespace UInt256Proof.Shift.Fixture
open UInt256Model.Safety UInt256Proof.Shift.Safety UInt256Proof.Shift.Variant

/-- The whole-limb count is a call to a compiled `count >> 6` helper. -/
theorem correctness : ShiftContract .left Extracted.program 0 :=
  wrapper_correctness Extracted.profile .left Extracted.program 0 1 (by rfl)
    (vector_helper_contract Extracted.profile (by rfl) Extracted.program 1 2 3 (by decide) (by rfl) (by rfl) (by rfl))

#print axioms correctness
end UInt256Proof.Shift.Fixture
