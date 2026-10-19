import Extracted
import UInt256.Methods.Shift.HelperVariant
import UInt256.Methods.Shift.ScalarOperator

namespace UInt256Proof.Shift.Fixture
open UInt256Model.Safety UInt256Proof.Shift.Safety UInt256Proof.Shift.Variant

/-- The whole-limb count is a call to a compiled `count >> 6` helper. -/
theorem correctness : ReadOnlyScalarContract CIL.Value.i32
    (fun input count => .aggregate (CIL.Safety.numberBytes (UInt256Proof.Shift.result .left input count).toNat 32))
    Extracted.program 0 :=
  operator_correctness Extracted.profile .left Extracted.program 0 1 (by rfl)
    (wrapper_correctness Extracted.profile .left Extracted.program 1 2 (by rfl)
      (scalar_helper_contract Extracted.profile (by rfl) Extracted.program 2 3 4 (by decide) (by rfl) (by rfl) (by rfl)))

#print axioms correctness
end UInt256Proof.Shift.Fixture
