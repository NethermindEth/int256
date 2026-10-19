import Extracted
import UInt256.Methods.Shift.EarlyStore

namespace UInt256Proof.Shift.Fixture
open UInt256Model.Safety UInt256Proof.Shift.Safety UInt256Proof.Shift.Variant

/-- The private result's first limb is zeroed before the input is read; the operator's output is always fresh. -/
theorem correctness : ReadOnlyScalarContract CIL.Value.i32
    (fun input count => .aggregate (CIL.Safety.numberBytes (UInt256Proof.Shift.result .left input count).toNat 32))
    Extracted.program 0 :=
  operator_disjoint_correctness Extracted.profile .left Extracted.program 0 1 (by rfl)
    (wrapper_disjoint_correctness Extracted.profile .left Extracted.program 1 2 (by rfl)
      (scalar_early_contract Extracted.profile (by rfl) Extracted.program 2 3 (by decide) (by rfl) (by rfl)))

#print axioms correctness
end UInt256Proof.Shift.Fixture
