import CIL.Safety.StepFlow
import UInt256.Methods.Shift.ScalarBody

namespace UInt256Proof.Shift.Variant
open UInt256Proof.Shift.Safety
set_option maxRecDepth 4096

/-- Every branch of the left body lands at or after the count computation, and it calls only storage. -/
theorem left_flow (profile : CIL.FeatureProfile) (storage : Nat) :
    ∀ op ∈ (scalarBody profile .left storage).code, (∀ target ∈ op.targets, 3 ≤ target) ∧
      ∀ callee ∈ op.callees, callee = storage := by
  simp [scalarBody, CIL.Op.targets, CIL.Op.callees]

#print axioms left_flow
end UInt256Proof.Shift.Variant
