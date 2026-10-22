import UInt256.Safety.RegionTransport
import UInt256.Methods.Shift.ScalarBody

namespace UInt256Proof.Shift.Variant
open CIL.Safety UInt256Proof.Transport UInt256Proof.Shift.Safety
set_option maxRecDepth 4096

/-- Every branch of the left body lands at or after the count computation and calls only storage. -/
theorem left_flow_inputs (profile : CIL.FeatureProfile) (storage : Nat) :
    ∀ op ∈ (scalarBody profile .left storage).code, FlowInput 3 (· = storage) op := by
  simp [scalarBody, FlowInput, CIL.Op.targets]

/-- The left body uses only the branch kinds `relocateOp` renames, so it agrees with `Op.relabel` there. -/
theorem left_relabel (profile : CIL.FeatureProfile) (storage : Nat) (f : Nat → Nat) :
    ∀ op ∈ (scalarBody profile .left storage).code, relocateOp f op = op.relabel f := by
  simp [scalarBody, relocateOp, CIL.Op.relabel]

#print axioms left_flow_inputs
#print axioms left_relabel
end UInt256Proof.Shift.Variant
