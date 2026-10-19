import UInt256.Safety.RegionSteps
import UInt256.Methods.Shift.ScalarBody

namespace UInt256Proof.Shift.Variant
open CIL.Safety UInt256Proof.Transport UInt256Proof.Shift.Safety
set_option maxRecDepth 4096

theorem left_supported (profile : CIL.FeatureProfile) (storage : Nat) :
    ∀ op ∈ (scalarBody profile .left storage).code, Supported op := by
  simp only [scalarBody, List.forall_mem_append, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first
    | (solve | simp)
    | exact .conv
    | exact .arg _
    | exact .localValue _
    | exact .setLocal _
    | exact .call _ _
    | exact .ret
    | exact .branch .ge _
    | exact .branch .ult _
    | exact .branch .ne _
    | exact .branch .nonzero _
    | (apply Supported.memory; constructor)
    | (apply Supported.binary; constructor)

/-- Every branch of the left body lands at or after the count computation and calls only storage. -/
theorem left_flow_inputs (profile : CIL.FeatureProfile) (storage : Nat) :
    ∀ op ∈ (scalarBody profile .left storage).code, FlowInput 3 (· = storage) op := by
  simp [scalarBody, FlowInput]

/-- After the count prefix, every branch stays in the operand and output suffix. -/
theorem left_suffix_flow_inputs (profile : CIL.FeatureProfile) (storage : Nat) :
    ∀ op ∈ (scalarBody profile .left storage).code.drop 27, FlowInput 27 (· = storage) op := by
  simp [scalarBody, List.drop, FlowInput]

#print axioms left_supported
#print axioms left_flow_inputs
#print axioms left_suffix_flow_inputs
end UInt256Proof.Shift.Variant
