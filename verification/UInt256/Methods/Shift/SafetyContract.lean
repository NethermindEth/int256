import UInt256.Methods.Shift.ContextSafetyContract

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- The public contract retains arbitrary valid overlap. The extracted body
    must establish that no output initialization precedes its operand reads. -/
theorem checked_shift_contract : ShiftContract shiftDirection Extracted.program shiftIndex := by
  intro memory input count output call
  exact checked_shift_context memory input count output call (Or.inl rfl)

#print axioms checked_shift_contract

theorem checked_shift_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ShiftContract shiftDirection (CIL.reprofile Extracted.program profile) shiftIndex :=
  ShiftContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same) checked_shift_contract

#print axioms checked_shift_family_contract
end UInt256Proof.Shift.Safety
