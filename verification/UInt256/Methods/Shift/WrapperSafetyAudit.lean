import UInt256.Methods.Shift.WrapperSafety

namespace UInt256Proof.Shift.Safety
theorem checked_wrapper_binding :
    UInt256Model.Safety.ShiftContract .left Extracted.program Extracted.entryIndex := by
  simpa only [show shiftDirection = .left from rfl, show wrapperIndex = Extracted.entryIndex from rfl] using checked_wrapper_contract

theorem checked_wrapper_family_binding (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ShiftContract .left (CIL.reprofile Extracted.program profile) Extracted.entryIndex := by
  simpa only [show shiftDirection = .left from rfl, show wrapperIndex = Extracted.entryIndex from rfl] using checked_wrapper_family_contract profile valid same

#print axioms checked_wrapper_binding
#print axioms checked_wrapper_family_binding
end UInt256Proof.Shift.Safety
