import UInt256.Methods.Shift.SafetyContract

theorem UInt256Proof.Shift.Safety.checked_shift_binding :
    UInt256Model.Safety.ShiftContract .left Extracted.program Extracted.entryIndex := by
  simpa only [show UInt256Proof.Shift.Safety.shiftDirection = .left from rfl,
    show UInt256Proof.Shift.Safety.shiftIndex = Extracted.entryIndex from rfl] using
    UInt256Proof.Shift.Safety.checked_shift_contract

#print axioms UInt256Proof.Shift.Safety.checked_shift_binding

theorem UInt256Proof.Shift.Safety.checked_shift_family_binding (profile : CIL.FeatureProfile)
    (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ShiftContract .left (CIL.reprofile Extracted.program profile) Extracted.entryIndex := by
  simpa only [show UInt256Proof.Shift.Safety.shiftDirection = .left from rfl,
    show UInt256Proof.Shift.Safety.shiftIndex = Extracted.entryIndex from rfl] using
    UInt256Proof.Shift.Safety.checked_shift_family_contract profile valid same

#print axioms UInt256Proof.Shift.Safety.checked_shift_family_binding
