import UInt256.Methods.Shift.ReturnSafety

namespace UInt256Proof.Shift.Safety
open UInt256Model.Safety
theorem checked_right_return_binding : ReadOnlyScalarContract CIL.Value.i32
    (fun initial count => .v256 (result .right initial count))
    Extracted.program Extracted.entryIndex := by
  simpa only [show shiftDirection = .right from rfl] using checked_return_contract

theorem checked_right_return_family_binding (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun initial count => .v256 (result .right initial count))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex := by
  simpa only [show shiftDirection = .right from rfl] using checked_return_family_contract profile valid same

#print axioms checked_right_return_binding
#print axioms checked_right_return_family_binding
end UInt256Proof.Shift.Safety
