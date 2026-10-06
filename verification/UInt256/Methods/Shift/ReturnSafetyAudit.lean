import UInt256.Methods.Shift.ReturnSafety

namespace UInt256Proof.Shift.Safety
open UInt256Model.Safety
theorem checked_return_binding : ReadOnlyScalarContract CIL.Value.i32
    (fun initial count => .v256 (result .left initial count))
    Extracted.program Extracted.entryIndex := by
  simpa only [show shiftDirection = .left from rfl] using checked_return_contract

theorem checked_return_family_binding (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun initial count => .v256 (result .left initial count))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex := by
  simpa only [show shiftDirection = .left from rfl] using checked_return_family_contract profile valid same

#print axioms checked_return_binding
#print axioms checked_return_family_binding
end UInt256Proof.Shift.Safety
