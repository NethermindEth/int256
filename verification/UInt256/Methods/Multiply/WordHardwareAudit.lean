import UInt256.Methods.Multiply.WordSafety

namespace UInt256Proof.Multiply.Safety

/-- The checked invocation theorem's hardware premise is inhabited for this
    extracted profile; the hardware evidence is not a vacuous conditional. -/
theorem hardware_profile_supported :
    Extracted.profile.bmi2 = true ∨ Extracted.profile.armBase64 = true := by decide

#print axioms hardware_profile_supported
end UInt256Proof.Multiply.Safety
