import UInt256.Methods.Reporting.SubtractCorrectness

open CIL UInt256Model

namespace UInt256Proof.Reporting

theorem checked_subtract_contract : ∀ initial left right out,
    Reporting.Contract .subtract Extracted.program Extracted.entryIndex initial left right out :=
  subtract_correct

theorem checked_subtract_profile_contract : ∀ profile : FeatureProfile,
    profile.Valid → Extracted.program.ProfileAgreement Extracted.profile profile →
    ∀ initial left right out,
      Reporting.Contract .subtract (reprofile Extracted.program profile)
        Extracted.entryIndex initial left right out := by
  intro profile _ agreement initial left right out
  obtain ⟨fuel, final, execution, bytes⟩ := subtract_correct initial left right out
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← invoke_uniform_reprofile_eq Extracted.program Extracted.profile profile
    (uniform_of_profile_map _ _ Extracted.programProfiles) agreement]
  exact execution

theorem checked_subtract_family_contract : ∀ profile : FeatureProfile,
    profile.Valid → profile.classify = Extracted.profile.classify →
    ∀ initial left right out,
      Reporting.Contract .subtract (reprofile Extracted.program profile)
        Extracted.entryIndex initial left right out := by
  intro profile valid family
  exact checked_subtract_profile_contract profile valid
    (Extracted.program.same_family_profile_agreement profile Extracted.profile
      valid Extracted.profileValid family Extracted.programClassified)

#print axioms checked_subtract_contract
#print axioms checked_subtract_profile_contract
#print axioms checked_subtract_family_contract

end UInt256Proof.Reporting
