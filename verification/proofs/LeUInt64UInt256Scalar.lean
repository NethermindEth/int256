import Extracted
import UInt256.Safety.ProfileContracts
import UInt256.Methods.Compare.PrimitiveValue

theorem UInt256Proof.Compare.LeUInt64UInt256.scalar_correctness :
    UInt256Proof.Compare.PrimitiveValue.Contract Extracted.program 0 :=
  UInt256Proof.Compare.PrimitiveValue.correctness Extracted.program 0 1 (by rfl) (by rfl)

#print axioms UInt256Proof.Compare.LeUInt64UInt256.scalar_correctness

theorem UInt256Proof.Compare.LeUInt64UInt256.scalar_family (profile : CIL.FeatureProfile) :
    UInt256Proof.Compare.PrimitiveValue.Contract (CIL.reprofile Extracted.program profile) 0 := by
  intro memory word value call
  obtain ⟨fuel, final, certificate, preserved⟩ := UInt256Proof.Compare.LeUInt64UInt256.scalar_correctness memory word value
    ((UInt256Model.Safety.callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, CIL.Safety.invocationCertificate_uniform_reprofile Extracted.program Extracted.profile profile
    (CIL.uniform_of_profile_map _ _ rfl)
    (CIL.Program.ProfileAgreement.of_flags _ _ _ (by
      have noReads : Extracted.program.profileReads = [] := by decide +kernel
      intro feature member
      simp [noReads] at member))
    _ _ _ _ _ _ certificate, preserved⟩
#print axioms UInt256Proof.Compare.LeUInt64UInt256.scalar_family
