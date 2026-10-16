import UInt256.Methods.Compare.ProfileBindings
import UInt256.Methods.Compare.GreaterEqualFamilySafetyAudit

/-- Unsigned ordering of the initial UInt256 values, checked finite return,
    and preservation of caller memory. -/
theorem UInt256Proof.Compare.GeUInt256UInt256.scalar_correctness :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat ≥ (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 :=
  UInt256Proof.Compare.Safety.checked_greater_equal_binding

#print axioms UInt256Proof.Compare.GeUInt256UInt256.scalar_correctness


theorem UInt256Proof.Compare.GeUInt256UInt256.scalar_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (native : Extracted.profile.avx512FVL = profile.avx512FVL)
    (avx2 : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2)
    (vector : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat ≥ (values[1]?.getD 0).toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex 2 :=
  UInt256Model.Safety.ReadOnlyContract.reprofile UInt256Proof.Compare.ProfileBindings.uniform (UInt256Proof.Compare.ProfileBindings.agreement profile valid native avx2 vector) UInt256Proof.Compare.GeUInt256UInt256.scalar_correctness
#print axioms UInt256Proof.Compare.GeUInt256UInt256.scalar_family
