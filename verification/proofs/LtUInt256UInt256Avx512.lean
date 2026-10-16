import UInt256.Methods.Compare.ProfileBindings
import Extracted
import UInt256.Methods.Compare.NativeEntrySafety

theorem UInt256Proof.Compare.LtUInt256UInt256.avx512_correctness :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program 0 2 := by
  have proof := UInt256Proof.Compare.Safety.native_entry_checked Extracted.profile true false Extracted.program 0 1 rfl rfl rfl rfl rfl rfl
  simpa [UInt256Proof.Compare.Safety.nativePredicate] using proof.to_contract
#print axioms UInt256Proof.Compare.LtUInt256UInt256.avx512_correctness


theorem UInt256Proof.Compare.LtUInt256UInt256.avx512_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (native : Extracted.profile.avx512FVL = profile.avx512FVL)
    (avx2 : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2)
    (vector : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) 0 2 :=
  UInt256Model.Safety.ReadOnlyContract.reprofile UInt256Proof.Compare.ProfileBindings.uniform (UInt256Proof.Compare.ProfileBindings.agreement profile valid native avx2 vector) UInt256Proof.Compare.LtUInt256UInt256.avx512_correctness
#print axioms UInt256Proof.Compare.LtUInt256UInt256.avx512_family
