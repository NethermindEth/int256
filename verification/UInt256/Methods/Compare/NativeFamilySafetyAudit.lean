import UInt256.Methods.Compare.NativeEntrySafety
import UInt256.Safety.ProfileContracts
import CIL.RelationalProfileCoverage

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

/-- Bind the discovered comparison chain to the extracted public entry and the
independent unsigned ordering of its two initial inputs. -/
theorem checked_less_contract :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0)) Extracted.program Extracted.entryIndex :=
    native_entry_checked
  exact entry.to_contract

theorem checked_less_binding :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_less_contract

#print axioms checked_less_contract
#print axioms checked_less_binding

theorem checked_less_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
    (native : Extracted.profile.avx512FVL = profile.avx512FVL)
    (avx2 : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2)
    (vector : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false →
      Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex 2 :=
  ReadOnlyContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.relational_profile_agreement Extracted.program Extracted.profile profile
      Extracted.profileValid valid (by decide) native avx2 vector) checked_less_contract

#print axioms checked_less_family
end UInt256Proof.Compare.Safety
