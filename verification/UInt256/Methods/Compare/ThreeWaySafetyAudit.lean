import UInt256.Methods.Compare.ThreeWaySafetyContract
import UInt256.Safety.ReadOnlyForwarder
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

/-- Bind the discovered comparison chain to the extracted public entry and the
independent unsigned ordering of its two initial inputs. -/
theorem checked_threeWay_contract :
    ReadOnlyContract
      (fun values => .i32 (UInt256Model.Compare.compareWord
        (values[0]?.getD 0).toNat (values[1]?.getD 0).toNat))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation
      (fun x y => .i32 (UInt256Model.Compare.compareWord x.toNat y.toNat))
      Extracted.program Extracted.entryIndex := threeWay_checked
  exact entry.to_contract

theorem checked_threeWay_binding :
    ReadOnlyContract
      (fun values => .i32 (UInt256Model.Compare.compareWord
        (values[0]?.getD 0).toNat (values[1]?.getD 0).toNat))
      Extracted.program Extracted.entryIndex 2 := checked_threeWay_contract

#print axioms checked_threeWay_contract
#print axioms checked_threeWay_binding

theorem checked_threeWay_family (profile : CIL.FeatureProfile) (_valid : profile.Valid) :
    ReadOnlyContract
      (fun values => .i32 (UInt256Model.Compare.compareWord
        (values[0]?.getD 0).toNat (values[1]?.getD 0).toNat))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex 2 :=
  ReadOnlyContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (Extracted.program.profile_independent_agreement (by decide) _ _) checked_threeWay_contract

#print axioms checked_threeWay_family

end UInt256Proof.Compare.Safety
