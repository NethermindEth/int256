import UInt256.Methods.ValueSafety
import UInt256.Methods.Compare.ThreeWaySafetyContract
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

theorem checked_threeWayValue_contract :
    ReadOnlyValueContract
      (fun x y => .i32 (UInt256Model.Compare.compareWord x.toNat y.toNat))
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.ValueSafety.value_entry_checked threeWayIndex
    (fun x y => UInt256Model.Compare.compareWord x.toNat y.toNat) (by rfl) threeWay_checked

theorem checked_threeWayValue_binding :
    ReadOnlyValueContract
      (fun x y => .i32 (UInt256Model.Compare.compareWord x.toNat y.toNat))
      Extracted.program Extracted.entryIndex := checked_threeWayValue_contract

theorem checked_threeWayValue_family (profile : CIL.FeatureProfile) (_valid : profile.Valid) :
    ReadOnlyValueContract
      (fun x y => .i32 (UInt256Model.Compare.compareWord x.toNat y.toNat))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex :=
  ReadOnlyValueContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (Extracted.program.profile_independent_agreement (by decide) _ _) checked_threeWayValue_contract

#print axioms checked_threeWayValue_contract
#print axioms checked_threeWayValue_binding
#print axioms checked_threeWayValue_family
end UInt256Proof.Compare.Safety
