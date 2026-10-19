import Extracted
import UInt256.Safety.ProfileContracts
import UInt256.Methods.Compare.ThreeWayValue

theorem UInt256Proof.Compare.CompareToUInt256Value.scalar_correctness :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.ValueForwarder32.encode
      (fun left right => .i32 (UInt256Model.Compare.compareWord left.toNat right.toNat)) Extracted.program 0 :=
  UInt256Proof.Compare.ThreeWayValue.correctness Extracted.profile Extracted.program 0 1 (by rfl) (by rfl)

#print axioms UInt256Proof.Compare.CompareToUInt256Value.scalar_correctness

theorem UInt256Proof.Compare.CompareToUInt256Value.scalar_family (profile : CIL.FeatureProfile) :
    UInt256Model.Safety.ReadOnlyScalarContract UInt256Proof.ValueForwarder32.encode
      (fun left right => .i32 (UInt256Model.Compare.compareWord left.toNat right.toNat))
      (CIL.reprofile Extracted.program profile) 0 :=
  UInt256Proof.Compare.ThreeWayValue.correctness profile (CIL.reprofile Extracted.program profile) 0 1 rfl rfl
#print axioms UInt256Proof.Compare.CompareToUInt256Value.scalar_family
