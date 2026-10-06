import UInt256.Methods.Equality.SignedSafetyContract
import UInt256.Methods.Equality.PrimitiveSafetyContract
import UInt256.Methods.Equality.SignedSafetyPrefix32
import UInt256.Methods.Equality.PrimitiveSafetyPrefix32
import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem scalar_signed_checked32 :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if right.toInt < 0 then 0 else
        if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      Extracted.program signedIndex := by
  intro memory left right call
  have checked := signed_checked memory left (.i32 right) (BitVec.ofNat 256 (right.zeroExtend 64).toNat) (decide (right.toInt < 0)) rfl
    (fun memory left call => primitive_checked memory left (.i32 right) (right.zeroExtend 64) rfl
      (primitive_prefix32 right) call)
    (fun h => signed_negative32 right (of_decide_eq_true h))
    (fun h => signed_positive32 right (of_decide_eq_false h)) call
  simp only [decide_eq_true_eq] at checked
  have widened : (right.zeroExtend 64).toNat = right.toNat := by
    have bound := right.isLt
    simp
    omega
  rw [widened] at checked
  exact checked

#print axioms scalar_signed_checked32

end UInt256Proof.Equality.Safety
