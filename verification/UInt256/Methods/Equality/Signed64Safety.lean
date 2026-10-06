import UInt256.Methods.Equality.SignedSafetyContract
import UInt256.Methods.Equality.PrimitiveSafetyContract
import UInt256.Methods.Equality.SignedSafetyPrefix64
import UInt256.Methods.Equality.PrimitiveSafetyPrefix64
import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem scalar_signed_checked64 :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if right.toInt < 0 then 0 else
        if left = BitVec.ofNat 256 right.toNat then 1 else 0))
      Extracted.program signedIndex := by
  intro memory left right call
  have checked := signed_checked memory left (.i64 right) (BitVec.ofNat 256 right.toNat) (decide (right.toInt < 0)) rfl
    (fun memory left call => primitive_checked memory left (.i64 right) right rfl
      (primitive_prefix64 right) call)
    (fun h => signed_negative64 right (of_decide_eq_true h))
    (fun h => signed_positive64 right (of_decide_eq_false h)) call
  simp only [decide_eq_true_eq] at checked
  exact checked

#print axioms scalar_signed_checked64

end UInt256Proof.Equality.Safety
