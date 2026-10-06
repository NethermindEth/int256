import UInt256.Methods.Equality.SignedSafetyContract
import UInt256.Methods.Equality.SignedSafetyPrefix64
import UInt256.Methods.Equality.VectorPrimitive64Safety
import UInt256.Methods.Equality.VectorPrimitiveWrapperContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem vector_signed_checked64 :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if right.toInt < 0 then 0 else
        if left = right.zeroExtend 256 then 1 else 0))
      Extracted.program signedIndex := by
  intro memory left right call
  have unsigned := vector_primitive_wrapper_checked CIL.Value.i64
    (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
    (fun _ => rfl) (fun _ _ => rfl) vector_primitive_checked64
  have checked := signed_checked memory left (.i64 right) (right.zeroExtend 256)
    (decide (right.toInt < 0)) rfl (fun memory left call => unsigned memory left right call)
    (fun h => signed_negative64 right (of_decide_eq_true h))
    (fun h => signed_positive64 right (of_decide_eq_false h)) call
  simp only [decide_eq_true_eq] at checked
  exact checked

#print axioms vector_signed_checked64

end UInt256Proof.Equality.Safety
