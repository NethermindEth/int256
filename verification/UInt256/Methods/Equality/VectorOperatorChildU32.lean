import UInt256.Methods.Equality.ScalarOperatorSafetyContract
import UInt256.Safety.ScalarEqualityFacts
import UInt256.Methods.Equality.VectorPrimitive32Safety
import UInt256.Methods.Equality.VectorPrimitiveWrapperContract

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem operator_child_checked :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if decide ((left.toNat : Int) = (right.toNat : Int)) then 1 else 0))
      Extracted.program operatorCallee := by
  intro memory left right call
  have child := vector_primitive_wrapper_checked CIL.Value.i32
    (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
    (fun _ => rfl) (fun _ _ => rfl) vector_primitive_checked32
  have checked := child memory left right call
  try dsimp only at checked
  rw [scalar_embedding right] at checked
  have bound : right.toNat < 2^256 := by have h := right.isLt; omega
  try dsimp only at checked
  rw [unsigned_scalar_flag (inputValue memory left) right.toNat bound] at checked
  simp only [decide_eq_true_eq]
  exact checked

#print axioms operator_child_checked

end UInt256Proof.Equality.Safety
