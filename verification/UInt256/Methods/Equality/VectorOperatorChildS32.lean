import UInt256.Methods.Equality.ScalarOperatorSafetyContract
import UInt256.Safety.ScalarEqualityFacts
import UInt256.Methods.Equality.VectorSigned32Safety

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem operator_child_checked :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if decide ((left.toNat : Int) = right.toInt) then 1 else 0))
      Extracted.program operatorCallee := by
  intro memory left right call
  have checked := vector_signed_checked32 memory left right call
  try dsimp only at checked
  rw [scalar_embedding right] at checked
  have bound : right.toNat < 2^256 := by have h := right.isLt; omega
  try dsimp only at checked
  rw [signed_scalar_flag (inputValue memory left) right bound] at checked
  simp only [decide_eq_true_eq]
  exact checked

#print axioms operator_child_checked

end UInt256Proof.Equality.Safety
