import UInt256.Methods.Equality.ScalarOperatorSafetyContract
import UInt256.Safety.ScalarEqualityFacts
import UInt256.Methods.Equality.PrimitiveSafetyContract
import UInt256.Methods.Equality.PrimitiveSafetyPrefix32

namespace UInt256Proof.Equality.Safety

open UInt256Model.Safety

theorem operator_child_checked :
    ReadOnlyScalarContract CIL.Value.i32
      (fun left right => .i32 (if decide ((left.toNat : Int) = (right.toNat : Int)) then 1 else 0))
      Extracted.program operatorCallee := by
  intro memory left right call
  have checked := primitive_checked memory left (.i32 right) (right.zeroExtend 64) rfl (primitive_prefix32 right) call
  have widened : (right.zeroExtend 64).toNat = right.toNat := by
    have bound := right.isLt
    simp
    omega
  try dsimp only at checked
  rw [widened] at checked
  have bound : right.toNat < 2^256 := by have h := right.isLt; omega
  try dsimp only at checked
  rw [unsigned_scalar_flag (inputValue memory left) right.toNat bound] at checked
  simp only [decide_eq_true_eq]
  exact checked

#print axioms operator_child_checked

end UInt256Proof.Equality.Safety
