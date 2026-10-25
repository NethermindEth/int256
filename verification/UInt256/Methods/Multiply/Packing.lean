import UInt256.Methods.Multiply.ProductColumns
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply
theorem productLimbs_value (a b : Limbs) :
    value (productLimbs a b) = BitVec.ofNat 256 (productTotal a b) := by
  simp (config := { implicitDefEqProofs := false }) only
    [value, productLimbs, Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte]
  rfl
end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.productLimbs_value
