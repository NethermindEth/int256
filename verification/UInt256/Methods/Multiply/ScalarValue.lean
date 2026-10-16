import UInt256.Methods.Multiply.ScalarProduct
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem scalarLimbs_value (a : Limbs) (word : W64) :
    value (scalarLimbs a word) = BitVec.ofNat 256 (scalarTotal a word) := by
  simp (config := { implicitDefEqProofs := false }) only
    [value, scalarLimbs, Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte]
  rfl

theorem scalar_retained_value (a : Limbs) (word : W64) :
    value a * BitVec.ofNat 256 word.toNat = BitVec.ofNat 256 (scalarRetained a word) := by
  apply BitVec.eq_of_toNat_eq
  have polynomial := scalar_polynomial (a 0).toNat (a 1).toNat (a 2).toNat (a 3).toNat word.toNat (2^64)
  simp (config := { implicitDefEqProofs := false }) only
    [show ((2 : Nat)^64)^2 = 2^128 by rw [← Nat.pow_mul],
     show ((2 : Nat)^64)^3 = 2^192 by rw [← Nat.pow_mul]] at polynomial
  simp (config := { implicitDefEqProofs := false }) only
    [value, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod, Nat.mul_mod_mod, scalarRetained]
  exact congrArg (fun n : Nat => n % 2^256) polynomial

theorem scalar_limbs_correct (a : Limbs) (word : W64) :
    value (scalarLimbs a word) = value a * BitVec.ofNat 256 word.toNat := by
  have reduced : scalarTotal a word % 2^256 = scalarRetained a word % 2^256 :=
    (Nat.add_mul_mod_self_right (scalarTotal a word) (scalarDiscarded a word) (2^256)).symm.trans
      (congrArg (fun n : Nat => n % 2^256) (scalar_conservation a word))
  have equal : BitVec.ofNat 256 (scalarTotal a word) = BitVec.ofNat 256 (scalarRetained a word) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    exact reduced
  exact (scalarLimbs_value a word).trans (equal.trans (scalar_retained_value a word).symm)

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.scalar_limbs_correct
