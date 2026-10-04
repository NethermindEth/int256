import UInt256.Methods.Multiply.WordProduct
open CIL
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem narrow_polynomial (al ah bl bh : Nat) :
    (al + 2^32 * ah) * (bl + 2^32 * bh) =
      al * bl + 2^32 * (al * bh + ah * bl) + 2^64 * (ah * bh) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  rw [Nat.mul_left_comm al (2^32) bh, Nat.mul_left_comm ah (2^32) bh]
  omega

theorem narrow_low_correct (a b : W64) :
    digitLow a * digitLow b + ((digitLow a * digitHigh b + digitHigh a * digitLow b) <<< 32) =
      lowProduct a b := by
  have polynomial := narrow_polynomial (a.toNat % 2^32) (a.toNat / 2^32)
    (b.toNat % 2^32) (b.toNat / 2^32)
  rw [Nat.mod_add_div, Nat.mod_add_div] at polynomial
  have reduced := congrArg (fun n : Nat => n % 2^64) polynomial
  simp only [Nat.add_mul_mod_self_left] at reduced
  apply BitVec.eq_of_toNat_eq
  simp (config := { implicitDefEqProofs := false }) only [BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, digitLow_nat, digitHigh_nat, lowProduct,
    Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
  rw [Nat.mul_comm _ (2^32)]
  exact reduced.symm

theorem narrow_low_split (a b : W64) :
    digitLow a * digitLow b + ((digitLow a * digitHigh b) <<< 32 +
      (digitHigh a * digitLow b) <<< 32) = lowProduct a b := by
  simpa only [BitVec.shiftLeft_add_distrib] using narrow_low_correct a b

theorem narrow_low_tail (a b tail : W64) :
    digitLow a * digitLow b + ((digitLow a * digitHigh b) <<< 32 +
      ((digitHigh a * digitLow b) <<< 32 + tail)) = lowProduct a b + tail := by
  simpa only [BitVec.add_assoc] using congrArg (fun word => word + tail) (narrow_low_split a b)

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.narrow_low_correct
