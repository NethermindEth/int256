import UInt256.Methods.Multiply.CountCarry
open CIL
namespace UInt256Proof.Multiply

theorem two_carries_nat (a b c : W64) :
    (sumHigh a b).toNat + (sumHigh (a + b) c).toNat =
      (a.toNat + b.toNat + c.toNat) / 2^64 := by
  simp only [sumHigh_nat, BitVec.toNat_add]
  omega

theorem sumHigh_pair_swap (a b c : W64) :
    sumHigh a b + sumHigh (a + b) c = sumHigh a c + sumHigh (a + c) b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, two_carries_nat]
  exact congrArg (fun n => n / 2^64 % 2^64) (by omega :
    a.toNat + b.toNat + c.toNat = a.toNat + c.toNat + b.toNat)

theorem countCarry_swap (a b c count : W64) :
    countCarry (a + b) c (countCarry a b count) =
      countCarry (a + c) b (countCarry a c count) := by
  unfold countCarry
  simp only [BitVec.add_assoc, sumHigh_pair_swap]

theorem sumHigh_pair_swap_tail (a b c tail : W64) :
    sumHigh a b + (sumHigh (a + b) c + tail) =
      sumHigh a c + (sumHigh (a + c) b + tail) := by
  rw [← BitVec.add_assoc, sumHigh_pair_swap, BitVec.add_assoc]

end UInt256Proof.Multiply
