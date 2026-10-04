import UInt256.Methods.Multiply.CountCarry
open CIL
namespace UInt256Proof.Multiply
@[simp] theorem lowProduct_zero_left (a : W64) : lowProduct (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by simp [lowProduct]
@[simp] theorem lowProduct_zero_right (a : W64) : lowProduct a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by simp [lowProduct]
@[simp] theorem highProduct_zero_left (a : W64) : highProduct (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by simp [highProduct]
@[simp] theorem highProduct_zero_right (a : W64) : highProduct a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by simp [highProduct]
@[simp] theorem sumHigh_zero_right (a : W64) : sumHigh a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by
  simp only [sumHigh, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  rw [Nat.div_eq_of_lt a.isLt]
@[simp] theorem sumHigh_zero_left (a : W64) : sumHigh (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by
  simpa only [sumHigh, Nat.add_comm] using sumHigh_zero_right a
end UInt256Proof.Multiply
