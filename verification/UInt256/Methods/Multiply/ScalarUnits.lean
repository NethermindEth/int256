import UInt256.Methods.Multiply.ScalarValue
import UInt256.Methods.Multiply.ZeroProducts
open CIL UInt256Model
namespace UInt256Proof.Multiply
@[simp] theorem highProduct_one_left (a : W64) : highProduct (BitVec.ofNat 64 1) a = BitVec.ofNat 64 0 := by
  simp only [highProduct, BitVec.toNat_ofNat, show (1 : Nat) % 2^64 = 1 from by decide, Nat.one_mul]
  rw [Nat.div_eq_of_lt a.isLt]
@[simp] theorem lowProduct_one_left (a : W64) : lowProduct (BitVec.ofNat 64 1) a = a := by
  simp [lowProduct]
theorem scalarLimbs_zero (a : Limbs) : scalarLimbs a (BitVec.ofNat 64 0) = fun _ => BitVec.ofNat 64 0 := by
  funext i
  simp [scalarLimbs, scalarCarry, show (3 : Fin 4).val = 3 from rfl]
theorem scalarLimbs_one (a : Limbs) : scalarLimbs a (BitVec.ofNat 64 1) = a := by
  funext i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have := i.isLt
    omega
  rcases cases with rfl | rfl | rfl | rfl <;> simp [scalarLimbs, scalarCarry, show (3 : Fin 4).val = 3 from rfl]
end UInt256Proof.Multiply
