import UInt256.Methods.Multiply.Calls
import UInt256.Methods.Multiply.ProductValue

namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

/-- A notation for arithmetic expressions, not evidence that a local is readable.
    Every execution use separately proves `known index = some value`. -/
def localWord (known : Nat → Option (BitVec 64)) (index : Nat) : BitVec 64 := (known index).getD 0

def widenWords (known : Nat → Option (BitVec 64)) (left right target result : Nat) :=
  rememberWord (rememberWord known target (lowProduct (localWord known left) (localWord known right)))
    result (highProduct (localWord known left) (localWord known right))

def countWords (known : Nat → Option (BitVec 64)) (left right counter result : Nat) :=
  rememberWord (rememberWord known counter
    (countCarry (localWord known left) (localWord known right) (localWord known counter)))
    result (localWord known left + localWord known right)

end UInt256Proof.Multiply.BothTwo
namespace UInt256Proof.Multiply
@[simp] theorem lowProduct_zero_left (a : BitVec 64) : lowProduct (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by simp [lowProduct]
@[simp] theorem lowProduct_zero_right (a : BitVec 64) : lowProduct a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by simp [lowProduct]
@[simp] theorem highProduct_zero_left (a : BitVec 64) : highProduct (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by simp [highProduct]
@[simp] theorem highProduct_zero_right (a : BitVec 64) : highProduct a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by simp [highProduct]
@[simp] theorem sumHigh_zero_right (a : BitVec 64) : sumHigh a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by
  simp only [sumHigh, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  rw [Nat.div_eq_of_lt a.isLt]
@[simp] theorem sumHigh_zero_left (a : BitVec 64) : sumHigh (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by
  simpa only [sumHigh, Nat.add_comm] using sumHigh_zero_right a
end UInt256Proof.Multiply
