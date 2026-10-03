import UInt256.Methods.Shift.Limbs
import UInt256.VectorRepresentation

open CIL UInt256Model

namespace UInt256Proof.Shift

theorem pack_vector (a0 a1 a2 a3 : W64) :
    pack a0 a1 a2 a3 = CIL.Vector.pack256 a0 a1 a2 a3 := by
  simpa only [pack, CIL.Vector.pack256, BitVec.cast_eq] using
    (BitVec.append_assoc (x₁ := a3 ++ a2) (x₂ := a1) (x₃ := a0))

theorem pack_value (limbs : Limbs) :
    pack (limbs 0) (limbs 1) (limbs 2) (limbs 3) = value limbs := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_vector, pack256_number]
  simp only [value, BitVec.toNat_ofNat]
  have bound := (CIL.Vector.pack256 (limbs 0) (limbs 1) (limbs 2) (limbs 3)).isLt
  rw [pack256_number, Nat.mul_add] at bound
  rw [Nat.mul_add]
  omega

theorem write_pack (memory : Memory) (out : Nat) (a0 a1 a2 a3 : W64) :
    writeBytes memory out (pack a0 a1 a2 a3).toNat 32 = store4 memory out a0 a1 a2 a3 := by
  rw [pack_vector]
  exact writeBytes_four_limbs memory out a0 a1 a2 a3

end UInt256Proof.Shift
