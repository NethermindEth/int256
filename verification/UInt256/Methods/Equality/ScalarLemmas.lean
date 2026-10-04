import UInt256.Methods.Equality.Lemmas
open CIL UInt256Model
namespace UInt256Proof.Equality
@[simp] theorem word32_mod64 (word : W32) :
    word.toNat % 18446744073709551616 = word.toNat := by
  apply Nat.mod_eq_of_lt
  have bound := word.isLt
  omega

theorem value_eq_word (a : Limbs) (word : W64) :
    (value a).toNat = word.toNat ↔
      a 0 = word ∧ a 1 = BitVec.ofNat 64 0 ∧ a 2 = BitVec.ofNat 64 0 ∧ a 3 = BitVec.ofNat 64 0 := by
  rw [value_toNat]
  simp only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod]
  omega
theorem value_eq_word32 (a : Limbs) (word : W32) :
    (value a).toNat = word.toNat ↔
      a 0 = word.setWidth 64 ∧ a 1 = BitVec.ofNat 64 0 ∧
      a 2 = BitVec.ofNat 64 0 ∧ a 3 = BitVec.ofNat 64 0 := by
  have same : (word.setWidth 64).toNat = word.toNat :=
    BitVec.toNat_setWidth_of_le (by decide)
  simpa only [same] using value_eq_word a (word.setWidth 64)
theorem setWidth32_eq_value (word : W32) (a : Limbs) :
    word.setWidth 256 = value a ↔ (value a).toNat = word.toNat := by
  rw [← BitVec.toNat_inj]
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 256)]
  exact eq_comm

end UInt256Proof.Equality
