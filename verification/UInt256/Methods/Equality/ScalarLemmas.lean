import UInt256.Methods.Equality.Lemmas
open CIL UInt256Model
namespace UInt256Proof.Equality
theorem value_eq_word (a : Limbs) (word : W64) :
    (value a).toNat = word.toNat ↔
      a 0 = word ∧ a 1 = BitVec.ofNat 64 0 ∧ a 2 = BitVec.ofNat 64 0 ∧ a 3 = BitVec.ofNat 64 0 := by
  rw [value_toNat]
  simp only [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.zero_mod]
  omega
end UInt256Proof.Equality
