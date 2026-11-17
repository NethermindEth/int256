import UInt256.VectorRepresentation

open CIL UInt256Model
namespace UInt256Proof.Equality

theorem value_toNat (a : Limbs) : (value a).toNat =
    (a 0).toNat + (a 1).toNat * 2^64 + (a 2).toNat * 2^128 +
      (a 3).toNat * 2^192 := by
  exact UInt256Proof.value_toNat a

theorem value_pack (a : Limbs) :
    value a = CIL.Vector.pack256 (a 0) (a 1) (a 2) (a 3) := by
  apply BitVec.eq_of_toNat_eq
  rw [value_toNat, pack256_number]
  omega

theorem value_eq_iff (a b : Limbs) : value a = value b ↔
    a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 := by
  constructor
  · intro h
    have limbs := representation_injective a b h
    subst b
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    apply congrArg value
    funext i
    rcases i with ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with h | h | h | h
    all_goals subst i; assumption

/-- The scalar equality reduction observes all four limbs. -/
theorem xor_or_zero_iff (a b : Limbs) :
    (((a 0 ^^^ b 0) ||| (a 1 ^^^ b 1)) ||| (a 2 ^^^ b 2) ||| (a 3 ^^^ b 3)) = BitVec.ofNat 64 0 ↔
      a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 := by
  simp only [BitVec.or_eq_zero_iff (w := 64), BitVec.xor_eq_zero_iff (w := 64), and_assoc]

theorem xor_or_zero_value (a b : Limbs) :
    (((a 0 ^^^ b 0) ||| (a 1 ^^^ b 1)) ||| (a 2 ^^^ b 2) ||| (a 3 ^^^ b 3)) = BitVec.ofNat 64 0 ↔
      value a = value b := by
  rw [xor_or_zero_iff, value_eq_iff]

end UInt256Proof.Equality
