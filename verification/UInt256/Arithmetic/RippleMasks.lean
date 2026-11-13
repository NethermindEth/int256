import UInt256.Arithmetic.Carry
import UInt256.Arithmetic.Borrow
import CIL.SIMD.Vector

open CIL CIL.Vector

namespace UInt256Proof.SIMD

theorem increment_wrap_iff (x : W64) : x + 1 = 0 ↔ x = BitVec.allOnes 64 := by
  have hx := x.isLt
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at hn
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_allOnes]
    omega
  · intro h
    subst x
    decide

theorem carry_not_full (x y : W64) (full : x + y = BitVec.allOnes 64) :
    ¬ x + y < x := by
  have hx := x.isLt
  have hy := y.isLt
  have hf := congrArg BitVec.toNat full
  simp only [BitVec.toNat_add, BitVec.toNat_allOnes] at hf
  simp only [BitVec.lt_def, BitVec.toNat_add]
  omega

/-- Ripple recurrence shared by 128-bit correction and the AVX lookup path. -/
theorem carry_generated_propagated (x y incoming : W64) (bound : incoming.toNat ≤ 1) :
    carry x y incoming =
      if x + y < x ∨ (x + y = BitVec.allOnes 64 ∧ incoming = 1) then 1 else 0 := by
  have hi : incoming = 0 ∨ incoming = 1 := by
    apply (show incoming.toNat = 0 ∨ incoming.toNat = 1 from by omega).elim
    · intro h; left; exact BitVec.eq_of_toNat_eq (by simpa using h)
    · intro h; right; exact BitVec.eq_of_toNat_eq (by simpa using h)
  rcases hi with hi | hi
  · subst incoming
    rw [← carry_expression x y 0 (by decide)]
    simp
  · subst incoming
    have inc : x + y + 1 < x + y ↔ x + y = BitVec.allOnes 64 :=
      (increment_lt (x + y)).trans (increment_wrap_iff (x + y))
    rw [← carry_expression x y 1 (by decide)]
    simp only [BitVec.ofNat_eq_ofNat] at inc ⊢
    by_cases full : x + y = BitVec.allOnes 64
    · have noCarry := carry_not_full x y full
      have yesInc := inc.mpr full
      simp only [noCarry, yesInc, ↓reduceIte]
      simp only [full, and_self, or_true, ↓reduceIte]
      rfl
    · have noInc : ¬ x + y + BitVec.ofNat 64 1 < x + y := fun h => full (inc.mp h)
      simp only [noInc, full, ↓reduceIte, and_true, or_false,
        BitVec.add_zero]

theorem borrow_generated_propagated (x y incoming : W64) (bound : incoming.toNat ≤ 1) :
    borrow x y incoming =
      if x < y ∨ (x = y ∧ incoming = 1) then 1 else 0 := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases one : incoming = 1
  · subst incoming
    simp only [borrow, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, BitVec.lt_def]
    have equal : x = y ↔ x.toNat = y.toNat :=
      ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
    simp only [equal]
    congr 1
    apply propext
    simp only [Nat.reducePow, Nat.reduceMod, and_true]
    omega
  · have hn : incoming.toNat = 0 := by
      have hne : incoming.toNat ≠ 1 := fun h => one (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have hz : incoming = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst incoming
    simp [borrow, BitVec.lt_def]

end UInt256Proof.SIMD
