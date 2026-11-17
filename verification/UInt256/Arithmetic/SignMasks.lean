import CIL.SIMD.VectorLemmas
import CIL.SIMD.Evaluation256Lemmas

open CIL CIL.Vector

namespace UInt256Proof.SIMD

theorem ternary_carry_sign (a b : W64) :
    (ternaryLogic a b (a + b) 0xD4).msb = (a + b).ult a := by
  rw [ternary_add]
  simp only [BitVec.msb_or, BitVec.msb_and, BitVec.msb_not]
  simp only [BitVec.msb_eq_decide, Nat.reduceSub]
  by_cases ha : 2^63 ≤ a.toNat <;> by_cases hb : 2^63 ≤ b.toNat <;>
    by_cases hr : 2^63 ≤ (a + b).toNat
  all_goals simp only [ha, hb, hr, decide_true, decide_false]
  all_goals simp [BitVec.ult_eq_decide_lt, BitVec.lt_def]
  all_goals have hia := a.isLt
  all_goals have hib := b.isLt
  all_goals simp only [BitVec.toNat_add] at hr ⊢
  all_goals omega

theorem ternary_borrow_sign (a b : W64) :
    (ternaryLogic a b (a - b) 0x8E).msb = a.ult b := by
  rw [ternary_subtract]
  simp only [BitVec.msb_or, BitVec.msb_and, BitVec.msb_not, BitVec.msb_xor]
  simp only [BitVec.msb_eq_decide, Nat.reduceSub]
  by_cases ha : 2^63 ≤ a.toNat <;> by_cases hb : 2^63 ≤ b.toNat <;>
    by_cases hr : 2^63 ≤ (a - b).toNat
  all_goals simp only [ha, hb, hr, decide_true, decide_false]
  all_goals simp [BitVec.ult_eq_decide_lt, BitVec.lt_def]
  all_goals have hia := a.isLt
  all_goals have hib := b.isLt
  all_goals simp only [BitVec.toNat_sub] at hr ⊢
  all_goals omega

theorem ternary_carry_mask (a b : W64) :
    (ternaryLogic a b (a + b) 0xD4).sshiftRight 63 = mask64 ((a + b).ult a) := by
  rw [arithmetic_sign_mask, ternary_carry_sign]

theorem ternary_borrow_mask (a b : W64) :
    (ternaryLogic a b (a - b) 0x8E).sshiftRight 63 = mask64 (a.ult b) := by
  rw [arithmetic_sign_mask, ternary_borrow_sign]

theorem carry_formula_mask (a b : W64) :
    ((a &&& b) ||| ((~~~(a + b)) &&& (a ||| b))).sshiftRight 63 =
      mask64 ((a + b).ult a) := by
  simpa only [ternary_add] using ternary_carry_mask a b

theorem borrow_formula_mask (a b : W64) :
    (((~~~a) &&& b) ||| ((~~~(a ^^^ b)) &&& (a - b))).sshiftRight 63 =
      mask64 (a.ult b) := by
  simpa only [ternary_subtract] using ternary_borrow_mask a b

theorem ternary_carry_packed (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    map256 (fun x => x.sshiftRight 63)
      (ternaryLogic (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3)
        (pack256 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3)) 0xD4) =
    pack256 (mask64 ((a0 + b0).ult a0)) (mask64 ((a1 + b1).ult a1))
      (mask64 ((a2 + b2).ult a2)) (mask64 ((a3 + b3).ult a3)) := by
  rw [ternary_add]
  simp only [pack256_and, pack256_or, pack256_not, map256,
    lane256_0, lane256_1, lane256_2, lane256_3, carry_formula_mask]

theorem ternary_borrow_packed (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    map256 (fun x => x.sshiftRight 63)
      (ternaryLogic (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3)
        (pack256 (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3)) 0x8E) =
    pack256 (mask64 (a0.ult b0)) (mask64 (a1.ult b1))
      (mask64 (a2.ult b2)) (mask64 (a3.ult b3)) := by
  rw [ternary_subtract]
  simp only [pack256_and, pack256_or, pack256_not, pack256_xor, map256,
    lane256_0, lane256_1, lane256_2, lane256_3, borrow_formula_mask]

theorem ternary_carry_packed_normal (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    map256 (fun x => x.sshiftRight 63)
      (ternaryLogic (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3)
        (pack256 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3)) (BitVec.ofNat 8 212)) =
    pack256 (mask64 ((a0 + b0).ult a0)) (mask64 ((a1 + b1).ult a1))
      (mask64 ((a2 + b2).ult a2)) (mask64 ((a3 + b3).ult a3)) :=
  ternary_carry_packed a0 a1 a2 a3 b0 b1 b2 b3

theorem ternary_borrow_packed_normal (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    map256 (fun x => x.sshiftRight 63)
      (ternaryLogic (pack256 a0 a1 a2 a3) (pack256 b0 b1 b2 b3)
        (pack256 (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3)) (BitVec.ofNat 8 142)) =
    pack256 (mask64 (a0.ult b0)) (mask64 (a1.ult b1))
      (mask64 (a2.ult b2)) (mask64 (a3.ult b3)) :=
  ternary_borrow_packed a0 a1 a2 a3 b0 b1 b2 b3

end UInt256Proof.SIMD
