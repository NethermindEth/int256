import UInt256.Methods.Add.SmallParents
import UInt256.Methods.Add.General

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

-- Keep the byte-writing function opaque to instruction simplification.
-- Its definition is unfolded only when proving the mathematical postcondition.
def addOutput (m : Memory) (out : Nat) (a b : Limbs) : Memory :=
  writeBytes m out (value a + value b).toNat 32


if_extracted Extracted.addScalarIndex {
theorem execute_scalar_right_small (m : Memory) (left right out frame fuel : Nat)
    (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_scalar_right_small_words m left right out frame fuel a b ha hb h1 h2 h3
  refine ⟨final, flag, he, ?_⟩
  intro address
  rw [hm, store4_value]
  change writeBytes m out (value (smallResult a (b 0))).toNat 32 (.byte address) = _
  rw [small_result_sum, singleLimb_eq b h1 h2 h3]

theorem execute_scalar_left_small (m : Memory) (left right out frame fuel : Nat)
    (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hn : b 1 ||| b 2 ||| b 3 ≠ 0)
    (h1 : a 1 = 0) (h2 : a 2 = 0) (h3 : a 3 = 0) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_scalar_left_small_words m left right out frame fuel a b ha hb hn h1 h2 h3
  refine ⟨final, flag, he, ?_⟩
  intro address
  rw [hm, store4_value]
  change writeBytes m out (value (smallResult b (a 0))).toNat 32 (.byte address) = _
  rw [small_result_sum, singleLimb_eq a h1 h2 h3]
  rw [BitVec.add_comm]

theorem execute_scalar_general (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_scalar_general_words m left right out frame fuel a b ha hb hna hnb
  refine ⟨final, flag, he, ?_⟩
  intro address
  rw [hm, store4_value]
  have hsum := four_limb_sum a b
  dsimp only at hsum
  rw [hsum]

theorem execute_scalar (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  by_cases hnb : b 1 ||| b 2 ||| b 3 = BitVec.ofNat 64 0
  · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hnb
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
    exact execute_scalar_right_small m left right out frame fuel a b ha hb h1 h2 h3
  · by_cases hna : a 1 ||| a 2 ||| a 3 = BitVec.ofNat 64 0
    · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hna
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
      exact execute_scalar_left_small m left right out frame fuel a b ha hb hnb h1 h2 h3
    · exact execute_scalar_general m left right out frame fuel a b ha hb hna hnb

theorem execute_scalar_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hf : executionBound Extracted.program Extracted.addScalarIndex ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = addOutput m out a b (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_scalar m left right out frame 0 a b ha hb
  refine ⟨final, flag, ?_, hm⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf he

theorem execute_scalar_words_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hf : executionBound Extracted.program Extracted.addScalarIndex ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_scalar_at m left right out frame fuel a b ha hb hf
  refine ⟨final, flag, he, ?_⟩
  intro address
  rw [store4_value]
  change final (.byte address) = writeBytes m out (value (sumWords a b)).toNat 32 (.byte address)
  rw [sumWords_sum]
  exact hm address

}

end UInt256Proof
