import UInt256.Methods.Add.EntryAutomation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem execute_entry_general_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
  have hc1 := carry_bound (a 0) (b 0) (BitVec.ofNat 64 0) hc0
  have hc2 := carry_bound (a 1) (b 1) _ hc1
  have hc3 := carry_bound (a 2) (b 2) _ hc2
  change a 1 ||| a 2 ||| a 3 ≠ BitVec.ofNat 64 0 at hna
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  simp only [sumWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hna, hnb
    with (first | cil_scalar_call | cil_small_call | cil_carry_call | cil_store_call)
  all_goals intro address
  all_goals first
    | solve | simp [*, store4, sumWords, fin_val_three, carry_tail_zero, carry_head_zero]
    | solve
      | simp_all only [BitVec.add_comm, add_overflow_right]
        simp [*, store4, sumWords, fin_val_three, carry_head_zero,
          carry_zero, carry_one, BitVec.add_comm, Nat.add_comm, add_overflow_right]

theorem execute_entry_right_small_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
  have hc1 := carry_bound (a 0) (b 0) (BitVec.ofNat 64 0) hc0
  have hc2 := carry_bound (a 1) (b 1) _ hc1
  have hc3 := carry_bound (a 2) (b 2) _ hc2
  have hshape : smallResult a (b 0) = sumWords a b := by
    rw [smallResult_words, singleLimb_eq b h1 h2 h3]
  simp only [sumWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, h1, h2, h3, hshape
    with (first | cil_scalar_call | cil_small_call | cil_carry_call | cil_store_call)
  all_goals intro address
  all_goals first
    | solve | simp [*, store4, sumWords, fin_val_three, carry_tail_zero, carry_head_zero]
    | solve
      | simp_all only [BitVec.add_comm, add_overflow_right]
        simp [*, store4, sumWords, fin_val_three, carry_head_zero,
          carry_zero, carry_one, BitVec.add_comm, Nat.add_comm, add_overflow_right]

theorem execute_entry_left_small_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hn : b 1 ||| b 2 ||| b 3 ≠ 0) (h1 : a 1 = 0) (h2 : a 2 = 0) (h3 : a 3 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
  have hc1 := carry_bound (a 0) (b 0) (BitVec.ofNat 64 0) hc0
  have hc2 := carry_bound (a 1) (b 1) _ hc1
  have hc3 := carry_bound (a 2) (b 2) _ hc2
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hn
  have hshape : smallResult b (a 0) = sumWords a b := by
    rw [smallResult_words, singleLimb_eq a h1 h2 h3, sumWords_comm]
  simp only [sumWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hn, h1, h2, h3, hshape
    with (first | cil_scalar_call | cil_small_call | cil_carry_call | cil_store_call)
  all_goals intro address
  all_goals first
    | solve | simp [*, store4, sumWords, fin_val_three, carry_tail_zero, carry_head_zero]
    | solve
      | simp_all only [BitVec.add_comm, add_overflow_right]
        simp [*, store4, sumWords, fin_val_three, carry_head_zero,
          carry_zero, carry_one, BitVec.add_comm, Nat.add_comm, add_overflow_right]

theorem execute_entry_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  by_cases hnb : b 1 ||| b 2 ||| b 3 = BitVec.ofNat 64 0
  · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hnb
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
    exact execute_entry_right_small_words m left right out frame fuel a b ha hb h1 h2 h3
  · by_cases hna : a 1 ||| a 2 ||| a 3 = BitVec.ofNat 64 0
    · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hna
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
      exact execute_entry_left_small_words m left right out frame fuel a b ha hb hnb h1 h2 h3
    · exact execute_entry_general_words m left right out frame fuel a b ha hb hna hnb

theorem execute_entry (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))):
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = addOutput m out a b (.byte address) := by
  obtain ⟨final, he, hm⟩ := execute_entry_words m left right out frame fuel a b ha hb
  refine ⟨final, he, ?_⟩
  intro address
  rw [hm, store4_value]
  change writeBytes m out (value (sumWords a b)).toNat 32 (.byte address) = _
  rw [sumWords_sum]
  rfl

end UInt256Proof
