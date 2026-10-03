import UInt256.Methods.Reporting.Automation
import UInt256.Methods.Reporting.AVXAdd

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.entryIndex {

theorem execute_add_entry_general (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  have _profileScalar : Extracted.profile.avx2 = false := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change a 1 ||| a 2 ||| a 3 ≠ BitVec.ofNat 64 0 at hna
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  simp only [sumWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hna, hnb,
    finalCarry, FeatureProfile.evaluate, word_positive,
    show (1 : W32) = BitVec.ofNat 32 1 from rfl
    with (first | cil_reporting_add128_call a b | cil_carry_call | cil_store_call)
  intro address
  cil_preserved_store
  intro location
  simp [*, write]

#print axioms execute_add_entry_general

theorem execute_add_entry_right_small (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  have _profileScalar : Extracted.profile.avx2 = false := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hvalue : value (singleLimb (b 0)) = value b :=
    congrArg value (singleLimb_eq b h1 h2 h3)
  have hshape : smallResult a (b 0) = sumWords a b := by
    rw [smallResult_words, singleLimb_eq b h1 h2 h3]
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, h1, h2, h3
    with (first | cil_reporting_small_call | cil_carry_call | cil_store_call)
  all_goals first
    | solve | simp [hvalue, hshape]
    | solve
      | intro address
        simp [*, store4]

#print axioms execute_add_entry_right_small

theorem execute_add_entry_left_small (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hn : b 1 ||| b 2 ||| b 3 ≠ 0) (h1 : a 1 = 0) (h2 : a 2 = 0) (h3 : a 3 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  have _profileScalar : Extracted.profile.avx2 = false := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hn
  have hvalue : value (singleLimb (a 0)) = value a :=
    congrArg value (singleLimb_eq a h1 h2 h3)
  have hshape : smallResult b (a 0) = sumWords a b := by
    rw [smallResult_words, singleLimb_eq a h1 h2 h3, sumWords_comm]
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hn, h1, h2, h3
    with (first | cil_reporting_small_call | cil_carry_call | cil_store_call)
  all_goals refine ⟨_, ⟨rfl, by simp [Nat.add_comm]⟩, ?_⟩
  all_goals intro address
  all_goals simp [*, store4]

}

theorem execute_add_entry_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  first
  | solve
    | simpa only [finalCarry_overflow] using
        execute_avx_add_words m left right out frame fuel a b ha hb
  | solve
    |
      by_cases hnb : b 1 ||| b 2 ||| b 3 = BitVec.ofNat 64 0
      · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hnb
        obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
        exact execute_add_entry_right_small m left right out frame fuel a b ha hb h1 h2 h3
      · by_cases hna : a 1 ||| a 2 ||| a 3 = BitVec.ofNat 64 0
        · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hna
          obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
          exact execute_add_entry_left_small m left right out frame fuel a b ha hb hnb h1 h2 h3
        · simpa only [finalCarry_overflow] using
            execute_add_entry_general m left right out frame fuel a b ha hb hna hnb
  |
    obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
    obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
    cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, finalCarry, word_positive,
      show (1 : W32) = BitVec.ofNat 32 1 from rfl
      with (first | cil_reporting_add128_call a b | cil_reporting_small_call | cil_carry_call | cil_store_call)
    all_goals simp (config := { implicitDefEqProofs := false }) only
      [sumWords, finalCarry, word_positive, write, ↓reduceIte]

#print axioms execute_add_entry_words

end UInt256Proof.Reporting
