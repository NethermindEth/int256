import UInt256.Methods.Reporting.AVXSubtract
import UInt256.Methods.Subtract.Automation
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Reporting.SubtractAutomation

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.entryIndex {

theorem execute_subtract_entry_general (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  have _profileScalar : Extracted.profile.avx2 = false := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
  have hc1 := borrow_bound (a 0) (b 0) (BitVec.ofNat 64 0)
  have hc2 := borrow_bound (a 1) (b 1) (borrow (a 0) (b 0) 0)
  have hc3 := borrow_bound (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0))
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  simp only [differenceWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
  cil_subtract_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
    hc0, hc1, hc2, hc3, hnb, finalBorrow, word_positive,
    UInt256Proof.finalBorrow, FeatureProfile.evaluate with
      (first | cil_reporting_subtract128_call a b | cil_borrow_call | cil_store_call)
  all_goals intro address
  all_goals first
    | solve | simp (config := { implicitDefEqProofs := false }) [*, store4, BitVec.toNat_sub, Nat.add_mod_mod]
    | solve
      | cil_preserved_store
        intro location
        simp [*, write]

#print axioms execute_subtract_entry_general

theorem execute_subtract_entry_small (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if (value a).toNat < (value b).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  have _profileScalar : Extracted.profile.avx2 = false := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hvalue : value (singleLimb (b 0)) = value b :=
    congrArg value (singleLimb_eq b h1 h2 h3)
  have hshape : smallDifference a (b 0) = differenceWords a b := by
    have hsingle : subtractionSingleLimb (b 0) = b := singleLimb_eq b h1 h2 h3
    rw [small_difference_words, hsingle]
  cil_subtract_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, h1, h2, h3
    with (first | cil_reporting_subtract_small_call | cil_borrow_call | cil_store_call)
  all_goals intro address
  all_goals simp [*, store4]

}

theorem execute_subtract_entry_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if (value a).toNat < (value b).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  first
  | solve
    | simpa only [finalBorrow_underflow] using
        execute_avx_subtract_words m left right out frame fuel a b ha hb
  | solve
    |
      by_cases hnb : b 1 ||| b 2 ||| b 3 = BitVec.ofNat 64 0
      · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hnb
        obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
        exact execute_subtract_entry_small m left right out frame fuel a b ha hb h1 h2 h3
      · simpa only [finalBorrow_underflow] using
          execute_subtract_entry_general m left right out frame fuel a b ha hb hnb
  |
    obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
    obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
    cil_subtract_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, finalBorrow, word_positive,
      show (1 : W32) = BitVec.ofNat 32 1 from rfl
      with (first | cil_reporting_subtract128_call a b | cil_reporting_subtract_small_call | cil_borrow_call | cil_store_call)
    all_goals simp (config := { implicitDefEqProofs := false }) only
      [differenceWords, finalBorrow, word_positive, write, ↓reduceIte]

#print axioms execute_subtract_entry_words

end UInt256Proof.Reporting
