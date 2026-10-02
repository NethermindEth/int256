import UInt256.Methods.Subtract.SIMDCalls

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof

theorem execute_subtract_entry_general_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
  have hc1 := borrow_bound (a 0) (b 0) (BitVec.ofNat 64 0)
  have hc2 := borrow_bound (a 1) (b 1) (borrow (a 0) (b 0) 0)
  have hc3 := borrow_bound (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0))
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  simp only [differenceWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
  cil_subtract_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3,
    hnb, borrow_expression, borrow_alternative_expression, FeatureProfile.evaluate with
    (first | cil_subtract256_call a b | cil_subtract128_call a b | cil_borrow_call | cil_store_call)
  all_goals intro address
  all_goals first
    | solve | simp (config := { implicitDefEqProofs := false }) [*, store4, BitVec.toNat_sub, Nat.add_mod_mod]
    | solve
      | cil_preserved_store
        intro location
        simp [*, write]

theorem execute_subtract_entry_small_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = store4 m out
        (smallDifference a (b 0) 0) (smallDifference a (b 0) 1)
        (smallDifference a (b 0) 2) (smallDifference a (b 0) 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hshape : subtractionSingleLimb (b 0) = b := singleLimb_eq b h1 h2 h3
  have hsmallWords : smallDifference a (b 0) = differenceWords a b := by
    rw [small_difference_words, hshape]
  cil_subtract_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, h1, h2, h3,
    hsmallWords, FeatureProfile.evaluate with
    (first | cil_subtract256_call a b | cil_subtract128_call a b | cil_subtract_small_call | cil_borrow_call | cil_store_call)
  all_goals intro address
  all_goals simp only [← hsmallWords]
  all_goals clear hsmallWords
  all_goals first
    | solve | simp [*, store4, smallDifference, differenceWords, fin_val_three]
    | solve
      | cil_preserved_store
        intro location
        simp [*, write]

def subtractOutput (m : Memory) (out : Nat) (a b : Limbs) : Memory :=
  writeBytes m out (value a - value b).toNat 32

theorem execute_subtract_entry (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = subtractOutput m out a b (.byte address) := by
  by_cases hsmall : b 1 ||| b 2 ||| b 3 = 0
  · have hz : b 1 = 0 ∧ b 2 = 0 ∧ b 3 = 0 := by
      change b 1 ||| b 2 ||| b 3 = BitVec.ofNat 64 0 at hsmall
      obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hsmall
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
      exact ⟨h1, h2, h3⟩
    obtain ⟨final, he, hm⟩ := execute_subtract_entry_small_words m left right out frame fuel a b ha hb hz.1 hz.2.1 hz.2.2
    refine ⟨final, he, ?_⟩
    have hshape : subtractionSingleLimb (b 0) = b := by
      funext i
      rcases i with ⟨i, hi⟩
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with h | h | h | h
      all_goals subst i; simp [subtractionSingleLimb, hz]
    intro address
    rw [hm, store4_value]
    change writeBytes m out (value (smallDifference a (b 0))).toNat 32 (.byte address) = _
    rw [small_difference_words, hshape, four_limb_difference]
    rfl
  · obtain ⟨final, he, hm⟩ := execute_subtract_entry_general_words m left right out frame fuel a b ha hb hsmall
    refine ⟨final, he, ?_⟩
    intro address
    rw [hm, store4_value]
    change writeBytes m out (value (differenceWords a b)).toNat 32 (.byte address) = _
    rw [four_limb_difference]
    rfl

end UInt256Proof
