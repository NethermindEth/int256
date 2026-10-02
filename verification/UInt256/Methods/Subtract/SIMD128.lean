import UInt256.Methods.Subtract.SIMD128Automation

open CIL CIL.Vector UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

if_extracted Extracted.subtractVector128Index {

theorem execute_subtract128_fast (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : propagation128 a b = 0) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.subtractVector128Index)
      Extracted.subtractVector128Index 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if independentBorrow (a 3) (b 3) ≠ BitVec.ofNat 64 0 then
          BitVec.ofNat 32 1 else BitVec.ofNat 32 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (speculativeDifference a b 0) (speculativeDifference a b 1)
        (speculativeDifference a b 2) (speculativeDifference a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hal := read128_of_limbs m left (a 0) (a 1) ha0 ha1
  have hah := read128_of_limbs m (left + 16) (a 2) (a 3) ha2
    (by simpa only [Nat.add_assoc] using ha3)
  have hbl := read128_of_limbs m right (b 0) (b 1) hb0 hb1
  have hbh := read128_of_limbs m (right + 16) (b 2) (b 3) hb2
    (by simpa only [Nat.add_assoc] using hb3)
  change propagation128 a b = BitVec.ofNat 128 0 at hp
  simp only [propagation128, borrowMask, zeroDifferenceMask] at hp
  cil_subtract128_execute hal, hah, hbl, hbh, hp with (fail)
  all_goals refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
  · exact borrow_mask_flag (a 3) (b 3)
  · intro address
    simp [store4, speculativeDifference, write128_two_limbs, borrow_mask_subtract_raw,
      Nat.add_assoc, independentBorrow, write, fin_val_three]

theorem execute_subtract128_fallback (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : propagation128 a b ≠ 0) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.subtractVector128Index)
      Extracted.subtractVector128Index 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ BitVec.ofNat 64 0 then
          BitVec.ofNat 32 1 else BitVec.ofNat 32 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hal := read128_of_limbs m left (a 0) (a 1) ha0 ha1
  have hah := read128_of_limbs m (left + 16) (a 2) (a 3) ha2
    (by simpa only [Nat.add_assoc] using ha3)
  have hbl := read128_of_limbs m right (b 0) (b 1) hb0 hb1
  have hbh := read128_of_limbs m (right + 16) (b 2) (b 3) hb2
    (by simpa only [Nat.add_assoc] using hb3)
  have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
  have hc1 := borrow_bound (a 0) (b 0) (BitVec.ofNat 64 0)
  have hc2 := borrow_bound (a 1) (b 1) (borrow (a 0) (b 0) 0)
  have hc3 := borrow_bound (a 2) (b 2) (borrow (a 1) (b 1) (borrow (a 0) (b 0) 0))
  change propagation128 a b ≠ BitVec.ofNat 128 0 at hp
  simp only [propagation128, borrowMask, zeroDifferenceMask] at hp
  simp only [differenceWords, finalBorrow, Fin.val_zero, Fin.val_one, Fin.val_two,
    fin_val_three, ↓reduceIte]
  cil_subtract128_execute hal, hah, hbl, hbh, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
    hc0, hc1, hc2, hc3, hp, BitVec.pos_iff_ne_zero with
    (first | cil_borrow_call | cil_store_call)
  all_goals intro address
  all_goals first
    | solve | simp [*, store4]
    | solve
      | cil_preserved_store
        intro location
        simp [*, write]
    | solve
      | simp only [store4, BitVec.toNat_sub, Nat.add_mod_mod]
        iterate 4 (apply writeBytes_congr; intro location)
        simp (config := { implicitDefEqProofs := false }) [*, write]

theorem execute_subtract128 (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.subtractVector128Index)
      Extracted.subtractVector128Index 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ BitVec.ofNat 64 0 then
          BitVec.ofNat 32 1 else BitVec.ofNat 32 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  by_cases hp : propagation128 a b = 0
  · have hn := propagation128_zero a b hp
    obtain ⟨final, hr, hm⟩ := execute_subtract128_fast m left right out frame fuel a b ha hb hp
    have hc := (independent_borrow_chain a b hn).2.2
    change finalBorrow a b = independentBorrow (a 3) (b 3) at hc
    rw [speculative_difference_words a b hn] at hm
    exact ⟨final, by simpa only [hc] using hr, hm⟩
  · exact execute_subtract128_fallback m left right out frame fuel a b ha hb hp

theorem execute_subtract128_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hf : executionBound Extracted.program Extracted.subtractVector128Index ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.subtractVector128Index 0
      [.object left, .object right, .object out] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨final, hr, hm⟩ := execute_subtract128 m left right out frame 0 a b ha hb
  refine ⟨final, (if finalBorrow a b ≠ BitVec.ofNat 64 0 then
    BitVec.ofNat 32 1 else BitVec.ofNat 32 0), ?_, hm⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf hr

}

end UInt256Proof
