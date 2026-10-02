import UInt256.Methods.Subtract.SIMD256Automation

open CIL CIL.Vector UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

if_extracted Extracted.subtractVector256Index {

theorem execute_subtract256_fast (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : propagation256 a b = 0) :
    ∃ final flag, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.subtractVector256Index)
      Extracted.subtractVector256Index 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hav := read256_of_limbs m left (a 0) (a 1) (a 2) (a 3) ha0 ha1 ha2 ha3
  have hbv := read256_of_limbs m right (b 0) (b 1) (b 2) (b 3) hb0 hb1 hb2 hb3
  have correct := speculative_difference_words a b (propagation256_zero a b hp)
  change propagation256 a b = BitVec.ofNat 256 0 at hp
  simp only [propagation256, borrowMask] at hp
  cil_subtract256_execute hav, hbv, hp with (fail)
  all_goals intro address
  all_goals simp (config := { implicitDefEqProofs := false })
    [speculativeDifference, ← correct, writeBytes_four_limbs,
      borrow_mask_subtract_raw, independentBorrow, fin_val_three]

theorem execute_subtract256_cascade (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : propagation256 a b ≠ 0) :
    ∃ final flag, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.subtractVector256Index)
      Extracted.subtractVector256Index 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hav := read256_of_limbs m left (a 0) (a 1) (a 2) (a 3) ha0 ha1 ha2 ha3
  have hbv := read256_of_limbs m right (b 0) (b 1) (b 2) (b 3) hb0 hb1 hb2 hb3
  have lookup : ∀ memory, read256 memory (.static Extracted.broadcastLookupData
      (32 * (SIMD.cascadeIndex (SIMD.operationMask (SIMD.subtractGenerate a b))
        (SIMD.operationMask (SIMD.subtractPropagate a b))).toNat)) =
      some (.v256 (SIMD.cascadeVector (SIMD.cascadeIndex
        (SIMD.operationMask (SIMD.subtractGenerate a b))
        (SIMD.operationMask (SIMD.subtractPropagate a b))))) := fun memory =>
    SIMD.read_cascade_lookup _ SIMD.extracted_lookup_valid _ _ memory
  have correction := SIMD.subtract_cascade_vector a b
  simp only [SIMD.operationMask, SIMD.subtractGenerate, SIMD.subtractPropagate,
    BitVec.ult_eq_decide_lt, SIMD.cascadeIndex] at lookup
  simp only [SIMD.operationMask, SIMD.subtractGenerate, SIMD.subtractPropagate,
    BitVec.ult_eq_decide_lt, SIMD.cascadeIndex, SIMD.packedLimbs, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3] at correction
  simp only [show (2 : W32) = BitVec.ofNat 32 2 from rfl,
    show (15 : W32) = BitVec.ofNat 32 15 from rfl] at lookup correction
  simp only [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.add_mod_mod] at lookup
  change propagation256 a b ≠ BitVec.ofNat 256 0 at hp
  simp only [propagation256, borrowMask] at hp
  cil_subtract256_execute hav, hbv, hp, lookup, correction, SIMD.moveMask_flags,
    eval_add_static_vector, SIMD.cascade_native_offset with cil_lookup_call
  all_goals intro address
  all_goals simp (config := { implicitDefEqProofs := false })
    [writeBytes_four_limbs, store4_overwrite_same]

theorem execute_subtract256 (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final flag, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.subtractVector256Index)
      Extracted.subtractVector256Index 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  by_cases hp : propagation256 a b = 0
  · exact execute_subtract256_fast m left right out frame fuel a b ha hb hp
  · exact execute_subtract256_cascade m left right out frame fuel a b ha hb hp

theorem execute_subtract256_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hf : executionBound Extracted.program Extracted.subtractVector256Index ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.subtractVector256Index 0
      [.object left, .object right, .object out] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨final, flag, hr, hm⟩ := execute_subtract256 m left right out frame 0 a b ha hb
  exact ⟨final, flag, run_of_le _ _ _ _ _ _ _ _ _ _ hf hr, hm⟩

}

end UInt256Proof
