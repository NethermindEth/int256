import UInt256.Methods.Subtract.SIMD256Automation
import UInt256.Methods.Reporting.VectorArithmetic

open CIL CIL.Vector UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.entryIndex {

theorem execute_avx_subtract_fast (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : propagation256 a b = 0) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  have _profileAVX : Extracted.profile.avx2 = true := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hav := read256_of_limbs m left (a 0) (a 1) (a 2) (a 3) ha0 ha1 ha2 ha3
  have hbv := read256_of_limbs m right (b 0) (b 1) (b 2) (b 3) hb0 hb1 hb2 hb3
  have correct := speculative_difference_words a b (propagation256_zero a b hp)
  have flag := (independent_borrow_chain a b (propagation256_zero a b hp)).2.2
  change finalBorrow a b = independentBorrow (a 3) (b 3) at flag
  change propagation256 a b = BitVec.ofNat 256 0 at hp
  simp only [propagation256, borrowMask] at hp
  cil_subtract256_execute hav, hbv, hp with (fail)
  refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
  · simp only [SIMD.moveMask_flags, flag32_positive, packed_top_flag,
      independentBorrow, borrow_initial]
    split <;> simp_all
  · intro address
    simp (config := { implicitDefEqProofs := false })
      [speculativeDifference, ← correct, writeBytes_four_limbs,
        borrow_mask_subtract_raw, independentBorrow, fin_val_three]

theorem execute_avx_subtract_cascade (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : propagation256 a b ≠ 0) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  have _profileAVX : Extracted.profile.avx2 = true := by decide
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
  have flag := cascade_subtract_flag a b
  simp only [SIMD.operationMask, SIMD.subtractGenerate, SIMD.subtractPropagate,
    BitVec.ult_eq_decide_lt, show (2 : W32) = BitVec.ofNat 32 2 from rfl,
    show (16 : W32) = BitVec.ofNat 32 16 from rfl] at flag
  refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
  · try simp only [packed_bextr_cascade, flag32_positive]
    split <;> simp_all
  · intro address
    simp (config := { implicitDefEqProofs := false })
      [writeBytes_four_limbs, store4_overwrite_same]

theorem execute_avx_subtract_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  by_cases hp : propagation256 a b = 0
  · exact execute_avx_subtract_fast m left right out frame fuel a b ha hb hp
  · exact execute_avx_subtract_cascade m left right out frame fuel a b ha hb hp

}
end UInt256Proof.Reporting
