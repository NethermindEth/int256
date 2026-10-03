import Extracted
import UInt256.VectorRepresentation
import UInt256.Methods.Add.SIMD256Arithmetic
import UInt256.LookupAutomation
import UInt256.Methods.Reporting.VectorArithmetic

open CIL CIL.Vector UInt256Model UInt256Proof.SIMD
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

theorem read256_local (m : Memory) (frame index : Nat) :
    read256 m (.local frame index) = do
      let .v256 bits ← m (.local frame index) | none
      return .v256 bits := rfl

theorem permute_incoming (a b c d : W64) :
    permute4x64 (pack256 a b c d) (BitVec.ofNat 8 144) = pack256 a a b c :=
  avx2_permute_incoming a b c d
theorem blend_incoming (a b c d : W64) :
    blend32 (pack256 a b c d) (BitVec.ofNat 256 0) (BitVec.ofNat 8 3) =
      pack256 (BitVec.ofNat 64 0) b c d := avx2_blend_incoming a b c d
theorem ones_packed :
    BitVec.ofNat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 =
      pack256 (BitVec.allOnes 64) (BitVec.allOnes 64) (BitVec.allOnes 64) (BitVec.allOnes 64) := by decide

if_extracted Extracted.entryIndex {
theorem execute_avx_add_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  have _profileAVX : Extracted.profile.avx2 = true := by decide
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  have hal := read256_of_limbs m left (a 0) (a 1) (a 2) (a 3) ha0 ha1 ha2 ha3
  have hbl := read256_of_limbs m right (b 0) (b 1) (b 2) (b 3) hb0 hb1 hb2 hb3
  have lookup : ∀ memory, read256 memory (.static Extracted.broadcastLookupData
      (32 * (cascadeIndex (operationMask (addGenerate a b))
        (operationMask (addPropagate a b))).toNat)) =
      some (.v256 (cascadeVector (cascadeIndex (operationMask (addGenerate a b))
        (operationMask (addPropagate a b))))) := fun memory =>
    read_cascade_lookup _ extracted_lookup_valid _ _ memory
  have correction := add_cascade_vector a b
  simp only [operationMask, addGenerate, addPropagate, cascadeIndex] at lookup
  simp only [operationMask, addGenerate, addPropagate, cascadeIndex, packedLimbs, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3] at correction
  simp only [show BitVec.allOnes 64 = BitVec.ofNat 64 18446744073709551615 from rfl]
    at lookup correction
  simp only [show (2 : W32) = BitVec.ofNat 32 2 from rfl,
    show (15 : W32) = BitVec.ofNat 32 15 from rfl] at lookup correction
  simp only [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.reducePow, Nat.reduceMod] at lookup
  cil_execute_core hal, hbl, evalMemory, unsafeAsRef, write256, read256_local, write,
    read256_write_local, zip256, lane256_0, lane256_1, lane256_2, lane256_3,
    permute_incoming, blend_incoming, and_incoming, avx512_incoming_normal, avx2_incoming_mask, ones_packed,
    ternary_carry_packed_normal, pack256_and, pack256_or, pack256_not, and_all_ones64, and_zero64,
    intrinsic_add256, intrinsic_lt256, intrinsic_eq256, intrinsic_sub256,
    intrinsic_reinterpret256, intrinsic_zero256, intrinsic_ones256, intrinsic_create256, intrinsic_and256,
    intrinsic_permute256, intrinsic_blend256, intrinsic_align256,
    intrinsic_ternary_add256, intrinsic_sign256, intrinsic_movemask256, intrinsic_testz256,
    moveMask_flags, lookup, correction, offsetValue, cascade_native_offset
    with cil_lookup_call
  · rename_i guard
    have guards := full_mask_guard _ _ _ _ _ _ guard
    have h1 : ¬ (addPropagate a b 1 && addGenerate a b 0) = true := by
      simpa only [addGenerate, addPropagate, show BitVec.allOnes 64 = BitVec.ofNat 64 18446744073709551615 from rfl] using guards.1
    have h2 : ¬ (addPropagate a b 2 && addGenerate a b 1) = true := by
      simpa only [addGenerate, addPropagate, show BitVec.allOnes 64 = BitVec.ofNat 64 18446744073709551615 from rfl] using guards.2.1
    have h3 : ¬ (addPropagate a b 3 && addGenerate a b 2) = true := by
      simpa only [addGenerate, addPropagate, show BitVec.allOnes 64 = BitVec.ofNat 64 18446744073709551615 from rfl] using guards.2.2
    have correct := fast_correction a b h1 h2
    have flag := fast_add_flag a b h1 h2 h3
    simp only [carryMask] at correct
    refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
    · simp only [flag32_positive, packed_top_flag, flag]
      cases h : addGenerate a b 3 <;> simp_all [addGenerate]
    · intro address
      simp (config := { implicitDefEqProofs := false }) only [write, reduceCtorEq, ↓reduceIte]
      rw [correct]
      exact congrFun (writeBytes_four_limbs m out _ _ _ _) (.byte address)
  · have flag := cascade_add_flag a b
    simp only [operationMask, addGenerate, addPropagate,
      show BitVec.allOnes 64 = BitVec.ofNat 64 18446744073709551615 from rfl,
      show (2 : W32) = BitVec.ofNat 32 2 from rfl,
      show (16 : W32) = BitVec.ofNat 32 16 from rfl] at flag
    refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
    · simp only [flag32_positive]
      split <;> simp_all
    · intro address
      simp (config := { implicitDefEqProofs := false }) only [write, reduceCtorEq, ↓reduceIte]
      rw [writeBytes_overwrite_same, writeBytes_four_limbs]

}
end UInt256Proof.Reporting
