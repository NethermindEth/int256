import UInt256.Methods.Add.SIMD128Arithmetic

open CIL CIL.Vector UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.SIMD

if_extracted Extracted.addVector128Index {

theorem execute_sse128_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (_hp : Extracted.profile.advSimd = false) :
    ∃ final flag, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.addVector128Index)
      Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 0)] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  first
  | solve
    | have h : Extracted.profile.advSimd = true := by decide
      have impossible : (false : Bool) = true := _hp.symm.trans h
      cases impossible
  |
    obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
    obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
    have hal := read128_of_limbs m left (a 0) (a 1) ha0 ha1
    have hah := read128_of_limbs m (left + 16) (a 2) (a 3) ha2 (by simpa [Nat.add_assoc] using ha3)
    have hbl := read128_of_limbs m right (b 0) (b 1) hb0 hb1
    have hbh := read128_of_limbs m (right + 16) (b 2) (b 3) hb2 (by simpa [Nat.add_assoc] using hb3)
    have hzero : BitVec.ofNat 128 0 = pack128 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := by decide
    have hc0 : (BitVec.ofNat 64 0).toNat ≤ 1 := by decide
    have hc1 := carry_bound (a 0) (b 0) (BitVec.ofNat 64 0) hc0
    have hc2 := carry_bound (a 1) (b 1) _ hc1
    have hc3 := carry_bound (a 2) (b 2) _ hc2
    simp only [sumWords, Fin.val_zero, Fin.val_one, Fin.val_two, fin_val_three, ↓reduceIte]
    cil_execute hal, hah, hbl, hbh, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
      hc0, hc1, hc2, hc3, hzero, evalMemory, unsafeAsRef,
      offsetValue, unsafe_add16_one, write128, read128_write_local,
      zip128, lane128_0, lane128_1, pack128_and, pack128_or,
      sse_arm_alignment, sse_incoming_low, adv_incoming, carryMask
      with (first | cil_vector_carry_call | cil_store_call)
    all_goals first
      | rename_i branch
        have hbranch : propagationLo a b ||| propagationHi a b = BitVec.ofNat 128 0 := by
          simpa (config := { implicitDefEqProofs := false }) only [propagationLo,
            propagationHi, correctedLo, correctedHi, carryMask, hzero,
            zip128, lane128_0, lane128_1, pack128_and, pack128_or, BitVec.and_zero, BitVec.zero_or] using branch
        intro address
        simpa [correctedLo,
          correctedHi, carryMask, sumWords, Fin.val_zero, Fin.val_one,
          Fin.val_two, fin_val_three, ↓reduceIte] using
          congrFun (corrected_stores_words m out a b hbranch) (.byte address)
      | intro address
        first
          | solve | simp (config := { implicitDefEqProofs := false }) [*, store4]
          | solve
            | try simp only [*]
              cil_preserved_store
              intro location
              simp (config := { implicitDefEqProofs := false }) [*, write]
          | solve
            | simp only [store4, BitVec.toNat_add, Nat.mod_add_mod, Nat.reducePow]
              repeat first | apply writeBytes_congr | intro location
              all_goals simp (config := { implicitDefEqProofs := false }) [*, write]

theorem execute_sse128_words_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : Extracted.profile.advSimd = false)
    (hf : executionBound Extracted.program Extracted.addVector128Index ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 0)] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_sse128_words m left right out frame 0 a b ha hb hp
  refine ⟨final, flag, ?_, hm⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf he

}
end UInt256Proof.SIMD
