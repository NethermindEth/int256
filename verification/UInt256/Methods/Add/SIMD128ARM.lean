import UInt256.Methods.Add.SIMD128Arithmetic

open CIL CIL.Vector UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.SIMD

if_extracted Extracted.addVector128Index {

/-- Execute the complete wrapping ARM vector helper, including its early stores and both repair hops. -/
theorem execute_arm128 (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (_hp : Extracted.profile.advSimd = true) :
    ∃ final flag, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.addVector128Index)
      Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 0)] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = armStores m out a b (.byte address) := by
  first
  | solve
    | have h : Extracted.profile.advSimd = false := by decide
      have impossible : (true : Bool) = false := _hp.symm.trans h
      cases impossible
  |
    obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
    obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
    have hal := read128_of_limbs m left (a 0) (a 1) ha0 ha1
    have hah := read128_of_limbs m (left + 16) (a 2) (a 3) ha2 (by simpa [Nat.add_assoc] using ha3)
    have hbl := read128_of_limbs m right (b 0) (b 1) hb0 hb1
    have hbh := read128_of_limbs m (right + 16) (b 2) (b 3) hb2 (by simpa [Nat.add_assoc] using hb3)
    have hzero : BitVec.ofNat 128 0 = pack128 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := by decide
    cil_execute hal, hah, hbl, hbh, hzero, evalMemory, unsafeAsRef,
      offsetValue, unsafe_add16_one, write128, read128_write_local,
      zip128, lane128_0, lane128_1, pack128_and, pack128_or, adv_incoming,
      pack128_complement, carryMask with (first | cil_store_call)
    all_goals rename_i branch
    all_goals first
      | have hbranch : propagationARM a b = BitVec.ofNat 128 0 := by
          simpa (config := { implicitDefEqProofs := false }) only [propagationARM, propagationLo, propagationHi, correctedLo,
            correctedHi, carryMask, hzero, zip128, lane128_0, lane128_1,
            pack128_and, adv_incoming] using branch
        simp only [armStores, ite_eq_left hbranch]
        intro address
        simp (config := { implicitDefEqProofs := false }) only [correctedLo, correctedHi, carryMask]
      | have hbranch : propagationARM a b ≠ BitVec.ofNat 128 0 := by
          simpa (config := { implicitDefEqProofs := false }) only [propagationARM, propagationLo, propagationHi, correctedLo,
            correctedHi, carryMask, hzero, zip128, lane128_0, lane128_1,
            pack128_and, adv_incoming] using branch
        simp only [armStores, ite_eq_right hbranch]
        intro address
        simp (config := { implicitDefEqProofs := false }) only [repairedHi, extraHi,
          propagationARM, propagationLo, propagationHi, correctedLo, correctedHi,
          carryMask, hzero, pack128_complement, zip128, lane128_0, lane128_1,
          pack128_and, pack128_or, adv_incoming, BitVec.or_zero,
          show ~~~(BitVec.ofNat 64 0) = BitVec.ofNat 64 (2^64-1) from rfl]

theorem execute_arm128_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : Extracted.profile.advSimd = true) :
    ∃ final flag, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.addVector128Index)
      Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 0)] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨final, flag, hr, hm⟩ := execute_arm128 m left right out frame fuel a b ha hb hp
  exact ⟨final, flag, hr, by simpa only [arm_stores_words] using hm⟩

theorem execute_arm128_words_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : Extracted.profile.advSimd = true)
    (hf : executionBound Extracted.program Extracted.addVector128Index ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 0)] frame [] m =
        some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨final, flag, he, hm⟩ := execute_arm128_words m left right out frame 0 a b ha hb hp
  refine ⟨final, flag, ?_, hm⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf he

}

end UInt256Proof.SIMD
