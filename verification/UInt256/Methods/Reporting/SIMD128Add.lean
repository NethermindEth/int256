import UInt256.Methods.Reporting.SIMD128AddArithmetic
import UInt256.Methods.Reporting.SSE128Add

open CIL CIL.Vector UInt256Model UInt256Proof UInt256Proof.SIMD
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.addVector128Index {



/-- Execute the complete wrapping ARM vector helper, including its early stores and both repair hops. -/
theorem execute_reporting_arm128 (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (_hp : Extracted.profile.advSimd = true) :
    ∃ final, run Extracted.program
      (fuel + executionBound Extracted.program Extracted.addVector128Index)
      Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 1)] frame [] m =
        some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
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
    · have hbranch : propagationLo a b ||| propagationHi a b = BitVec.ofNat 128 0 := by
        simpa only [propagationLo, propagationHi, correctedLo, correctedHi, carryMask,
          hzero, zip128, lane128_0, lane128_1, pack128_and, pack128_or,
          BitVec.and_zero, BitVec.zero_or] using branch
      have flag := unpropagated_high_flag a b hbranch
      have mask := carry_mask_negative (a 3) (b 3)
      simp only [carryMask] at mask
      refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
      · rw [flag, mask]
        simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff, ite_not]
      · intro address
        simp (config := { implicitDefEqProofs := false }) only [write, reduceCtorEq, ↓reduceIte]
        simpa (config := { implicitDefEqProofs := false }) only [correctedLo, correctedHi, carryMask] using
          congrFun (corrected_stores_words m out a b hbranch) (.byte address)
    · have flag := repaired_high_flag a b
      simp only [repairedCarryHi, propagationHi, propagationLo, correctedLo, correctedHi,
        extraHi, propagationARM, carryMask, hzero, pack128_complement, zip128,
        lane128_0, lane128_1, pack128_and, pack128_or, adv_incoming,
        BitVec.or_zero, BitVec.or_assoc,
        show ~~~(BitVec.ofNat 64 0) = BitVec.ofNat 64 18446744073709551615 from rfl] at flag
      refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
      · rw [flag]
        simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff, ite_not]
      · intro address
        simp (config := { implicitDefEqProofs := false }) only [write, reduceCtorEq, ↓reduceIte]
        have stores : writeBytes (writeBytes (writeBytes m out (correctedLo a b).toNat 16)
            (out + 16) (correctedHi a b).toNat 16) (out + 16) (repairedHi a b).toNat 16 =
            store4 m out (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) := by
          rw [writeBytes_overwrite_same, corrected_lo_words, repaired_hi_words, arm_repair_words,
            write128_two_limbs, write128_two_limbs]
          simp only [store4, Nat.add_assoc]
        simpa (config := { implicitDefEqProofs := false }) only [repairedHi, extraHi,
          propagationARM, propagationLo, propagationHi, correctedLo, correctedHi,
          carryMask, hzero, pack128_complement, zip128, lane128_0, lane128_1,
          pack128_and, pack128_or, adv_incoming, BitVec.or_zero,
          show ~~~(BitVec.ofNat 64 0) = BitVec.ofNat 64 (2^64-1) from rfl] using
          congrFun stores (.byte address)

theorem execute_reporting_arm128_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hp : Extracted.profile.advSimd = true)
    (hf : executionBound Extracted.program Extracted.addVector128Index ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 1)] frame [] m =
        some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨final, hr, hm⟩ := execute_reporting_arm128 m left right out frame 0 a b ha hb hp
  simp only [Nat.zero_add] at hr
  exact ⟨final, run_of_le _ _ _ _ _ _ _ _ _ _ hf hr, hm⟩
theorem execute_reporting128_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hf : executionBound Extracted.program Extracted.addVector128Index ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.addVector128Index 0
      [.object left, .object right, .object out, .i32 (BitVec.ofNat 32 1)] frame [] m =
        some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  cases hp : Extracted.profile.advSimd with
  | true => exact execute_reporting_arm128_at m left right out frame fuel a b ha hb hp hf
  | false => exact execute_reporting_sse128_at m left right out frame fuel a b ha hb hp hf
}
end UInt256Proof.Reporting
