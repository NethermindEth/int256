import UInt256.Methods.Add.SIMD128Automation

open CIL CIL.Vector UInt256Model UInt256Proof

namespace UInt256Proof.SIMD

theorem propagation_arm_bits (a b : Limbs) : propagationARM a b =
    pack128 (-(propagationBit (a 1) (b 1) (carryBit (a 0) (b 0))))
      (-(propagationBit (a 2) (b 2) (carryBit (a 1) (b 1)))) := by
  have hzero : BitVec.ofNat 128 0 = pack128 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := by decide
  simp only [propagationARM, propagationLo, propagationHi, correctedLo, correctedHi,
    hzero, zip128, lane128_0, lane128_1, pack128_and, adv_incoming]
  rw [propagation_mask, propagation_mask]

theorem extra_hi_bits (a b : Limbs) : extraHi a b =
    pack128 (-(propagationBit (a 1) (b 1) (carryBit (a 0) (b 0))))
      (-(propagationBit (a 2) (b 2) (carryBit (a 1) (b 1)) |||
        fullPropagationBit (a 2 + b 2 + carryBit (a 1) (b 1))
          (propagationBit (a 1) (b 1) (carryBit (a 0) (b 0))))) := by
  have hzero : BitVec.ofNat 128 0 = pack128 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := by decide
  have hones : ~~~(BitVec.ofNat 64 0) = BitVec.allOnes 64 := by decide
  simp only [extraHi, propagation_arm_bits, correctedHi, hzero, pack128_complement,
    hones, zip128, lane128_0, lane128_1, pack128_and, adv_incoming, pack128_or]
  rw [carry_mask_sum, full_mask _ _ (propagationBit_bound _ _ _),
    negative_bits_or _ _ (propagationBit_bound _ _ _) (fullPropagationBit_bound _ _)]
  congr 1
  exact BitVec.or_zero

theorem repaired_hi_words (a b : Limbs) :
    repairedHi a b = pack128 (armRepairWords a b 2) (armRepairWords a b 3) := by
  simp only [repairedHi, correctedHi, extra_hi_bits, zip128, lane128_0, lane128_1]
  rw [carry_mask_sum, carry_mask_sum, BitVec.sub_eq_add_neg,
    BitVec.sub_eq_add_neg, BitVec.neg_neg, BitVec.neg_neg]
  rfl

theorem corrected_lo_words (a b : Limbs) :
    correctedLo a b = pack128 (armRepairWords a b 0) (armRepairWords a b 1) := by
  unfold correctedLo
  rw [carry_mask_sum]
  rfl

theorem arm_repair_words (a b : Limbs) : armRepairWords a b = sumWords a b := by
  apply representation_injective
  rw [arm_repair_sum, sumWords_sum]

theorem repaired_of_no_propagation (a b : Limbs)
    (h : propagationARM a b = BitVec.ofNat 128 0) : repairedHi a b = correctedHi a b := by
  simp only [repairedHi, extraHi, h, BitVec.and_zero]
  have hz : advExtract64 (BitVec.ofNat 128 0) (BitVec.ofNat 128 0) 1 =
      BitVec.ofNat 128 0 := by decide
  rw [hz, BitVec.or_zero]
  have hzero : BitVec.ofNat 128 0 = pack128 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := by decide
  simp only [zip128, hzero, lane128_0, lane128_1, BitVec.sub_zero]
  exact pack128_lanes _

theorem arm_stores_words (m : Memory) (out : Nat) (a b : Limbs) :
    armStores m out a b = store4 m out (sumWords a b 0) (sumWords a b 1)
      (sumWords a b 2) (sumWords a b 3) := by
  have hs : armStores m out a b =
      writeBytes (writeBytes m out (correctedLo a b).toNat 16)
        (out + 16) (repairedHi a b).toNat 16 := by
    by_cases h : propagationARM a b = BitVec.ofNat 128 0
    · simp only [armStores, ite_eq_left h, repaired_of_no_propagation a b h]
    · simp only [armStores, ite_eq_right h]
      exact writeBytes_overwrite_same _ _ _ _ _
  rw [hs, corrected_lo_words, repaired_hi_words, arm_repair_words,
    write128_two_limbs, write128_two_limbs]
  simp only [store4, Nat.add_assoc]

theorem corrected_stores_words (m : Memory) (out : Nat) (a b : Limbs)
    (h : propagationLo a b ||| propagationHi a b = BitVec.ofNat 128 0) :
    writeBytes (writeBytes m out (correctedLo a b).toNat 16)
      (out + 16) (correctedHi a b).toNat 16 =
    store4 m out (sumWords a b 0) (sumWords a b 1)
      (sumWords a b 2) (sumWords a b 3) := by
  obtain ⟨hl, hh⟩ := BitVec.or_eq_zero_iff.mp h
  have hp : propagationARM a b = BitVec.ofNat 128 0 := by
    simp only [propagationARM, hl, hh]
    decide
  have hm := arm_stores_words m out a b
  simpa only [armStores, ite_eq_left hp] using hm

end UInt256Proof.SIMD
