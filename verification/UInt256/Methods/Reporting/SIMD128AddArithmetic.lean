import UInt256.Methods.Add.SIMD128Arithmetic
import UInt256.Methods.Reporting.ARMArithmetic

open CIL CIL.Vector UInt256Model UInt256Proof.SIMD
namespace UInt256Proof.Reporting

def repairedCarryHi (a b : Limbs) : V128 :=
  pack128 (carryMask (a 2) (b 2)) (carryMask (a 3) (b 3)) ||| propagationHi a b |||
    (zip128 (fun x y => mask64 (x == y)) (correctedHi a b) (~~~(BitVec.ofNat 128 0)) &&& extraHi a b)

theorem repaired_high_flag (a b : Limbs) : lane64 (repairedCarryHi a b) 1 = -finalCarry a b := by
  have hones : ~~~(BitVec.ofNat 128 0) =
      pack128 (BitVec.allOnes 64) (BitVec.allOnes 64) := by decide
  have hz : lane64 (BitVec.ofNat 128 0) 1 = BitVec.ofNat 64 0 := by decide
  have hp : (armIncomingRepair a b).toNat ≤ 1 :=
    bit_or_bound _ _ (propagationBit_bound _ _ _) (fullPropagationBit_bound _ _)
  simp only [repairedCarryHi, propagationHi, correctedHi, extra_hi_bits, hones,
    zip128, lane128_0, lane128_1, pack128_and, pack128_or, hz]
  rw [propagation_mask, carry_mask_negative, carry_mask_sum]
  change (-carryBit (a 3) (b 3)) ||| (-propagationBit (a 3) (b 3) (carryBit (a 2) (b 2))) |||
    (mask64 ((a 3 + b 3 + carryBit (a 2) (b 2)) == BitVec.allOnes 64) &&&
      (-armIncomingRepair a b)) = _
  rw [full_mask _ _ hp, negative_bits_or _ _ (carryBit_bound _ _) (propagationBit_bound _ _ _),
    negative_bits_or _ _ (bit_or_bound _ _ (carryBit_bound _ _) (propagationBit_bound _ _ _))
      (fullPropagationBit_bound _ _)]
  change -armOutgoingFlag a b = _
  rw [arm_outgoing_flag]

theorem unpropagated_high_flag (a b : Limbs)
    (hp : propagationLo a b ||| propagationHi a b = BitVec.ofNat 128 0) :
    finalCarry a b = carryBit (a 3) (b 3) := by
  obtain ⟨hl, hh⟩ := BitVec.or_eq_zero_iff.mp hp
  have hzero : BitVec.ofNat 128 0 = pack128 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := by decide
  have h1 := congrArg (fun v => lane64 v 1) hl
  have h2 := congrArg (fun v => lane64 v 0) hh
  have h3 := congrArg (fun v => lane64 v 1) hh
  simp only [propagationLo, propagationHi, correctedLo, correctedHi, hzero, zip128,
    pack128_and, lane128_0, lane128_1] at h1 h2 h3
  have c1 := carry_base (a 0) (b 0)
  have c2 := carry_no_propagation (a 1) (b 1) _ (carryBit_bound _ _)
    (masked_carry_no_propagation _ _ _ _ h1)
  have c3 := carry_no_propagation (a 2) (b 2) _ (carryBit_bound _ _)
    (masked_carry_no_propagation _ _ _ _ h2)
  have c4 := carry_no_propagation (a 3) (b 3) _ (carryBit_bound _ _)
    (masked_carry_no_propagation _ _ _ _ h3)
  unfold finalCarry
  rw [c1, c2, c3, c4]

#print axioms repaired_high_flag
#print axioms unpropagated_high_flag
end UInt256Proof.Reporting
