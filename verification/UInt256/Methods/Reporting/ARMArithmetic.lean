import UInt256.Arithmetic.SIMDCarry
import UInt256.Methods.Reporting.VectorArithmetic

open CIL CIL.Vector UInt256Model UInt256Proof.SIMD

namespace UInt256Proof.Reporting

theorem bit_or_bound (p q : W64) (hp : p.toNat ≤ 1) (hq : q.toNat ≤ 1) :
    (p ||| q).toNat ≤ 1 := by
  rcases bit_zero_or_one p hp with h | h <;> rcases bit_zero_or_one q hq with k | k
  all_goals subst p; subst q; decide

theorem bit_add_or (p q : W64) (hp : p.toNat ≤ 1) (hq : q.toNat ≤ 1)
    (hs : (p + q).toNat ≤ 1) : p + q = p ||| q := by
  rcases bit_zero_or_one p hp with h | h <;> rcases bit_zero_or_one q hq with k | k
  all_goals subst p; subst q
  all_goals first | decide | simp at hs

theorem bit_disjoint (p q : W64) (hq : q.toNat ≤ 1) (hs : (p + q).toNat ≤ 1) :
    p = 1 → q = 0 := by
  intro h; subst p
  rcases bit_zero_or_one q hq with h | h
  · exact h
  · subst q
    simp at hs

def armIncomingRepair (a b : Limbs) : W64 :=
  propagationBit (a 2) (b 2) (carryBit (a 1) (b 1)) |||
    fullPropagationBit (a 2 + b 2 + carryBit (a 1) (b 1))
      (propagationBit (a 1) (b 1) (carryBit (a 0) (b 0)))

def armOutgoingFlag (a b : Limbs) : W64 :=
  carryBit (a 3) (b 3) ||| propagationBit (a 3) (b 3) (carryBit (a 2) (b 2)) |||
    fullPropagationBit (a 3 + b 3 + carryBit (a 2) (b 2)) (armIncomingRepair a b)

theorem arm_outgoing_flag (a b : Limbs) : armOutgoingFlag a b = finalCarry a b := by
  let g0 := carryBit (a 0) (b 0)
  let g1 := carryBit (a 1) (b 1)
  let g2 := carryBit (a 2) (b 2)
  let p1 := propagationBit (a 1) (b 1) g0
  have c1 : carry (a 0) (b 0) 0 = g0 := carry_base _ _
  have c2 : carry (a 1) (b 1) g0 = g1 + p1 :=
    carry_after_incoming _ _ _ (carryBit_bound _ _)
  have hc2 : (g1 + p1).toNat ≤ 1 := by
    rw [← c2]; exact carry_bound _ _ _ (carryBit_bound _ _)
  have hops2 := propagation_two_hops (a 2) (b 2) g1 p1
    (carryBit_bound _ _) (propagationBit_bound _ _ _)
    (generated_propagation_disjoint _ _ _ (carryBit_bound _ _))
  have c3 := carry_after_incoming (a 2) (b 2) (g1 + p1) hc2
  rw [hops2] at c3
  change carry (a 2) (b 2) (g1 + p1) = g2 + armIncomingRepair a b at c3
  have hc3 : (g2 + armIncomingRepair a b).toNat ≤ 1 := by
    rw [← c3]; exact carry_bound _ _ _ hc2
  have hp : (armIncomingRepair a b).toNat ≤ 1 :=
    bit_or_bound _ _ (propagationBit_bound _ _ _) (fullPropagationBit_bound _ _)
  have hops3 := propagation_two_hops (a 3) (b 3) g2 (armIncomingRepair a b)
    (carryBit_bound _ _) hp (bit_disjoint _ _ hp hc3)
  have c4 := carry_after_incoming (a 3) (b 3) (g2 + armIncomingRepair a b) hc3
  rw [hops3] at c4
  have hp3 := bit_or_bound _ _ (propagationBit_bound (a 3) (b 3) g2)
    (fullPropagationBit_bound (a 3 + b 3 + g2) (armIncomingRepair a b))
  have hc4 := carry_bound (a 3) (b 3) (g2 + armIncomingRepair a b) hc3
  rw [c4] at hc4
  rw [bit_add_or _ _ (carryBit_bound _ _) hp3 hc4] at c4
  unfold finalCarry
  rw [c1, c2, c3, c4]
  exact BitVec.or_assoc _ _ _

#print axioms arm_outgoing_flag
end UInt256Proof.Reporting
