import UInt256.Methods.Add.CarryMemory
import UInt256.Arithmetic.Carry

namespace UInt256Proof.Safety

theorem carryWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    carryWord a b c = UInt256Proof.carry a b c := by
  simp only [carryWord, UInt256Proof.extend_choice]
  have h := UInt256Proof.carry_expression a b c incoming
  change ((if a + b < a then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) +
    (if a + b + c < a + b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) = _ at h
  exact h

theorem carryWord_arithmetic (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    (a + b + c).toNat + 2^64 * (carryWord a b c).toNat = a.toNat + b.toNat + c.toNat ∧
      (carryWord a b c).toNat ≤ 1 := by
  rw [carryWord_correct a b c incoming]
  exact ⟨UInt256Proof.carry_word_nat a b c incoming, UInt256Proof.carry_bound a b c incoming⟩

#print axioms carryWord_correct
#print axioms carryWord_arithmetic

end UInt256Proof.Safety
