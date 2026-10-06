import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Model.Safety

theorem unsigned_scalar_flag (left : BitVec 256) (number : Nat) (bound : number < 2^256) :
    (if left = BitVec.ofNat 256 number then (1 : BitVec 32) else 0) =
      (if (left.toNat : Int) = number then 1 else 0) := by
  have equal : (left = BitVec.ofNat 256 number) ↔ left.toNat = number := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  simp only [equal, Int.ofNat_inj]

theorem signed_scalar_flag {width : Nat} (left : BitVec 256) (right : BitVec width)
    (bound : right.toNat < 2^256) :
    (if right.toInt < 0 then (0 : BitVec 32) else
      if left = BitVec.ofNat 256 right.toNat then 1 else 0) =
      (if (left.toNat : Int) = right.toInt then 1 else 0) := by
  by_cases negative : right.toInt < 0
  · have unequal : (left.toNat : Int) ≠ right.toInt := by omega
    simp only [negative, unequal, ite_true, ite_false]
  · have same : right.toInt = (right.toNat : Int) := by
      have formula := BitVec.toInt_eq_toNat_cond right
      have bounded := right.isLt
      split at formula <;> omega
    simp only [same]
    exact unsigned_scalar_flag left right.toNat bound

theorem scalar_embedding {width : Nat} (right : BitVec width) :
    right.zeroExtend 256 = BitVec.ofNat 256 right.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

#print axioms unsigned_scalar_flag
#print axioms signed_scalar_flag
#print axioms scalar_embedding

end UInt256Model.Safety
