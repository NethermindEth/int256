import UInt256.Methods.Multiply.VectorProducts
import UInt256.Methods.Multiply.SingleWord
import UInt256.Methods.Multiply.ReturnContract
open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply
theorem packed_single_product (a b : W64) :
    CIL.Vector.pack256 (lowProduct a b) (highProduct a b)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) = value (singleWord a) * value (singleWord b) := by
  rw [← four_value_pack]
  simpa only [ite_self] using single_product_value a b

@[irreducible] def returnOutput (a b : Limbs) : CIL.Vector.V256 := value a * value b

theorem word64_cast {width : Nat} (word : BitVec width) :
    BitVec.ofNat 64 (word.toNat % 18446744073709551616) = word.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    show (2 : Nat)^64 = 18446744073709551616 from rfl, Nat.mod_mod]

end UInt256Proof.Multiply
