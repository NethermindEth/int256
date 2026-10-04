import UInt256.Methods.Equality.Lemmas

open CIL UInt256Model
namespace UInt256Proof.Bitwise

theorem word_not_number (x : W64) : 18446744073709551615 - x.toNat = (~~~x).toNat := by
  rw [BitVec.toNat_not]

theorem word_not_xor_number (x : W64) : x.toNat ^^^ 18446744073709551615 = (~~~x).toNat := by
  have allOnes : (~~~(0 : W64)).toNat = 18446744073709551615 := rfl
  rw [←allOnes,←BitVec.toNat_xor]
  rw [show ~~~(0 : W64) = BitVec.allOnes 64 from rfl,BitVec.xor_allOnes]

theorem full_not_number (x : BitVec 256) :
    115792089237316195423570985008687907853269984665640564039457584007913129639935 - x.toNat =
      (~~~x).toNat := by
  rw [BitVec.toNat_not]

theorem value_and (a b : Limbs) :
    value (fun i => a i &&& b i) = value a &&& value b := by
  simp only [Equality.value_pack, CIL.Vector.pack256]
  rw [BitVec.and_append, BitVec.and_append, BitVec.and_append]

theorem value_or (a b : Limbs) :
    value (fun i => a i ||| b i) = value a ||| value b := by
  simp only [Equality.value_pack, CIL.Vector.pack256]
  rw [BitVec.or_append, BitVec.or_append, BitVec.or_append]

theorem value_xor (a b : Limbs) :
    value (fun i => a i ^^^ b i) = value a ^^^ value b := by
  simp only [Equality.value_pack, CIL.Vector.pack256]
  rw [BitVec.xor_append, BitVec.xor_append, BitVec.xor_append]

theorem value_not (a : Limbs) :
    value (fun i => ~~~a i) = ~~~value a := by
  simp only [Equality.value_pack, CIL.Vector.pack256]
  rw [BitVec.not_append, BitVec.not_append, BitVec.not_append]

/-- Alternative correct word XOR, independent of its helper decomposition. -/
@[simp] theorem xor_alternative (x y : BitVec width) :
    (x ||| y) &&& ~~~(x &&& y) = x ^^^ y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_xor]
  cases x[i] <;> cases y[i] <;> rfl

theorem intrinsic_and256 (a b : BitVec 256) :
    CIL.evalIntrinsic (.vector (.band 256)) [.v256 a,.v256 b] = some (.v256 (a &&& b)) := rfl

theorem intrinsic_or256 (a b : BitVec 256) :
    CIL.evalIntrinsic (.vector (.bor 256)) [.v256 a,.v256 b] = some (.v256 (a ||| b)) := rfl

theorem intrinsic_xor256 (a b : BitVec 256) :
    CIL.evalIntrinsic (.vector (.bxor 256)) [.v256 a,.v256 b] = some (.v256 (a ^^^ b)) := rfl

theorem intrinsic_not256 (a : BitVec 256) :
    CIL.evalIntrinsic (.vector (.bnot 256)) [.v256 a] = some (.v256 (~~~a)) := rfl

@[simp] theorem and_alternative (x y : BitVec width) : ~~~(~~~x ||| ~~~y) = x &&& y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_not,BitVec.getElem_or,BitVec.getElem_and]
  cases x[i] <;> cases y[i] <;> rfl

@[simp] theorem or_alternative (x y : BitVec width) : ~~~(~~~x &&& ~~~y) = x ||| y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_not,BitVec.getElem_or,BitVec.getElem_and]
  cases x[i] <;> cases y[i] <;> rfl

end UInt256Proof.Bitwise
