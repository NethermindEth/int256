import UInt256.Methods.Equality.Lemmas

open CIL UInt256Model
namespace UInt256Proof.Bitwise

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

end UInt256Proof.Bitwise
