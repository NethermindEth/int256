import UInt256.Methods.Equality.Contract
import UInt256.VectorRepresentation
import UInt256.Methods.Equality.Lemmas
import CIL.SIMD.VectorLemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Equality

theorem maskPack_zero (e0 e1 e2 e3 : Bool) :
    Vector.pack256 (Vector.mask64 e0) (Vector.mask64 e1) (Vector.mask64 e2) (Vector.mask64 e3) = 0 ↔
      e0 = false ∧ e1 = false ∧ e2 = false ∧ e3 = false := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> decide

theorem equalityMask_zero (a b : Limbs) :
    Vector.zip256 (fun x y => Vector.mask64 (x == y)) (value a) (value b) = 0 ↔
      a 0 ≠ b 0 ∧ a 1 ≠ b 1 ∧ a 2 ≠ b 2 ∧ a 3 ≠ b 3 := by
  simp only [value_pack,Vector.zip256,Vector.lane256_0,Vector.lane256_1,
    Vector.lane256_2,Vector.lane256_3,maskPack_zero,beq_eq_false_iff_ne]

theorem intrinsic_mask_eq256 (a b : BitVec 256) :
    evalIntrinsic (.vector (.eq64 256)) [.v256 a,.v256 b] =
      some (.v256 (Vector.zip256 (fun x y => Vector.mask64 (x == y)) a b)) := rfl

theorem intrinsic_scalar32 (word : W32) :
    evalIntrinsic (.vector (.createScalar32 256)) [.i32 word] =
      some (.v256 (word.zeroExtend 256)) := rfl

theorem intrinsic_scalar64 (word : W64) :
    evalIntrinsic (.vector (.createScalar64 256)) [.i64 word] =
      some (.v256 (word.zeroExtend 256)) := rfl

theorem zeroExtend32_toNat256 (word : W32) : (word.zeroExtend 256).toNat = word.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth]
  exact BitVec.toNat_setWidth_of_le (by decide)

theorem zeroExtend64_toNat256 (word : W64) : (word.zeroExtend 256).toNat = word.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth]
  exact BitVec.toNat_setWidth_of_le (by decide)

theorem intrinsic_zero256 : evalIntrinsic (.vector (.zero 256)) [] = some (.v256 0) := rfl

theorem intrinsic_equal256 (a b : BitVec 256) :
    evalIntrinsic (.vector (.equalsAll 256)) [.v256 a, .v256 b] =
      some (.i32 (UInt256Model.Equality.booleanWord (decide (a = b)))) := rfl

theorem intrinsic_equal128 (a b : BitVec 128) :
    evalIntrinsic (.vector (.equalsAll 128)) [.v128 a, .v128 b] =
      some (.i32 (UInt256Model.Equality.booleanWord (decide (a = b)))) := rfl

theorem intrinsic_xor128 (a b : BitVec 128) :
    evalIntrinsic (.vector (.bxor 128)) [.v128 a, .v128 b] = some (.v128 (a ^^^ b)) := rfl

theorem intrinsic_or128 (a b : BitVec 128) :
    evalIntrinsic (.vector (.bor 128)) [.v128 a, .v128 b] = some (.v128 (a ||| b)) := rfl

theorem intrinsic_zero128 : evalIntrinsic (.vector (.zero 128)) [] = some (.v128 0) := rfl

theorem initial_append_halves (initial : Bytes) (base : Nat) :
    halfValue initial (base + 16) ++ halfValue initial base = byteValue initial base := by
  rw [← initial_halves]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (halfValue initial base).isLt, Nat.shiftLeft_eq]
  have bound := (halfValue initial (base + 16) ++ halfValue initial base).isLt
  rw [BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (halfValue initial base).isLt, Nat.shiftLeft_eq] at bound
  omega

theorem halves_eq_iff (initial : Bytes) (left right : Nat) :
    (halfValue initial left = halfValue initial right ∧
      halfValue initial (left + 16) = halfValue initial (right + 16)) ↔
      byteValue initial left = byteValue initial right := by
  constructor
  · rintro ⟨lo, hi⟩
    rw [← initial_append_halves initial left, ← initial_append_halves initial right, lo, hi]
  · intro equal
    have joined : halfValue initial (left + 16) ++ halfValue initial left =
        halfValue initial (right + 16) ++ halfValue initial right := by
      rw [initial_append_halves, initial_append_halves]
      exact equal
    exact ⟨by simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun bits : BitVec 256 => bits.extractLsb' 0 128) joined,
      by simpa only [BitVec.extractLsb'_append_eq_left] using
        congrArg (fun bits : BitVec 256 => bits.extractLsb' 128 128) joined⟩

theorem halves_snapshot_eq_iff (initial : Bytes) (left : Nat) (right : BitVec 256) :
    (halfValue initial left = right.extractLsb' 0 128 ∧
      halfValue initial (left + 16) = right.extractLsb' 128 128) ↔
      byteValue initial left = right := by
  constructor
  · rintro ⟨lo,hi⟩
    rw [←initial_append_halves initial left,lo,hi,BitVec.extractLsb'_append_extractLsb']
  · intro equal
    have joined : halfValue initial (left + 16) ++ halfValue initial left = right := by
      rw [initial_append_halves]
      exact equal
    exact ⟨by simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun bits : BitVec 256 => bits.extractLsb' 0 128) joined,
      by simpa only [BitVec.extractLsb'_append_eq_left] using
        congrArg (fun bits : BitVec 256 => bits.extractLsb' 128 128) joined⟩

end UInt256Proof.Equality
