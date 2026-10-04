import CIL.SIMD.Intrinsics
import CIL.SIMD.VectorLemmas
import UInt256.Methods.Compare.MaskLemmas
import UInt256.Methods.Equality.Lemmas

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Compare

def flagNumber (flag : Bool) : Nat := if flag then 1 else 0

theorem intrinsic_extract256 (bits : BitVec 256) (index : W32) :
    evalIntrinsic (.vector (.extract64 256)) [.v256 bits, .i32 index] =
      if index.toNat < 4 then some (.i64 (Vector.lane64 bits index.toNat)) else none := rfl

theorem intrinsic_reinterpret256 (bits : BitVec 256) :
    evalIntrinsic (.vector (.reinterpret 256)) [.v256 bits] = some (.v256 bits) := rfl

theorem intrinsic_native_eq (left right : BitVec 256) :
    evalIntrinsic (.avx2 .eq64) [.v256 left,.v256 right] =
      some (.v256 (Vector.zip256 (fun x y => Vector.mask64 (x == y)) left right)) := rfl

theorem intrinsic_native_gt (left right : BitVec 256) :
    evalIntrinsic (.avx512 .gtu64) [.v256 left,.v256 right] =
      some (.v256 (Vector.zip256 (fun x y => Vector.mask64 (y.ult x)) left right)) := rfl

theorem intrinsic_native_lt (left right : BitVec 256) :
    evalIntrinsic (.avx512 .ltu64) [.v256 left,.v256 right] =
      some (.v256 (Vector.zip256 (fun x y => Vector.mask64 (x.ult y)) left right)) := rfl

theorem intrinsic_avx_blend (left right : BitVec 256) :
    evalIntrinsic (.avx .blend32) [.v256 left,.v256 right,.i32 (BitVec.ofNat 32 170)] =
      some (.v256 (Vector.blend32 left right (BitVec.ofNat 8 170))) := rfl

theorem intrinsic_avx2_blend (left right : BitVec 256) :
    evalIntrinsic (.avx2 .blend32) [.v256 left,.v256 right,.i32 (BitVec.ofNat 32 170)] =
      some (.v256 (Vector.blend32 left right (BitVec.ofNat 8 170))) := rfl

theorem intrinsic_native_mask (bits : BitVec 256) :
    evalIntrinsic (.avx .moveMask32) [.v256 bits] = some (.i32 (Vector.moveMask32 bits)) := rfl

theorem orderingDigit_flags (left right : W64) :
    orderingDigit left right = flagNumber (left == right) + 2 * flagNumber (right.ult left) := by
  by_cases equal : left = right
  · subst right
    simp [orderingDigit,flagNumber,BitVec.ult]
  · by_cases greater : right.toNat < left.toNat
    all_goals simp [orderingDigit,flagNumber,BitVec.ult,equal,greater]

theorem moveMask_blend_masks (e0 e1 e2 e3 c0 c1 c2 c3 : Bool) :
    Vector.moveMask32 (Vector.blend32
      (Vector.pack256 (Vector.mask64 e0) (Vector.mask64 e1) (Vector.mask64 e2) (Vector.mask64 e3))
      (Vector.pack256 (Vector.mask64 c0) (Vector.mask64 c1) (Vector.mask64 c2) (Vector.mask64 c3))
      (BitVec.ofNat 8 170)) = BitVec.ofNat 32
        (flagNumber e0 + 2 * flagNumber c0 + 4 * flagNumber e1 + 8 * flagNumber c1 +
          16 * flagNumber e2 + 32 * flagNumber c2 + 64 * flagNumber e3 + 128 * flagNumber c3) := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;>
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem nativeOrderingMask (left right : Limbs) :
    Vector.moveMask32 (Vector.blend32
      (Vector.zip256 (fun x y => Vector.mask64 (x == y)) (value left) (value right))
      (Vector.zip256 (fun x y => Vector.mask64 (y.ult x)) (value left) (value right))
      (BitVec.ofNat 8 170)) = BitVec.ofNat 32 (orderingMask left right) := by
  simp only [Equality.value_pack,Vector.zip256,Vector.lane256_0,Vector.lane256_1,
    Vector.lane256_2,Vector.lane256_3,moveMask_blend_masks]
  congr 1
  simp only [orderingMask,orderingDigit_flags]
  omega

theorem nativeOrderingReverseMask (left right : Limbs) :
    Vector.moveMask32 (Vector.blend32
      (Vector.zip256 (fun x y => Vector.mask64 (x == y)) (value left) (value right))
      (Vector.zip256 (fun x y => Vector.mask64 (x.ult y)) (value left) (value right))
      (BitVec.ofNat 8 170)) = BitVec.ofNat 32 (orderingMask right left) := by
  simp only [Equality.value_pack,Vector.zip256,Vector.lane256_0,Vector.lane256_1,
    Vector.lane256_2,Vector.lane256_3,moveMask_blend_masks]
  congr 1
  have e0 : (left 0 == right 0) = (right 0 == left 0) := BEq.comm
  have e1 : (left 1 == right 1) = (right 1 == left 1) := BEq.comm
  have e2 : (left 2 == right 2) = (right 2 == left 2) := BEq.comm
  have e3 : (left 3 == right 3) = (right 3 == left 3) := BEq.comm
  simp only [orderingMask,orderingDigit_flags,e0,e1,e2,e3]
  omega

theorem moveMask_four (a b c d : Bool) :
    Vector.moveMask64 (Vector.pack256 (Vector.mask64 a) (Vector.mask64 b)
      (Vector.mask64 c) (Vector.mask64 d)) =
      BitVec.ofNat 32 (flagNumber a + 2 * flagNumber b + 4 * flagNumber c + 8 * flagNumber d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem portableEqualityMask (left right : Limbs) :
    Vector.moveMask64 (Vector.zip256 (fun x y => Vector.mask64 (x == y))
      (value left) (value right)) = BitVec.ofNat 32 (equalityMask left right) := by
  simp only [Equality.value_pack,Vector.zip256,Vector.lane256_0,Vector.lane256_1,
    Vector.lane256_2,Vector.lane256_3,moveMask_four]
  simp [equalityMask,flagNumber]

theorem portableLessMask (left right : Limbs) :
    Vector.moveMask64 (Vector.zip256 (fun x y => Vector.mask64 (x.ult y))
      (value left) (value right)) = BitVec.ofNat 32 (lessMask left right) := by
  simp only [Equality.value_pack,Vector.zip256,Vector.lane256_0,Vector.lane256_1,
    Vector.lane256_2,Vector.lane256_3,moveMask_four]
  simp [lessMask,flagNumber,BitVec.ult]

theorem intrinsic_portable_eq (left right : BitVec 256) :
    evalIntrinsic (.vector (.eq64 256)) [.v256 left,.v256 right] =
      some (.v256 (Vector.zip256 (fun x y => Vector.mask64 (x == y)) left right)) := rfl

theorem intrinsic_portable_lt (left right : BitVec 256) :
    evalIntrinsic (.vector (.ltu64 256)) [.v256 left,.v256 right] =
      some (.v256 (Vector.zip256 (fun x y => Vector.mask64 (x.ult y)) left right)) := rfl

theorem intrinsic_portable_mask (bits : BitVec 256) :
    evalIntrinsic (.vector (.extractMSB64 256)) [.v256 bits] =
      some (.i32 (Vector.moveMask64 bits)) := rfl

end UInt256Proof.Compare

