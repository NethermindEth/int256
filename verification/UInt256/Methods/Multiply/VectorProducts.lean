import UInt256.Methods.Multiply.NarrowProduct
import UInt256.VectorRepresentation
import CIL.SIMD.VectorLemmas
open CIL CIL.Vector
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem pack_limbs_value (a : UInt256Model.Limbs) :
    pack256 (a 0) (a 1) (a 2) (a 3) = UInt256Model.value a := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt256Proof.pack256_number, UInt256Proof.value_toNat]
  omega

theorem four_value_pack (a b c d : W64) :
    UInt256Model.value (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) =
      pack256 a b c d := by
  exact (pack_limbs_value _).symm

@[simp] theorem digitLow_shift32 (a : W64) : digitLow (a >>> 32) = digitHigh a := by rfl

theorem even_lane (x : V256) (i : Nat) : lane32 x (2*i) = (lane64 x i).setWidth 32 := by
  ext j hj
  simp (config := { implicitDefEqProofs := false }) only [lane32, lane64, BitVec.getElem_extractLsb', BitVec.getElem_setWidth]
  grind

@[simp↓] theorem eval_reinterpret256 (x : V256) :
    evalIntrinsic (.vector (.reinterpret 256)) [.v256 x] = some (.v256 x) := by rfl

@[simp↓] theorem eval_shift_right256 (a b c d : W64) :
    evalIntrinsic (.avx2 .shr64) [.v256 (pack256 a b c d), .i32 (BitVec.ofNat 32 32)] =
      some (.v256 (pack256 (a >>> 32) (b >>> 32) (c >>> 32) (d >>> 32))) := by
  change some (Value.v256 (map256 (· >>> 32) (pack256 a b c d))) = _
  simp only [map256, lane256_0, lane256_1, lane256_2, lane256_3]

@[simp↓] theorem eval_shift_left256 (a b c d : W64) :
    evalIntrinsic (.avx2 .shl64) [.v256 (pack256 a b c d), .i32 (BitVec.ofNat 32 32)] =
      some (.v256 (pack256 (a <<< 32) (b <<< 32) (c <<< 32) (d <<< 32))) := by
  change some (Value.v256 (map256 (· <<< 32) (pack256 a b c d))) = _
  simp only [map256, lane256_0, lane256_1, lane256_2, lane256_3]

@[simp↓] theorem eval_reverse256 (a b c d : W64) :
    evalIntrinsic (.avx2 .permute4x64) [.v256 (pack256 a b c d), .i32 (BitVec.ofNat 32 27)] =
      some (.v256 (pack256 d c b a)) := by
  change some (Value.v256 (permute4x64 (pack256 a b c d) (BitVec.ofNat 8 27))) = _
  simp (config := { implicitDefEqProofs := false }) only [permute4x64, show ((BitVec.ofNat 8 27).extractLsb' 0 2).toNat = 3 from rfl,
    show ((BitVec.ofNat 8 27).extractLsb' 2 2).toNat = 2 from rfl,
    show ((BitVec.ofNat 8 27).extractLsb' 4 2).toNat = 1 from rfl,
    show ((BitVec.ofNat 8 27).extractLsb' 6 2).toNat = 0 from rfl,
    lane256_0, lane256_1, lane256_2, lane256_3]

@[simp↓] theorem eval_sum256 (a b c d : W64) :
    evalIntrinsic (.vector (.sum64 256)) [.v256 (pack256 a b c d)] = some (.i64 (a+b+c+d)) := by
  change some (Value.i64 (lane64 (pack256 a b c d) 0 + lane64 (pack256 a b c d) 1 +
    lane64 (pack256 a b c d) 2 + lane64 (pack256 a b c d) 3)) = _
  simp only [lane256_0, lane256_1, lane256_2, lane256_3]

@[simp↓] theorem eval_add256 (a b c d e f g h : W64) :
    evalIntrinsic (.avx2 .add64) [.v256 (pack256 a b c d), .v256 (pack256 e f g h)] =
      some (.v256 (pack256 (a+e) (b+f) (c+g) (d+h))) := by
  change some (Value.v256 (zip256 (· + ·) (pack256 a b c d) (pack256 e f g h))) = _
  simp only [zip256, lane256_0, lane256_1, lane256_2, lane256_3]

@[simp↓] theorem eval_dq_product256 (a b c d e f g h : W64) :
    evalIntrinsic (.avx512DQ .mul64) [.v256 (pack256 a b c d), .v256 (pack256 e f g h)] =
      some (.v256 (pack256 (a*e) (b*f) (c*g) (d*h))) := by
  change some (Value.v256 (zip256 (· * ·) (pack256 a b c d) (pack256 e f g h))) = _
  simp only [zip256, lane256_0, lane256_1, lane256_2, lane256_3]

@[simp↓] theorem eval_even_product256 (a b c d e f g h : W64) :
    evalIntrinsic (.avx2 .multiplyEven32) [.v256 (pack256 a b c d), .v256 (pack256 e f g h)] =
      some (.v256 (pack256 (digitLow a * digitLow e) (digitLow b * digitLow f)
        (digitLow c * digitLow g) (digitLow d * digitLow h))) := by
  change some (Value.v256 (multiplyEven32 (pack256 a b c d) (pack256 e f g h))) = _
  have e0 (x : V256) : lane32 x 0 = (lane64 x 0).setWidth 32 := even_lane x 0
  have e1 (x : V256) : lane32 x 2 = (lane64 x 1).setWidth 32 := even_lane x 1
  have e2 (x : V256) : lane32 x 4 = (lane64 x 2).setWidth 32 := even_lane x 2
  have e3 (x : V256) : lane32 x 6 = (lane64 x 3).setWidth 32 := even_lane x 3
  simp only [multiplyEven32, e0, e1, e2, e3,
    lane256_0, lane256_1, lane256_2, lane256_3, digitLow]

end UInt256Proof.Multiply

