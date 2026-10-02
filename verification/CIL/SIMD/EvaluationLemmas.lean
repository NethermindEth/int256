import CIL.SIMD.VectorLemmas
import CIL.SIMD.Intrinsics

open CIL

namespace CIL.Vector

@[simp] theorem intrinsic_create256 (a b c d : W64) :
    evalIntrinsic (.vector (.create64 256)) [.i64 a, .i64 b, .i64 c, .i64 d] =
      some (.v256 (pack256 a b c d)) := rfl

theorem avx2_incoming_mask (a b c d : W64) :
    permute4x64 (pack256 a b c d) (BitVec.ofNat 8 144) &&&
      pack256 (BitVec.ofNat 64 0) (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 18446744073709551615) =
    pack256 0 a b c := by
  rw [show permute4x64 (pack256 a b c d) (BitVec.ofNat 8 144) =
    pack256 a a b c from avx2_permute_incoming a b c d]
  unfold pack256
  rw [BitVec.and_append, BitVec.and_append, BitVec.and_append]
  change ((c &&& BitVec.allOnes 64) ++ (b &&& BitVec.allOnes 64)) ++
    ((a &&& BitVec.allOnes 64) ++ (a &&& 0)) = (c ++ b) ++ (a ++ 0)
  rw [BitVec.and_allOnes, BitVec.and_allOnes, BitVec.and_allOnes]
  have hz : a &&& (0 : W64) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp
  rw [hz]

theorem avx512_incoming_normal (a b c d : W64) :
    alignRight64 (pack256 a b c d) (BitVec.ofNat 256 0) 3 =
      pack256 (BitVec.ofNat 64 0) a b c := avx512_incoming a b c d

@[simp] theorem intrinsic_bextr_flag (a : W32) :
    evalIntrinsic (.bmi1 .bextr32)
      [.i32 a, .i32 (BitVec.ofNat 32 4), .i32 (BitVec.ofNat 32 1)] =
      some (.i32 (bextr32 a 4 1)) := rfl

theorem bextr_flag_bound (a : W32) : (bextr32 a 4 1).toNat < 256 := by
  simp only [bextr32, show ¬ (4 : Nat) ≥ 32 from by decide, ↓reduceIte]
  change ((a >>> 4) &&& BitVec.ofNat 32 1).toNat < 256
  have h : (a >>> 4).toNat &&& 1 ≤ 1 := Nat.and_le_right
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at *
  change (a >>> 4).toNat &&& 1 < 256
  omega

theorem bextr_flag_value (a : W32) :
    bextr32 a 4 1 = if a.getLsbD 4 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
  change (a >>> 4) &&& BitVec.ofNat 32 1 = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases i with
  | zero =>
    cases h : a.getLsbD 4 <;> simp [h]
    change a[4] = false at h
    exact h
  | succ i =>
    cases h : a.getLsbD 4 <;>
      simp [BitVec.getLsbD_ofNat, Nat.testBit_add_one]

theorem bit4_mask_value (a : W32) :
    a &&& BitVec.ofNat 32 16 =
      if a.getLsbD 4 then BitVec.ofNat 32 16 else BitVec.ofNat 32 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have maskBit : (BitVec.ofNat 32 16).getLsbD i = decide (4 = i) := by
    rw [BitVec.getLsbD_ofNat]
    change (decide (i < 32) && Nat.testBit (2^4) i) = decide (4 = i)
    rw [Nat.testBit_two_pow]
    simp only [hi, decide_true, Bool.true_and]
  simp only [BitVec.getLsbD_and, maskBit]
  cases h : a.getLsbD 4 <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_zero, maskBit]
  all_goals by_cases position : i = 4
  all_goals first
    | subst i; simp only [h, decide_true, Bool.and_true]
    | simp [Ne.symm position]

theorem bextr_mask_flag_agree (a : W32) :
    (bextr32 a 4 1 != BitVec.ofNat 32 0) =
      ((a &&& BitVec.ofNat 32 16) != BitVec.ofNat 32 0) := by
  rw [bextr_flag_value, bit4_mask_value]
  cases a.getLsbD 4 <;> decide

@[simp] theorem intrinsic_sub128 (a b : V128) :
    evalIntrinsic (.vector (.sub64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (· - ·) a b)) := rfl
@[simp] theorem intrinsic_add128 (a b : V128) :
    evalIntrinsic (.vector (.add64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (· + ·) a b)) := rfl
@[simp] theorem intrinsic_lt128 (a b : V128) :
    evalIntrinsic (.vector (.ltu64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (fun x y => mask64 (x.ult y)) a b)) := rfl
@[simp] theorem intrinsic_eq128 (a b : V128) :
    evalIntrinsic (.vector (.eq64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (fun x y => mask64 (x == y)) a b)) := rfl
@[simp] theorem intrinsic_and128 (a b : V128) :
    evalIntrinsic (.vector (.band 128)) [.v128 a, .v128 b] = some (.v128 (a &&& b)) := rfl
@[simp] theorem intrinsic_or128 (a b : V128) :
    evalIntrinsic (.vector (.bor 128)) [.v128 a, .v128 b] = some (.v128 (a ||| b)) := rfl
@[simp] theorem intrinsic_zero128 :
    evalIntrinsic (.vector (.zero 128)) [] = some (.v128 0) := rfl
@[simp] theorem intrinsic_equal_all128 (a b : V128) :
    evalIntrinsic (.vector (.equalsAll 128)) [.v128 a, .v128 b] =
      some (.i32 (if a == b then 1 else 0)) := rfl
@[simp] theorem intrinsic_adv_extract (a b : V128) :
    evalIntrinsic (.advSimd .extract64) [.v128 a, .v128 b, .i32 (BitVec.ofNat 32 1)] =
      some (.v128 (advExtract64 a b 1)) := rfl
@[simp] theorem intrinsic_sse_shift (a : V128) :
    evalIntrinsic (.sse .shiftLeftBytes) [.v128 a, .i32 (BitVec.ofNat 32 8)] =
      some (.v128 (sseShiftLeftBytes a 8)) := rfl
@[simp] theorem intrinsic_sse_align (a b : V128) :
    evalIntrinsic (.sse .alignBytes) [.v128 a, .v128 b, .i32 (BitVec.ofNat 32 8)] =
      some (.v128 (ssseAlignBytes a b 8)) := rfl
@[simp] theorem intrinsic_reinterpret128 (a : V128) :
    evalIntrinsic (.vector (.reinterpret 128)) [.v128 a] = some (.v128 a) := rfl
@[simp] theorem intrinsic_extract128 (a : V128) :
    evalIntrinsic (.vector (.extract64 128)) [.v128 a, .i32 (BitVec.ofNat 32 1)] = some (.i64 (lane64 a 1)) := rfl

theorem pack128_zero : pack128 0 0 = 0 := by decide

@[simp] theorem lane128_zero (i : Nat) : lane64 (BitVec.ofNat 128 0) i = 0 := by
  simp [lane64]

@[simp] theorem adv_incoming_zero (a b : W64) :
    advExtract64 (BitVec.ofNat 128 0) (pack128 a b) 1 = pack128 0 a := by
  change advExtract64 (pack128 0 0) (pack128 a b) 1 = pack128 0 a
  exact adv_incoming 0 0 a b

theorem pack128_and (a b c d : W64) :
    pack128 a b &&& pack128 c d = pack128 (a &&& c) (b &&& d) := BitVec.and_append
theorem pack128_or (a b c d : W64) :
    pack128 a b ||| pack128 c d = pack128 (a ||| c) (b ||| d) := BitVec.or_append

end CIL.Vector
