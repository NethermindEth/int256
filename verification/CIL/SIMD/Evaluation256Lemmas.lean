import CIL.SIMD.EvaluationLemmas

open CIL

namespace CIL.Vector

@[simp] theorem intrinsic_add256 (a b : V256) :
    evalIntrinsic (.vector (.add64 256)) [.v256 a, .v256 b] =
      some (.v256 (zip256 (· + ·) a b)) := rfl
@[simp] theorem intrinsic_sub256 (a b : V256) :
    evalIntrinsic (.vector (.sub64 256)) [.v256 a, .v256 b] =
      some (.v256 (zip256 (· - ·) a b)) := rfl
@[simp] theorem intrinsic_lt256 (a b : V256) :
    evalIntrinsic (.vector (.ltu64 256)) [.v256 a, .v256 b] =
      some (.v256 (zip256 (fun x y => mask64 (x.ult y)) a b)) := rfl
@[simp] theorem intrinsic_eq256 (a b : V256) :
    evalIntrinsic (.vector (.eq64 256)) [.v256 a, .v256 b] =
      some (.v256 (zip256 (fun x y => mask64 (x == y)) a b)) := rfl
@[simp] theorem intrinsic_and256 (a b : V256) :
    evalIntrinsic (.vector (.band 256)) [.v256 a, .v256 b] = some (.v256 (a &&& b)) := rfl
@[simp] theorem intrinsic_reinterpret256 (a : V256) :
    evalIntrinsic (.vector (.reinterpret 256)) [.v256 a] = some (.v256 a) := rfl
@[simp] theorem intrinsic_zero256 :
    evalIntrinsic (.vector (.zero 256)) [] = some (.v256 0) := rfl
@[simp] theorem intrinsic_ones256 :
    evalIntrinsic (.vector (.ones 256)) [] = some (.v256 (~~~0)) := rfl
@[simp] theorem intrinsic_permute256 (a : V256) :
    evalIntrinsic (.avx2 .permute4x64) [.v256 a, .i32 (BitVec.ofNat 32 0x90)] =
      some (.v256 (permute4x64 a 0x90)) := rfl
@[simp] theorem intrinsic_blend256 (a b : V256) :
    evalIntrinsic (.avx2 .blend32) [.v256 a, .v256 b, .i32 (BitVec.ofNat 32 3)] =
      some (.v256 (blend32 a b 3)) := rfl
@[simp] theorem intrinsic_align256 (a b : V256) :
    evalIntrinsic (.avx512 .alignRight64) [.v256 a, .v256 b, .i32 (BitVec.ofNat 32 3)] =
      some (.v256 (alignRight64 a b 3)) := rfl
@[simp] theorem intrinsic_ternary_add256 (a b c : V256) :
    evalIntrinsic (.avx512 .ternaryLogic) [.v256 a, .v256 b, .v256 c, .i32 (BitVec.ofNat 32 0xD4)] =
      some (.v256 (ternaryLogic a b c 0xD4)) := rfl
@[simp] theorem intrinsic_ternary_sub256 (a b c : V256) :
    evalIntrinsic (.avx512 .ternaryLogic) [.v256 a, .v256 b, .v256 c, .i32 (BitVec.ofNat 32 0x8E)] =
      some (.v256 (ternaryLogic a b c 0x8E)) := rfl
@[simp] theorem intrinsic_sign256 (a : V256) :
    evalIntrinsic (.vector (.ashr64 256)) [.v256 a, .i32 (BitVec.ofNat 32 63)] =
      some (.v256 (map256 (fun x => x.sshiftRight 63) a)) := rfl
@[simp] theorem intrinsic_movemask256 (a : V256) :
    evalIntrinsic (.avx .moveMask64) [.v256 a] = some (.i32 (moveMask64 a)) := rfl
@[simp] theorem intrinsic_testz256 (a b : V256) :
    evalIntrinsic (.avx .testZ64) [.v256 a, .v256 b] =
      some (.i32 (if (a &&& b) == 0 then 1 else 0)) := rfl

theorem pack256_zero : pack256 0 0 0 0 = 0 := by decide

private theorem append_eq {a b c d : V128} (h : a = b) (k : c = d) :
    a ++ c = b ++ d := by
  cases h
  cases k
  rfl

theorem pack256_and (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    pack256 a0 a1 a2 a3 &&& pack256 b0 b1 b2 b3 =
      pack256 (a0 &&& b0) (a1 &&& b1) (a2 &&& b2) (a3 &&& b3) := by
  unfold pack256
  exact (@BitVec.and_append 128 128 (a3 ++ a2) (b3 ++ b2) (a1 ++ a0) (b1 ++ b0)).trans
    (append_eq BitVec.and_append BitVec.and_append)

theorem pack256_or (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    pack256 a0 a1 a2 a3 ||| pack256 b0 b1 b2 b3 =
      pack256 (a0 ||| b0) (a1 ||| b1) (a2 ||| b2) (a3 ||| b3) := by
  unfold pack256
  exact (@BitVec.or_append 128 128 (a3 ++ a2) (b3 ++ b2) (a1 ++ a0) (b1 ++ b0)).trans
    (append_eq BitVec.or_append BitVec.or_append)

theorem pack256_not (a0 a1 a2 a3 : W64) :
    ~~~(pack256 a0 a1 a2 a3) = pack256 (~~~a0) (~~~a1) (~~~a2) (~~~a3) := by
  unfold pack256
  exact (@BitVec.not_append 128 128 (a3 ++ a2) (a1 ++ a0)).trans
    (append_eq BitVec.not_append BitVec.not_append)

theorem pack256_xor (a0 a1 a2 a3 b0 b1 b2 b3 : W64) :
    pack256 a0 a1 a2 a3 ^^^ pack256 b0 b1 b2 b3 =
      pack256 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) := by
  unfold pack256
  exact (@BitVec.xor_append 128 128 (a3 ++ a2) (b3 ++ b2) (a1 ++ a0) (b1 ++ b0)).trans
    (append_eq BitVec.xor_append BitVec.xor_append)

end CIL.Vector
