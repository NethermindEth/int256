import CIL.SIMD.Intrinsics
import CIL.SIMD.VectorLemmas

open CIL CIL.Vector

-- Portable operations: little-endian lanes, separate wrapping and all-bit masks.
example : lane64 (pack256 1 2 3 4) 2 = 3 := by decide
example : evalIntrinsic (.vector (.add64 128))
    [.v128 (pack128 (~~~0) 7), .v128 (pack128 1 2)] =
      some (.v128 (pack128 0 9)) := by decide
example : evalIntrinsic (.vector (.sub64 128))
    [.v128 (pack128 0 7), .v128 (pack128 1 2)] =
      some (.v128 (pack128 (~~~0) 5)) := by decide
example : evalIntrinsic (.vector (.ltu64 128))
    [.v128 (pack128 1 7), .v128 (pack128 2 2)] =
      some (.v128 (pack128 (~~~0) 0)) := by decide
example : evalIntrinsic (.vector (.eq64 128))
    [.v128 (pack128 1 7), .v128 (pack128 1 2)] =
      some (.v128 (pack128 (~~~0) 0)) := by decide
example : evalIntrinsic (.vector (.equalsAll 128)) [.v128 0, .v128 0] =
    some (.i32 1) := by decide
example : evalIntrinsic (.vector (.reinterpret 256)) [.v256 0x8000000000000000] =
    some (.v256 0x8000000000000000) := by decide
example : evalIntrinsic (.vector (.ashr64 128))
    [.v128 (pack128 0x8000000000000000 0x7FFFFFFFFFFFFFFF), .i32 63] =
      some (.v128 (pack128 (~~~0) 0)) := by decide
example : evalIntrinsic (.vector (.ashr64 128))
    [.v128 (pack128 1 2), .i32 64] = some (.v128 (pack128 1 2)) := by decide

-- ARM: extraction order is opposite to the managed SSSE3 alignment operands.
example : evalIntrinsic (.advSimd .extract64)
    [.v128 (pack128 1 2), .v128 (pack128 3 4), .i32 1] =
      some (.v128 (pack128 2 3)) := by decide
example : evalIntrinsic (.advSimd .extract64) [.v128 0, .v128 0, .i32 2] = none := by decide

-- SSE/SSSE3: byte counts, shifts zero out, alignment can cross halves.
example : evalIntrinsic (.sse .shiftLeftBytes) [.v128 (pack128 1 2), .i32 8] =
    some (.v128 (pack128 0 1)) := by decide
example : evalIntrinsic (.sse .shiftLeftBytes) [.v128 (~~~0), .i32 16] =
    some (.v128 0) := by decide
example : evalIntrinsic (.sse .alignBytes)
    [.v128 (pack128 3 4), .v128 (pack128 1 2), .i32 8] =
      some (.v128 (pack128 2 3)) := by decide
example : evalIntrinsic (.sse .alignBytes) [.v128 (~~~0), .v128 (~~~0), .i32 32] =
    some (.v128 0) := by decide

-- AVX2: selectors use successive low-to-high 2-bit/1-bit immediate fields.
example : evalIntrinsic (.avx2 .permute4x64) [.v256 (pack256 1 2 3 4), .i32 0x90] =
    some (.v256 (pack256 1 1 2 3)) := by decide
example : evalIntrinsic (.avx2 .blend32)
    [.v256 (pack256 1 2 3 4), .v256 0, .i32 3] =
      some (.v256 (pack256 0 2 3 4)) := by decide

-- AVX: MoveMask takes sign bits; integer TestZ examines every bit, not just signs.
example : evalIntrinsic (.avx .moveMask64)
    [.v256 (pack256 0x8000000000000000 0 0x8000000000000000 0)] =
      some (.i32 5) := by decide
example : evalIntrinsic (.avx .testZ64) [.v256 1, .v256 1] = some (.i32 0) := by decide
example : evalIntrinsic (.avx .testZ64) [.v256 1, .v256 2] = some (.i32 1) := by decide

-- AVX-512: count masking and all eight truth-table entries determine operand order.
example : evalIntrinsic (.avx512 .alignRight64)
    [.v256 (pack256 1 2 3 4), .v256 0, .i32 3] =
      some (.v256 (pack256 0 1 2 3)) := by decide
example : evalIntrinsic (.avx512 .alignRight64)
    [.v256 (pack256 1 2 3 4), .v256 0, .i32 7] =
      some (.v256 (pack256 0 1 2 3)) := by decide
example (a b c : BitVec 256) : ternaryLogic a b c 0xF0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ternaryLogic, List.range_succ, List.foldl_cons, List.foldl_nil,
    Nat.testBit_eq_decide_div_mod_eq, hi]
  grind
example (a b c : BitVec 256) : ternaryLogic a b c 0xCC = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ternaryLogic, List.range_succ, List.foldl_cons, List.foldl_nil,
    Nat.testBit_eq_decide_div_mod_eq, hi]
  grind
example (a b c : BitVec 256) : ternaryLogic a b c 0xAA = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ternaryLogic, List.range_succ, List.foldl_cons, List.foldl_nil,
    Nat.testBit_eq_decide_div_mod_eq, hi]
  grind

-- BMI: lengths clamp at word width; byte/bool bitcasts preserve the byte representation.
example : evalIntrinsic (.bmi1 .bextr32) [.i32 0x10, .i32 4, .i32 1] = some (.i32 1) := by decide
example : evalIntrinsic (.bmi1 .bextr32) [.i32 (~~~0), .i32 31, .i32 255] = some (.i32 1) := by decide
example : evalIntrinsic (.bmi1 .bextr32) [.i32 (~~~0), .i32 32, .i32 1] = some (.i32 0) := by decide
example : evalIntrinsic (.vector .byteToBool) [.i8 1] = some (.i32 1) := by decide
example : evalIntrinsic (.vector .byteToBool) [.i8 0x80] = some (.i32 0x80) := by decide

-- Invalid width, arity, mixed vector widths, non-byte immediate, and element index.
example : evalIntrinsic (.vector (.add64 64)) [.v128 1, .v128 2] = none := by decide
example : evalIntrinsic (.vector (.add64 128)) [.v128 1, .v256 2] = none := by decide
example : evalIntrinsic (.vector (.add64 128)) [.v128 1] = none := by decide
example : evalIntrinsic (.avx2 .permute4x64) [.v256 0, .i32 256] = none := by decide
example : evalIntrinsic (.vector (.extract64 128)) [.v128 0, .i32 2] = none := by decide

#print axioms CIL.Vector.ternary_add
#print axioms CIL.Vector.ternary_subtract

#print axioms CIL.Vector.pack256_lanes
#print axioms CIL.Vector.avx2_blend_incoming
#print axioms CIL.Vector.arithmetic_sign_mask
