import CIL.SIMD.AdvSimd
import CIL.SIMD.SSE
import CIL.SIMD.AVX2
import CIL.SIMD.AVX512
import CIL.SIMD.BMI1

namespace CIL.Vector

@[simp] theorem lane128_0 (a b : W64) : lane64 (pack128 a b) 0 = a := by
  simp only [lane64, pack128]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
@[simp] theorem lane128_1 (a b : W64) : lane64 (pack128 a b) 1 = b := by
  simp only [lane64, pack128]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem lane256_0 (a b c d : W64) : lane64 (pack256 a b c d) 0 = a := by
  simp only [lane64, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
@[simp] theorem lane256_1 (a b c d : W64) : lane64 (pack256 a b c d) 1 = b := by
  simp only [lane64, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
@[simp] theorem lane256_2 (a b c d : W64) : lane64 (pack256 a b c d) 2 = c := by
  simp only [lane64, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind
@[simp] theorem lane256_3 (a b c d : W64) : lane64 (pack256 a b c d) 3 = d := by
  simp only [lane64, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

theorem pack128_lanes (x : V128) : pack128 (lane64 x 0) (lane64 x 1) = x := by
  simp only [lane64, pack128]
  ext i hi
  grind

theorem pack256_lanes (x : V256) :
    pack256 (lane64 x 0) (lane64 x 1) (lane64 x 2) (lane64 x 3) = x := by
  unfold lane64 pack256
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb'

theorem reinterpret_identity (x : BitVec n) : reinterpret x = x := rfl
theorem reinterpret_roundtrip (x : BitVec n) : reinterpret (reinterpret x) = x := rfl

@[simp] theorem adv_incoming (a b c d : W64) :
    advExtract64 (pack128 a b) (pack128 c d) 1 = pack128 b c := by
  simp only [advExtract64, pack128]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

theorem sse_arm_alignment (a b c d : W64) :
    ssseAlignBytes (pack128 c d) (pack128 a b) 8 =
      advExtract64 (pack128 a b) (pack128 c d) 1 := rfl

@[simp] theorem sse_incoming_low (a b : W64) :
    sseShiftLeftBytes (pack128 a b) 8 = pack128 0 a := by
  simp only [sseShiftLeftBytes, pack128]
  ext i hi
  simp only [BitVec.getElem_shiftLeft]
  grind

@[simp] theorem avx512_incoming (a b c d : W64) :
    alignRight64 (pack256 a b c d) 0 3 = pack256 0 a b c := by
  simp only [alignRight64, pack256]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  grind

@[simp] theorem avx2_permute_incoming (a b c d : W64) :
    permute4x64 (pack256 a b c d) 0x90 = pack256 a a b c := by
  simp [permute4x64]

@[simp] theorem avx2_blend_incoming (a b c d : W64) :
    blend32 (pack256 a b c d) 0 3 = pack256 0 b c d := by
  simp only [blend32, lane32]
  dsimp
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  have high : (pack256 a b c d).extractLsb' 128 128 = pack128 c d :=
    BitVec.extractLsb'_append_eq_left
  have mid : (pack256 a b c d).extractLsb' 64 64 = b := lane256_1 a b c d
  rw [high, mid]
  rfl

theorem avx2_incoming_blend_normal (a b c d : W64) :
    blend32 (permute4x64 (pack256 a b c d) (BitVec.ofNat 8 144))
      (BitVec.ofNat 256 0) (BitVec.ofNat 8 3) = pack256 (BitVec.ofNat 64 0) a b c := by
  have hp := avx2_permute_incoming a b c d
  change permute4x64 (pack256 a b c d) (BitVec.ofNat 8 144) = pack256 a a b c at hp
  rw [hp]
  exact avx2_blend_incoming a a b c

theorem arithmetic_sign_mask (a : W64) :
    a.sshiftRight 63 = mask64 a.msb := by
  change a.sshiftRight 63 = if a.msb then BitVec.allOnes 64 else 0
  ext i hi
  cases h : a.msb <;>
    simp only [h, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getElem_sshiftRight, BitVec.getElem_allOnes]
  all_goals split <;> simp_all [BitVec.msb, BitVec.getMsbD]
  all_goals grind

theorem ternary_add (a b r : BitVec n) :
    ternaryLogic a b r 0xD4 = (a &&& b) ||| ((~~~r) &&& (a ||| b)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ternaryLogic, List.range_succ, List.foldl_cons, List.foldl_nil,
    Nat.testBit_eq_decide_div_mod_eq, hi]
  generalize ha : a[i] = aa
  generalize hb : b[i] = bb
  generalize hr : r[i] = rr
  cases aa <;> cases bb <;> cases rr <;> decide

theorem ternary_subtract (a b r : BitVec n) :
    ternaryLogic a b r 0x8E = ((~~~a) &&& b) ||| ((~~~(a ^^^ b)) &&& r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [ternaryLogic, List.range_succ, List.foldl_cons, List.foldl_nil,
    Nat.testBit_eq_decide_div_mod_eq, hi]
  generalize ha : a[i] = aa
  generalize hb : b[i] = bb
  generalize hr : r[i] = rr
  cases aa <;> cases bb <;> cases rr <;> decide

end CIL.Vector
