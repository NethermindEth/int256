import Extracted
import UInt256.Methods.Add.ARMExpansion

namespace UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_FeatureExpressions
open UInt256Model.Safety.CodeExpansion UInt256Proof.Add.Safety

/-- Each repeated feature test becomes `feature, feature, and`. -/
def edits : Nat → List (Nat × Edit)
  | 0 => [(0, .dup)]
  | 1 => [(0, .dup)]
  | 2 => [(37, .dup), (71, .dup), (111, .dup)]
  | 3 => [(12, .dup)]
  | _ => []

theorem expansion : Expansion (armProgram Extracted.profile) Extracted.program id edits where
  body m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;>
      exact body_of_code rfl rfl (by decide +kernel)
  static m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;> rfl
  checked m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;> decide +kernel
  calls m b found pc h member := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp [edits] at member
  folds m b found pc h member := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp [edits] at member

/-- Duplicated feature tests keep the production AdvSimd Add contract. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  wrapping_transfer expansion rfl (arm_program_contract Extracted.profile rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_FeatureExpressions
