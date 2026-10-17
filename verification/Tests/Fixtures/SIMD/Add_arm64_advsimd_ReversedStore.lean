import Extracted
import UInt256.Methods.Add.ARMExpansion

namespace UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_ReversedStore
open UInt256Model.Safety.CodeExpansion UInt256Proof.Add.Safety

/-- The four limb pushes before the storage call run in reverse order. -/
def edits : Nat → List (Nat × Edit)
  | 3 => [(48, .reverse [5, 1, 2, 3] 4 5), (49, .skip), (50, .skip), (51, .skip), (52, .skip)]
  | _ => []

/-- Limb storage receives the four limbs in reverse argument order. -/
def arguments : Nat → List Nat
  | 4 => reversal 5 4
  | _ => []

theorem expansion : Expansion (armProgram Extracted.profile) Extracted.program id edits arguments where
  body m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;>
      exact body_of_code rfl rfl (by decide +kernel)
  static m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;>
      rfl
  frames m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;>
      exact ⟨rfl, rfl⟩
  checked m b found := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp only [armProgram, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.some.injEq, reduceCtorEq] at found <;> subst found <;>
      decide +kernel
  calls m b found pc h member := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp [edits] at member
  folds m b found pc h member := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp [edits] at member

/-- Limbs passed to storage in reverse argument order keep the production AdvSimd Add contract. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  wrapping_transfer expansion rfl rfl (arm_program_contract Extracted.profile rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_ReversedStore
