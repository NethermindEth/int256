import Extracted
import UInt256.Methods.Add.ARMExpansion

namespace UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_ExtractedHelper
open UInt256Model.Safety.CodeExpansion UInt256Proof.Add.Safety

/-- Production methods keep their order; the two helpers sit before the scalar tail. -/
def remap (index : Nat) : Nat := [0, 1, 2, 5, 6].getD index index

/-- The lane extract becomes a call to method 4 and the propagation merge a call to method 3. -/
def edits : Nat → List (Nat × Edit)
  | 2 => [(46, .fold 4), (47, .skip), (100, .call 3)]
  | _ => []

theorem expansion : Expansion (armProgram Extracted.profile) Extracted.program remap edits (fun _ => []) where
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
    obtain ⟨rfl, rfl⟩ := member
    simp only [armProgram, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
    subst found
    exact ⟨_, rfl, rfl⟩
  folds m b found pc h member := by
    rcases m with _ | _ | _ | _ | _ | m <;> simp [edits] at member
    obtain ⟨rfl, rfl⟩ := member
    simp only [armProgram, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
    subst found
    exact ⟨_, _, rfl, rfl, rfl⟩

/-- Lane extract and merge moved into private helpers keep the production AdvSimd Add contract. -/
theorem correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  wrapping_transfer expansion rfl rfl (arm_program_contract Extracted.profile rfl rfl)

#print axioms correctness
end UInt256Proof.Fixture.SIMD.Add_arm64_advsimd_ExtractedHelper
