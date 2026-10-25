import UInt256.Generated.AddTemplates
import UInt256.Methods.Add.ARMEntry
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
def armBody (profile : CIL.FeatureProfile) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Add.method2
      $(Lean.mkIdent `profile) true 0 0)) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
def armWordSpec : NumericLocalSpec := ⟨.word64, .i64 0, 0, rfl⟩
def armSpecs : List NumericLocalSpec := List.replicate 14 vector128ZeroSpec ++ List.replicate 5 armWordSpec ++ List.replicate 4 vector128ZeroSpec

theorem armSpecs_first : ∀ i : Fin 14, armSpecs[i.val]? = some vector128ZeroSpec := by
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem armSpecs_repair : ∀ i : Fin 4, armSpecs[19 + i.val]? = some vector128ZeroSpec := by
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

theorem arm_helper_checked (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true)
    (program : CIL.Program) (method : Nat) (found : program[method]? = some (armBody profile))
    (memory : Memory) (left right output : Reference) (flag : BitVec 32)
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let b := armBody profile
  have disabledFalse (disabled : b.profile.advSimd = false) : False := by
    change profile.advSimd = false at disabled
    rw [enabled] at disabled
    contradiction
  apply checked_vector128_arm_contract program b method armSpecs found
    rfl (by simp only [b, armBody, incomingPrefix, enabled, ite_true]; rfl)
    rfl armSpecs_first (fun disabled => (disabledFalse disabled).elim)
    (fun disabled => (disabledFalse disabled).elim)
    (by simp only [b, armBody, earlyOutputCode, enabled, ite_true]; rfl)
    rfl (by simp only [b, armBody, decisionCode, enabled, ite_true]; rfl)
    (by simp only [b, armBody, fastOutputCode, enabled, ite_true]; rfl) rfl
    rfl rfl armSpecs_repair ⟨rfl,rfl⟩ rfl rfl rfl enabled
    memory left right output flag flagFit call
#print axioms arm_helper_checked
end UInt256Proof.Add.Safety
