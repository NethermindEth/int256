import UInt256.Generated.MethodTemplates
import CIL.Safety.Equations
import UInt256.Methods.Multiply.Calls

/-!
The widening word multiply on hardware with a high-product instruction: BMI2 or ARM64 computes
the high word, and the ordinary product is stored through the output reference.
-/
namespace UInt256Proof.Multiply
def bmiWordBody (profile : CIL.FeatureProfile) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method11 $(Lean.mkIdent `profile) true false)) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

def armWordBody (profile : CIL.FeatureProfile) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method11 $(Lean.mkIdent `profile) false true)) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

end UInt256Proof.Multiply
namespace UInt256Proof.Multiply
open CIL.Safety

def hardwareWordBody (arm : Bool) (profile : CIL.FeatureProfile) : CIL.Method :=
  if arm then armWordBody profile else bmiWordBody profile

def hardwareWordIntrinsic (arm : Bool) : CIL.Intrinsic :=
  if arm then .armBase64 .multiplyHigh64 else .bmi2 .multiplyHigh64

/-- Either hardware body stores the low product and returns the high product. -/
theorem hardware_word_contract (arm : Bool) (profile : CIL.FeatureProfile)
    (bmi : profile.bmi2 = !arm) (armEnabled : arm = true → profile.armBase64 = true)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (hardwareWordBody arm profile)) : Calls.WordContract program index := by
  intro memory a b output wf writable
  have formed := access_reference_valid _ _ _ _ _ writable
  have length : (numberBytes (lowProduct a b).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨final, written⟩ := write_succeeds (bytes := numberBytes (lowProduct a b).toNat 8)
    (by simpa only [length] using writable)
  have loaded := write_readback _ _ _ _ _ written
  rw [length] at loaded
  refine ⟨if arm then 13 else 11, final, ?_, write_preserves_wellFormed _ _ _ _ _ wf written,
    loaded, write_preserves_access_below written _, fun id _ offset outside =>
      write_outside _ _ _ _ _ _ _ written (by simpa only [length] using outside)⟩
  have bmiFeature : profile.evaluate .bmi2 = !arm := bmi
  cases arm
  · cil_checked_steps [found, hardwareWordBody, bmiWordBody, bmiFeature, bmi, formed, written,
      lowProduct]
    rfl
  · have armFeature : profile.evaluate .armBase64 = true := armEnabled rfl
    cil_checked_steps [found, hardwareWordBody, armWordBody, bmiFeature, armFeature,
      armEnabled rfl, formed, written, lowProduct]
    rfl

end UInt256Proof.Multiply
