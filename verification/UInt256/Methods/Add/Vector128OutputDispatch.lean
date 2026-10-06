import UInt256.Methods.Add.Vector128Snapshots
import UInt256.Safety.OutputHalves

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128EarlyOutputStart : Nat := if Extracted.profile.advSimd then 73 else 82

/-- SkipInit checks the output reference but neither initializes nor reads its
    bytes. The extracted feature guard selects ARM's early stores or SSE's skip. -/
theorem vector128_output_dispatch (memory : Memory) (output : Reference)
    (frame : Frame) (args : List Value)
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index vector128EarlyOutputStart args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 69 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  conv at continuation in vector128EarlyOutputStart => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, argument, checkedValue, formValue, formed, instruction,
           pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           numericValue, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_output_dispatch
end UInt256Proof.Add.Safety
