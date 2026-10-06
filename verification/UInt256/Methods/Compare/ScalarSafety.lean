import Extracted
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def scalarIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with | .field _ => true | _ => false) &&
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false)

def scalarResult (memory : Memory) (left right : Reference) : BitVec 32 :=
  if inputLimb memory left 3 = inputLimb memory right 3 then
    if inputLimb memory left 2 = inputLimb memory right 2 then
      if inputLimb memory left 1 = inputLimb memory right 1 then
        if (inputLimb memory left 0).toNat < (inputLimb memory right 0).toNat then 1 else 0
      else if (inputLimb memory left 1).toNat < (inputLimb memory right 1).toNat then 1 else 0
    else if (inputLimb memory left 2).toNat < (inputLimb memory right 2).toNat then 1 else 0
  else if (inputLimb memory left 3).toNat < (inputLimb memory right 3).toNat then 1 else 0

macro "comparison_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, CIL.step, CIL.binary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

theorem scalar_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel scalarIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (scalarResult memory left right))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  conv in scalarIndex => cbv
  refine ⟨48, ?_⟩
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3
  · by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2
    · by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1
      · comparison_steps 20 with fl, fr, hl, hr, h3, h2, h1
        simp [run, cil_code, step, checkedValue, numericValue, scalarResult, h3, h2, h1,
          BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · comparison_steps 20 with fl, fr, hl, hr, h3, h2, h1
        simp [run, cil_code, step, checkedValue, numericValue, scalarResult, h3, h2, h1,
          BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · comparison_steps 15 with fl, fr, hl, hr, h3, h2
      simp [run, cil_code, step, checkedValue, numericValue, scalarResult, h3, h2,
        BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · comparison_steps 10 with fl, fr, hl, hr, h3
    simp [run, cil_code, step, checkedValue, numericValue, scalarResult, h3,
      BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_run
end UInt256Proof.Compare.Safety
