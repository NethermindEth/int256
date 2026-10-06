import Extracted
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

/-- Discover the reachable leaf containing the limb reads; its body is still
    executed and checked below, never assigned a contract by its shape. -/
def scalarIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with | .field _ => true | _ => false) &&
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false)

def scalarDifference (memory : Memory) (left right : Reference) : BitVec 64 :=
  (inputLimb memory left 0 ^^^ inputLimb memory right 0) |||
  (inputLimb memory left 1 ^^^ inputLimb memory right 1) |||
  (inputLimb memory left 2 ^^^ inputLimb memory right 2) |||
  (inputLimb memory left 3 ^^^ inputLimb memory right 3)

theorem scalar_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel scalarIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if scalarDifference memory left right = 0 then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := rfl
  conv in scalarIndex => cbv
  refine ⟨28, ?_⟩
  -- This is a checked sufficient execution prefix, not an assumed summary:
  -- every fetched opcode and transition must prove before the final return.
  iterate 26
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl, hr, hc, pureArity, scalars, CIL.step, CIL.binary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, numericValue, scalarDifference,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms scalar_run

end UInt256Proof.Equality.Safety
