import Extracted
import UInt256.Safety.Contract
import UInt256.Safety.UnaryOutput
import UInt256.Safety.OutputValue
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import UInt256.Safety.CallerSetup
import UInt256.Safety.InitializedOutput

namespace UInt256Proof.Bitwise.NotSafety
open CIL.Safety UInt256Model.Safety

def vectorIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.bnot 256)) _ => true | _ => false

def vectorBody : CIL.Method := Extracted.program[vectorIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem vector_run (memory : Memory) (input output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ final,
      run Extracted.program 8 vectorIndex 0 (unaryArguments input output) frame [] memory =
        .ok (leaveFrame frame final, []) ∧
      CallingConditions Extracted.program final [input] [output] ∧
      (∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset) ∧
      read final output 32 1 = .ok (numberBytes (~~~(inputValue memory input)).toNat 32) := by
  let result := ~~~(inputValue memory input)
  have length : (numberBytes result.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨final, written, retained, outside, readback⟩ := call.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes result.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  simp [result] at written
  refine ⟨final, ?_, retained, outside, readback⟩
  have fl := call.input_formed (reference := input) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have hl := call.input_load (reference := input) (by simp)
  have intrinsic (x : BitVec 256) :
      CIL.evalIntrinsic (.vector (.bnot 256)) [.v256 x] = some (.v256 (~~~x)) := rfl
  conv in vectorIndex => cbv
  iterate 7
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, unaryArguments, checkedValue, numericValue, formValue, fl, fo, hl,
            pureArity, scalars, staticInstruction, memoryInstruction, storeValue, referenceAt,
            CIL.step.eq_def, CIL.Intrinsic.available, intrinsic, written,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_run

theorem vector_initialized : InitializedUnaryContract (fun input => ~~~input) Extracted.program vectorIndex := by
  intro memory input output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have setup : enterFrame vectorBody (unaryArguments input output) memory = .ok (frame, memory) := by rfl
  have checked : (unaryArguments input output).mapM (checkedValue memory) =
      .ok (unaryArguments input output) := by
    have fl := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [unaryArguments, checkedValue, formValue, fl, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨final, finished, retained, outside, readback⟩ := vector_run memory input output frame call
  simp only [leaveFrame, frame, List.foldl_nil] at finished
  refine ⟨8, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    readback, ?_, ?_⟩
  · exact retained.1.2.2 (wordView output) (by simp)
  · intro id _ offset beyond
    exact outside id offset beyond

#print axioms vector_initialized
end UInt256Proof.Bitwise.NotSafety
