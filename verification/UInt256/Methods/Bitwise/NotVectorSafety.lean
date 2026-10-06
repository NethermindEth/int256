import Extracted
import UInt256.Safety.Contract
import UInt256.Safety.UnaryOutput
import UInt256.Safety.OutputValue
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

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
            CIL.step, CIL.Intrinsic.available, intrinsic, written,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_run
end UInt256Proof.Bitwise.NotSafety
