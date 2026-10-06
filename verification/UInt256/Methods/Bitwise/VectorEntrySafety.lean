import Extracted
import UInt256.Safety.Contract
import UInt256.Methods.Bitwise.Contract
import UInt256.Safety.OutputValue
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import UInt256.Safety.CallerSetup
import UInt256.Safety.InitializedOutput
import CIL.Safety.CallComposition

namespace UInt256Proof.Bitwise.Safety
open CIL.Safety UInt256Model.Safety

def vectorIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.bxor 256)) _ | .intrinsic (.vector (.band 256)) _
    | .intrinsic (.vector (.bor 256)) _ => true | _ => false

def vectorBody : CIL.Method := Extracted.program[vectorIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- Discovery proposes an operation; each public gate binds it to its independent specification. -/
def vectorOperation : UInt256Model.Bitwise.Binary :=
  if vectorBody.code.any (fun op => match op with | .intrinsic (.vector (.band 256)) _ => true | _ => false)
  then .and
  else if vectorBody.code.any (fun op => match op with | .intrinsic (.vector (.bor 256)) _ => true | _ => false)
  then .or else .xor

theorem vector_run (memory : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ final,
      run Extracted.program 11 vectorIndex 0 (binaryArguments left right output) frame [] memory =
        .ok (leaveFrame frame final, []) ∧
      CallingConditions Extracted.program final [left, right] [output] ∧
      (∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset) ∧
      read final output 32 1 = .ok (numberBytes (UInt256Model.Bitwise.applyBinary vectorOperation (inputValue memory left) (inputValue memory right)).toNat 32) := by
  let result := UInt256Model.Bitwise.applyBinary vectorOperation (inputValue memory left) (inputValue memory right)
  have length : (numberBytes result.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨final, written, retained, outside, readback⟩ := call.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes result.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  have selected : vectorOperation = vectorOperation := rfl
  conv at selected => rhs; cbv
  simp [result, selected, UInt256Model.Bitwise.applyBinary] at written
  refine ⟨final, ?_, retained, outside, readback⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have hl := call.input_load (reference := left) (by simp)
  have hr := call.input_load (reference := right) (by simp)
  have intrinsic (x y : BitVec 256) :
      CIL.evalIntrinsic (.vector (.bxor 256)) [.v256 x, .v256 y] = some (.v256 (x ^^^ y)) := rfl
  have intrinsic_and (x y : BitVec 256) :
      CIL.evalIntrinsic (.vector (.band 256)) [.v256 x, .v256 y] = some (.v256 (x &&& y)) := rfl
  have intrinsic_or (x y : BitVec 256) :
      CIL.evalIntrinsic (.vector (.bor 256)) [.v256 x, .v256 y] = some (.v256 (x ||| y)) := rfl
  conv in vectorIndex => cbv
  iterate 10
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo, hl, hr,
            pureArity, scalars, staticInstruction, memoryInstruction, storeValue, referenceAt,
            CIL.step.eq_def, CIL.Intrinsic.available, intrinsic, intrinsic_and, intrinsic_or, written, result, selected, UInt256Model.Bitwise.applyBinary,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_run

theorem vector_initialized : InitializedBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation) Extracted.program vectorIndex := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have setup : enterFrame vectorBody (binaryArguments left right output) memory = .ok (frame, memory) := by rfl
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨final, finished, retained, outside, readback⟩ := vector_run memory left right output frame call
  simp only [leaveFrame, frame, List.foldl_nil] at finished
  refine ⟨11, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    readback, ?_, ?_⟩
  · exact retained.1.2.2 (wordView output) (by simp)
  · intro id _ offset beyond
    exact outside id offset beyond

theorem vector_checked : WrappingBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation)
    Extracted.program vectorIndex := vector_initialized.to_wrapping

#print axioms vector_initialized
#print axioms vector_checked

def binaryIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .call callee 3 => callee == vectorIndex | _ => false

def binaryBody : CIL.Method := Extracted.program[binaryIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem vector_entry_initialized : InitializedBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation)
    Extracted.program binaryIndex := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[binaryIndex]? = some binaryBody := by rfl
  have setup : enterFrame binaryBody (binaryArguments left right output) memory = .ok (frame, memory) := by rfl
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨fuel, final, certificate, value, authority, outside⟩ := vector_initialized memory left right output call
  have fetched : binaryBody.code[5]? = some (.call vectorIndex 3) := by rfl
  have returned : binaryBody.code[6]? = some .ret := by rfl
  have returns : binaryBody.returnsValue = false := by rfl
  have stepped : step binaryBody (.call vectorIndex 3) 5 (binaryArguments left right output) frame
      (binaryArguments left right output).reverse memory =
      .ok (.call vectorIndex (binaryArguments left right output) [] memory) := by
    simp [step, binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run Extracted.program 1 binaryIndex 6 (binaryArguments left right output) frame [] final =
      .ok (final, []) := by
    simp [run, found, returned, returns, step, leaveFrame, frame, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨fuel, certificate.1⟩ ⟨1, tail⟩
  have index : binaryIndex = binaryIndex := rfl
  conv at index => rhs; cbv
  simp only [index] at tail
  have finished : run Extracted.program (tailFuel + 5) binaryIndex 0
      (binaryArguments left right output) frame [] memory = .ok (final, []) := by
    conv in binaryIndex => cbv
    iterate 5
      apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, binaryArguments, checkedValue, formValue, numericValue, fl, fr, fo,
              pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate, CIL.truth,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩)
          done
    exact tail
  exact ⟨tailFuel + 5, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    value, authority, outside⟩

theorem vector_entry_checked : WrappingBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation)
    Extracted.program binaryIndex := vector_entry_initialized.to_wrapping

#print axioms vector_entry_initialized
#print axioms vector_entry_checked
end UInt256Proof.Bitwise.Safety
