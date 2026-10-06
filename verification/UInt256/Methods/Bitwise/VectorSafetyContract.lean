import Extracted
import UInt256.Safety.Contract
import UInt256.Methods.Bitwise.Contract
import UInt256.Safety.OutputValue
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import UInt256.Safety.CallerSetup
import UInt256.Safety.InitializedOutput

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
            CIL.step, CIL.Intrinsic.available, intrinsic, intrinsic_and, intrinsic_or, written, result, selected, UInt256Model.Bitwise.applyBinary,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_run
end UInt256Proof.Bitwise.Safety

namespace UInt256Proof.Bitwise.Safety
open CIL.Safety UInt256Model.Safety


theorem vector_initialized : InitializedBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation) Extracted.program vectorIndex := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have kinds : vectorBody.localKinds = [] := by rfl
  have values : vectorBody.locals = [] := by rfl
  have arguments : vectorBody.aggregateArgs = [] := by rfl
  have setup : enterFrame vectorBody (binaryArguments left right output) memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, values, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
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
end UInt256Proof.Bitwise.Safety
