import UInt256.Methods.Multiply.InitializedSafety
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.ReadOnlyForwarder
import CIL.Safety.NumericLocalLoad
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem primitive_multiply_finish (word : WordContract) (top : FullTopContract) (firstScalar : Bool)
    (memory : Memory) (input operand output : Reference) (argument : CIL.Value)
    (frame : Frame) (watermark : Nat)
    (slots : frame.locals = [.bytes .vector256 operand, .bytes .vector256 output])
    (call : CallingConditions Extracted.program memory [input, operand] [output])
    (privateOutput : watermark ≤ output.allocation) (bound : watermark ≤ memory.nextIdentity)
    (owned : ∀ id ∈ frame.owned, watermark ≤ id)
    (code3 : Extracted.entryBody.code[3]? = some (if firstScalar then .aggregateLocalAddr 0 else .arg 0))
    (code4 : Extracted.entryBody.code[4]? = some (if firstScalar then .arg 1 else .aggregateLocalAddr 0)) :
    ∃ fuel final,
      run Extracted.program fuel Extracted.entryIndex 3
        (scalarOperatorArguments firstScalar input argument) frame [] memory =
        .ok (final, [.scalar (.v256 (inputValue memory input * inputValue memory operand))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  let left := if firstScalar then operand else input
  let right := if firstScalar then input else operand
  have childCall : CallingConditions Extracted.program memory [left, right] [output] := by
    cases firstScalar
    · exact call
    · exact call.swap_binary_inputs
  obtain ⟨childFuel, result, certificate, loaded, _, outside⟩ :=
    multiply_initialized_contract word top memory left right output childCall
  let value := inputValue memory input * inputValue memory operand
  have resultRead : read result output 32 1 = .ok (numberBytes value.toNat 32) := by
    cases firstScalar
    · exact loaded
    · simpa only [left, right, ite_true, value, BitVec.mul_comm] using loaded
  have localRead := load_numeric_local .vector256 (.v256 value) value.toNat rfl resultRead
  have outputSlot : frame.locals[1]? = some (.bytes .vector256 output) := by simp [slots]
  have operandSlot : frame.locals[0]? = some (.bytes .vector256 operand) := by simp [slots]
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by rfl
  have tail : run Extracted.program 2 Extracted.entryIndex 7
      (scalarOperatorArguments firstScalar input argument) frame [] result =
      .ok (leaveFrame frame result, [.scalar (.v256 value)]) := by
    apply Eq.trans
    · apply run_next found (by rfl)
      simp [step, outputSlot, localRead, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [run, cil_code, step, checkedValue, numericValue, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fi := call.input_formed (reference := input) (by simp)
  have fa := call.input_formed (reference := operand) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have stepped : step Extracted.entryBody (.call multiplyIndex 3) 6
      (scalarOperatorArguments firstScalar input argument) frame
      (binaryArguments left right output).reverse memory =
      .ok (.call multiplyIndex (binaryArguments left right output) [] memory) := by
    cases firstScalar <;> simp [step, binaryArguments, left, right, checkedValue, formValue,
      fi, fa, fo, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, called⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certificate.1⟩ ⟨2, tail⟩
  let post : Memory → List Value → Prop := fun final returned => final = leaveFrame frame result ∧ returned = [.scalar (.v256 value)]
  have prefixRun : ∃ fuel final returned,
      run Extracted.program fuel Extracted.entryIndex 3 (scalarOperatorArguments firstScalar input argument)
        frame [] memory = .ok (final, returned) ∧ post final returned := by
    cases firstScalar <;> dsimp [left, right] at code3 code4 called ⊢
    all_goals
      apply run_next_exists post found code3
      · simp [step, scalarOperatorArguments, scalarArguments, localAddress, operandSlot, checkedValue,
          formValue, fi, fa, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      apply run_next_exists post found code4
      · simp [step, scalarOperatorArguments, scalarArguments, localAddress, operandSlot, checkedValue,
          formValue, fi, fa, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      apply run_next_exists post found (by rfl)
      · simp [step, localAddress, outputSlot, formValue, fo, checkedAt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨tailFuel, _, _, called, rfl, rfl⟩
  obtain ⟨fuel, final, returned, ran, rfl, rfl⟩ := prefixRun
  have retained := leaveFrame_preserves_memory_below frame result watermark owned
  refine ⟨fuel, _, ran, ?_⟩
  intro id old offset
  exact (retained.cells id old offset).trans
    (outside id (Nat.lt_of_lt_of_le old bound) offset (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le old privateOutput))))

#print axioms primitive_multiply_finish
end UInt256Proof.Multiply.Safety
