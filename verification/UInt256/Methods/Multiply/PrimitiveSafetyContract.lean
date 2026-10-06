import UInt256.Methods.Multiply.InitializedSafety
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.ReadOnlyForwarder
import CIL.Safety.NumericLocalLoad
import CIL.Safety.ReturnMemory
import UInt256.Methods.Multiply.WordConversionSafety
import UInt256.Safety.PrivateAggregateStore
import UInt256.Safety.ReadOnlyCall
import Extracted
import UInt256.Safety.ConstructorSetup
import CIL.Safety.NumericHomes

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

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem primitive_body (wordContract : WordContract) (top : FullTopContract)
    (firstScalar : Bool) (memory : Memory) (input operand output : Reference)
    (argument : CIL.Value) (word : BitVec 64) (frame : Frame) (watermark : Nat)
    (numeric : numericValue argument = true) (prefixProof : ConversionPrefix argument word)
    (slots : frame.locals = [.bytes .vector256 operand, .bytes .vector256 output])
    (call : CallingConditions Extracted.program memory [input] [output])
    (writable : access memory operand 32 1 true = .ok ())
    (older : input.allocation < operand.allocation)
    (privateOperand : watermark ≤ operand.allocation) (ordered : operand.allocation < output.allocation)
    (owned : ∀ id ∈ frame.owned, watermark ≤ id)
    (code0 : Extracted.entryBody.code[0]? = some (.arg (if firstScalar then 0 else 1)))
    (code3 : Extracted.entryBody.code[3]? = some (if firstScalar then .aggregateLocalAddr 0 else .arg 0))
    (code4 : Extracted.entryBody.code[4]? = some (if firstScalar then .arg 1 else .aggregateLocalAddr 0)) :
    ∃ fuel final,
      run Extracted.program fuel Extracted.entryIndex 0
        (scalarOperatorArguments firstScalar input argument) frame [] memory =
        .ok (final, [.scalar (.v256 (inputValue memory input * BitVec.ofNat 256 word.toNat))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  have conversionCall : CallingConditions Extracted.program memory [] [] :=
    ⟨⟨call.1.1, by simp, by simp⟩, call.2⟩
  obtain ⟨conversionFuel, converted, invoked, _, authority, preserved⟩ :=
    conversion_invoke memory argument word numeric prefixProof conversionCall
  have convertedCall := call.after_readonly_call invoked authority preserved
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  have operandBound : operand.allocation < memory.nextIdentity := (call.1.1.1 _ _ present).1
  have convertedWritable := authority.access writable operandBound
  obtain ⟨prepared, stored, preparedCall, operandValue, inputsSame, storedBelow⟩ :=
    convertedCall.store_private_aggregate operand (BitVec.ofNat 256 word.toNat) convertedWritable
      (by simpa using older)
  have outputPrivate : watermark ≤ output.allocation := Nat.le_trans privateOperand (Nat.le_of_lt ordered)
  have preparedBound : watermark ≤ prepared.nextIdentity := by
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (preparedCall.input_formed (reference := operand) (by simp))
    exact Nat.le_trans privateOperand (Nat.le_of_lt (preparedCall.1.1.1 _ _ present).1)
  obtain ⟨tailFuel, final, tail, outside⟩ := primitive_multiply_finish wordContract top firstScalar
    prepared input operand output argument frame watermark slots preparedCall outputPrivate preparedBound owned code3 code4
  have inputSame := inputsSame input (by simp)
  have initialValue := call.input_value_of_caller_eq preserved input (by simp)
  rw [inputSame, operandValue, initialValue] at tail
  let value := inputValue memory input * BitVec.ofNat 256 word.toNat
  let post : Memory → List Value → Prop := fun result returned => result = final ∧ returned = [.scalar (.v256 value)]
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by rfl
  have storeStep : step Extracted.entryBody (.setAggregateLocal 0) 2
      (scalarOperatorArguments firstScalar input argument) frame [.scalar (.v256 (BitVec.ofNat 256 word.toNat))]
      converted = .ok (.next 3 [] frame prepared) := by
    simp only [step, slots, List.getElem?_cons_zero, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases frame
    simp_all
  have afterConversion := run_next_exists post found (by rfl) storeStep ⟨tailFuel, final, _, tail, rfl, rfl⟩
  obtain ⟨afterFuel, after, values, afterRun, afterEq, valuesEq⟩ := afterConversion
  change after = final at afterEq
  subst after
  change values = [.scalar (.v256 value)] at valuesEq
  subst values
  have callStep : step Extracted.entryBody (.call conversionIndex 1) 1
      (scalarOperatorArguments firstScalar input argument) frame [.scalar argument] memory =
      .ok (.call conversionIndex [.scalar argument] [] memory) := by
    simp [step, checkedValue, numeric, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨callFuel, called⟩ := run_call_exists found (by rfl) callStep ⟨conversionFuel, invoked⟩ ⟨afterFuel, afterRun⟩
  have started : ∃ fuel result returned,
      run Extracted.program fuel Extracted.entryIndex 0 (scalarOperatorArguments firstScalar input argument)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
    apply run_next_exists post found code0
    · cases firstScalar <;> simp [step, scalarOperatorArguments, scalarArguments, checkedValue, numeric,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨callFuel, final, _, called, rfl, rfl⟩
  obtain ⟨fuel, result, returned, ran, resultEq, returnedEq⟩ := started
  change result = final at resultEq
  subst result
  change returned = [.scalar (.v256 value)] at returnedEq
  subst returned
  refine ⟨fuel, final, ran, ?_⟩
  intro id old offset
  have beforeOperand := Nat.lt_of_lt_of_le old privateOperand
  exact (outside id old offset).trans
    ((storedBelow.cells id beforeOperand offset).trans
      (preserved id (Nat.lt_trans beforeOperand operandBound) offset))

#print axioms primitive_body
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def primitiveSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.vector256, .v256 0, 0, by rfl⟩]

theorem primitive_frame_setup (memory : Memory) (input : Reference) (args : List Value)
    (call : CallingConditions Extracted.program memory [input] []) :
    ∃ frame entered operand output,
      enterFrame Extracted.entryBody args memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 operand, .bytes .vector256 output] ∧
      memory.nextIdentity ≤ operand.allocation ∧ operand.allocation < output.allocation ∧
      access entered operand 32 1 true = .ok () ∧
      CallingConditions Extracted.program entered [input] [output] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity primitiveSpecs call.1.1
  cases homes with
  | cons operand spec fresh loaded writable tail =>
    cases tail with
    | cons output spec2 later loaded2 writable2 tail2 =>
      cases tail2
      let frame : Frame := ⟨memory.nextIdentity,
        [.bytes .vector256 operand, .bytes .vector256 output], owned, []⟩
      have kinds : Extracted.entryBody.localKinds = numericKinds primitiveSpecs := by rfl
      have values : Extracted.entryBody.locals = numericInitializers primitiveSpecs := by rfl
      have arguments : Extracted.entryBody.aggregateArgs = [] := by rfl
      have setup : enterFrame Extracted.entryBody args memory = .ok (frame, entered) := by
        simp [enterFrame, kinds, values, arguments, made, makeArgumentHomes, frame,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨frame, entered, operand, output, setup, rfl, fresh, later, writable,
        (call.after_frame_setup setup).with_writable_output writable2,
        enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms primitive_frame_setup
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def primitiveScalarFirst : Bool := match Extracted.entryBody.code[0]? with
  | some (CIL.Op.arg 0) => true
  | _ => false

theorem primitive_checked (wordContract : WordContract) (top : FullTopContract)
    (firstScalar : Bool) (memory : Memory) (input : Reference)
    (argument : CIL.Value) (word : BitVec 64)
    (numeric : numericValue argument = true) (prefixProof : ConversionPrefix argument word)
    (code0 : Extracted.entryBody.code[0]? = some (.arg (if firstScalar then 0 else 1)))
    (code3 : Extracted.entryBody.code[3]? = some (if firstScalar then .aggregateLocalAddr 0 else .arg 0))
    (code4 : Extracted.entryBody.code[4]? = some (if firstScalar then .arg 1 else .aggregateLocalAddr 0))
    (call : CallingConditions Extracted.program memory [input] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program Extracted.entryIndex
        (scalarOperatorArguments firstScalar input argument) memory fuel final
        [.scalar (.v256 (inputValue memory input * BitVec.ofNat 256 word.toNat))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, operand, output, setup, slots, privateOperand, ordered, writable, enteredCall, before⟩ :=
    primitive_frame_setup memory input (scalarOperatorArguments firstScalar input argument) call
  have lookup : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by rfl
  have formed := call.input_formed (reference := input) (by simp)
  have checked : (scalarOperatorArguments firstScalar input argument).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments firstScalar input argument) := by
    cases firstScalar <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨allocation, present, _⟩ := formed_reference_live _ _ _ formed
  have bound := (call.1.1.1 _ _ present).1
  have older := Nat.lt_of_lt_of_le bound privateOperand
  obtain ⟨fuel, final, finished, cells⟩ := primitive_body wordContract top firstScalar
    entered input operand output argument word frame memory.nextIdentity numeric prefixProof slots
    enteredCall writable older privateOperand ordered (fun id member => (fresh.2 id member).1) code0 code3 code4
  have sameInput : inputValue entered input = inputValue memory input := by
    simp only [inputValue, before.cells _ bound]
  rw [sameInput] at finished
  refine ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  intro id old offset
  exact (cells id old offset).trans (before.cells id old offset)

#print axioms primitive_checked
end UInt256Proof.Multiply.Safety
