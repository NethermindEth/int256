import UInt256.Methods.Multiply.PrimitiveSafetyFinish
import UInt256.Methods.Multiply.WordConversionSafety
import UInt256.Safety.PrivateAggregateStore
import UInt256.Safety.ReadOnlyCall

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
