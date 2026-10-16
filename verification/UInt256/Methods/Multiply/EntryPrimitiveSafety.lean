import UInt256.Methods.Multiply.EntryPrimitiveSetup
import UInt256.Safety.ReadOnlyCall
import UInt256.Safety.PrivateAggregateStore
import UInt256.Safety.OrderedScalarContract

namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety

theorem primitive_multiply_finish (ctx : PrimitiveContext) (word : Calls.WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) (firstScalar : Bool)
    (memory : Memory) (input operand output : Reference) (argument : CIL.Value)
    (frame : Frame) (watermark : Nat)
    (slots : frame.locals = [.bytes (.aggregate 32) operand, .bytes (.aggregate 32) output])
    (call : CallingConditions ctx.program memory [input, operand] [output])
    (privateOutput : watermark ≤ output.allocation) (bound : watermark ≤ memory.nextIdentity)
    (owned : ∀ id ∈ frame.owned, watermark ≤ id)
    (code3 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[3]? = some (if firstScalar then .localAddr 0 else .arg 0))
    (code4 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[4]? = some (if firstScalar then .arg 1 else .localAddr 0)) :
    ∃ fuel final,
      run ctx.program fuel ctx.wrapperIndex 3
        (scalarOperatorArguments firstScalar input argument) frame [] memory =
        .ok (final, [.scalar (encoded (inputValue memory input * inputValue memory operand))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  let left := if firstScalar then operand else input
  let right := if firstScalar then input else operand
  have childCall : CallingConditions ctx.program memory [left, right] [output] := by
    cases firstScalar
    · exact call
    · refine ⟨⟨call.1.1, ?_, call.1.2.2⟩, call.2⟩
      intro view member
      apply call.1.2.1 view
      simpa [left, right, or_comm] using member
  obtain ⟨childFuel, result, certificate, loaded, _, outside⟩ :=
    initialized_result ctx.toContext word top memory left right output childCall
  let value := inputValue memory input * inputValue memory operand
  have resultRead : read result output 32 1 = .ok (numberBytes value.toNat 32) := by
    cases firstScalar
    · exact loaded
    · simpa only [left, right, ite_true, value, BitVec.mul_comm] using loaded

  have outputSlot : frame.locals[1]? = some (.bytes (.aggregate 32) output) := by simp [slots]
  have operandSlot : frame.locals[0]? = some (.bytes (.aggregate 32) operand) := by simp [slots]
  have found : ctx.program[ctx.wrapperIndex]? = some (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) := ctx.wrapper
  have tail : run ctx.program 2 ctx.wrapperIndex 7
      (scalarOperatorArguments firstScalar input argument) frame [] result =
      .ok (leaveFrame frame result, [.scalar (encoded value)]) := by
    apply Eq.trans
    · apply run_next found (by rfl)
      exact step_load_aggregate (size := 32) (reference := output) outputSlot resultRead
    · simp [run, found, primitiveBody, step, checkedValue, numericValue, encoded,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fi := call.input_formed (reference := input) (by simp)
  have fa := call.input_formed (reference := operand) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have stepped : step (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) (.call ctx.indices.entry 3) 6
      (scalarOperatorArguments firstScalar input argument) frame
      (binaryArguments left right output).reverse memory =
      .ok (.call ctx.indices.entry (binaryArguments left right output) [] memory) := by
    cases firstScalar <;> simp [step, binaryArguments, left, right, checkedValue, formValue,
      fi, fa, fo, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, called⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certificate.1⟩ ⟨2, tail⟩
  let post : Memory → List Value → Prop := fun final returned => final = leaveFrame frame result ∧ returned = [.scalar (encoded value)]
  have prefixRun : ∃ fuel final returned,
      run ctx.program fuel ctx.wrapperIndex 3 (scalarOperatorArguments firstScalar input argument)
        frame [] memory = .ok (final, returned) ∧ post final returned := by
    cases firstScalar <;> dsimp [left, right] at code3 code4 called ⊢
    all_goals
      apply run_next_exists post found code3
      · simp [step, scalarOperatorArguments, scalarArguments, localAddress, operandSlot, checkedValue,
          formValue, fi, fa, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      apply run_next_exists post found code4
      · simp [step, scalarOperatorArguments, localAddress, operandSlot, checkedValue,
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
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety

theorem primitive_body (ctx : PrimitiveContext) (wordContract : Calls.WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage)
    (firstScalar : Bool) (memory : Memory) (input operand output : Reference)
    (argument : CIL.Value) (word : BitVec 64) (frame : Frame) (watermark : Nat)
    (numeric : numericValue argument = true) (prefixProof : ConversionPrefix ctx argument word)
    (slots : frame.locals = [.bytes (.aggregate 32) operand, .bytes (.aggregate 32) output])
    (call : CallingConditions ctx.program memory [input] [output])
    (writable : access memory operand 32 1 true = .ok ())
    (older : input.allocation < operand.allocation)
    (privateOperand : watermark ≤ operand.allocation) (ordered : operand.allocation < output.allocation)
    (owned : ∀ id ∈ frame.owned, watermark ≤ id)
    (code0 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[0]? = some (.arg (if firstScalar then 0 else 1)))
    (code3 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[3]? = some (if firstScalar then .localAddr 0 else .arg 0))
    (code4 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[4]? = some (if firstScalar then .arg 1 else .localAddr 0)) :
    ∃ fuel final,
      run ctx.program fuel ctx.wrapperIndex 0
        (scalarOperatorArguments firstScalar input argument) frame [] memory =
        .ok (final, [.scalar (encoded (inputValue memory input * BitVec.ofNat 256 word.toNat))]) ∧
      ∀ id, id < watermark → ∀ offset, final.cells id offset = memory.cells id offset := by
  have conversionCall : CallingConditions ctx.program memory [] [] :=
    ⟨⟨call.1.1, by simp, by simp⟩, call.2⟩
  obtain ⟨conversionFuel, converted, invoked, _, authority, preserved⟩ :=
    conversion_invoke ctx memory argument word numeric prefixProof conversionCall
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
  obtain ⟨tailFuel, final, tail, outside⟩ := primitive_multiply_finish ctx wordContract top firstScalar
    prepared input operand output argument frame watermark slots preparedCall outputPrivate preparedBound owned code3 code4
  have inputSame := inputsSame input (by simp)
  have initialValue := call.input_value_of_caller_eq preserved input (by simp)
  rw [inputSame, operandValue, initialValue] at tail
  let value := inputValue memory input * BitVec.ofNat 256 word.toNat
  let post : Memory → List Value → Prop := fun result returned => result = final ∧ returned = [.scalar (encoded value)]
  have found : ctx.program[ctx.wrapperIndex]? = some (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) := ctx.wrapper
  have storeStep : step (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) (.setLocal 0) 2
      (scalarOperatorArguments firstScalar input argument) frame [.scalar (encoded (BitVec.ofNat 256 word.toNat))]
      converted = .ok (.next 3 [] frame prepared) := by
    simp only [step, slots, List.getElem?_cons_zero, encoded, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases frame
    simp_all
  have afterConversion := run_next_exists post found (by rfl) storeStep ⟨tailFuel, final, _, tail, rfl, rfl⟩
  obtain ⟨afterFuel, after, values, afterRun, afterEq, valuesEq⟩ := afterConversion
  change after = final at afterEq
  subst after
  change values = [.scalar (encoded value)] at valuesEq
  subst values
  have callStep : step (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) (.call ctx.conversionIndex 1) 1
      (scalarOperatorArguments firstScalar input argument) frame [.scalar argument] memory =
      .ok (.call ctx.conversionIndex [.scalar argument] [] memory) := by
    simp [step, checkedValue, numeric, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨callFuel, called⟩ := run_call_exists found (by rfl) callStep ⟨conversionFuel, invoked⟩ ⟨afterFuel, afterRun⟩
  have started : ∃ fuel result returned,
      run ctx.program fuel ctx.wrapperIndex 0 (scalarOperatorArguments firstScalar input argument)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
    apply run_next_exists post found code0
    · cases firstScalar <;> simp [step, scalarOperatorArguments, scalarArguments, checkedValue, numeric,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨callFuel, final, _, called, rfl, rfl⟩
  obtain ⟨fuel, result, returned, ran, resultEq, returnedEq⟩ := started
  change result = final at resultEq
  subst result
  change returned = [.scalar (encoded value)] at returnedEq
  subst returned
  refine ⟨fuel, final, ran, ?_⟩
  intro id old offset
  have beforeOperand := Nat.lt_of_lt_of_le old privateOperand
  exact (outside id old offset).trans
    ((storedBelow.cells id beforeOperand offset).trans
      (preserved id (Nat.lt_trans beforeOperand operandBound) offset))

#print axioms primitive_body
end UInt256Proof.Multiply.Entry
namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety

theorem primitive_frame_setup (ctx : PrimitiveContext) (memory : Memory) (input : Reference) (args : List Value)
    (call : CallingConditions ctx.program memory [input] []) :
    ∃ frame entered operand output,
      enterFrame (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) args memory = .ok (frame, entered) ∧
      frame.locals = [.bytes (.aggregate 32) operand, .bytes (.aggregate 32) output] ∧
      memory.nextIdentity ≤ operand.allocation ∧ operand.allocation < output.allocation ∧
      access entered operand 32 1 true = .ok () ∧
      CallingConditions ctx.program entered [input] [output] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨operand, allocated, middle, home, stored, _, writable, _, fresh⟩ :=
    allocate_initialized_aggregate memory memory.nextIdentity (32 : Fin (2^64))
      (List.replicate 32 0) (by decide) call.1.1
  have made : makeLocal memory.nextIdentity (.aggregate 32) (.aggregate (List.replicate 32 0)) memory =
      .ok (.bytes (.aggregate 32) operand, [operand.allocation], middle) := by
    simp only [makeLocal, localWidth, localAlignment, home, stored, reduceCtorEq, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have wf := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ call.1.1 made
  obtain ⟨output, allocated2, entered, home2, stored2, _, writable2, before2, fresh2⟩ :=
    allocate_initialized_aggregate middle memory.nextIdentity (32 : Fin (2^64))
      (List.replicate 32 0) (by decide) wf
  have made2 : makeLocal memory.nextIdentity (.aggregate 32) (.aggregate (List.replicate 32 0)) middle =
      .ok (.bytes (.aggregate 32) output, [output.allocation], entered) := by
    simp only [makeLocal, localWidth, localAlignment, home2, stored2, reduceCtorEq, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  let frame : Frame := ⟨memory.nextIdentity,
    [.bytes (.aggregate 32) operand, .bytes (.aggregate 32) output], [operand.allocation, output.allocation], []⟩
  have setup : enterFrame (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) args memory =
      .ok (frame, entered) := by
    simp only [enterFrame, primitiveBody, makeLocals, made, made2, makeArgumentHomes, makeParameterHomes,
      frame, Bind.bind, Except.bind, Pure.pure, Except.pure, List.map_nil, List.append_nil, List.cons_append, List.nil_append]
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  have bound := (wf.1 _ _ present).1
  exact ⟨frame, entered, operand, output, setup, rfl, Nat.le_of_eq fresh.symm,
    by simpa only [fresh2] using bound,
    (before2.access operand bound 32 1 true).trans writable,
    (call.after_frame_setup setup).with_writable_output writable2,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩
#print axioms primitive_frame_setup
end UInt256Proof.Multiply.Entry
namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety
theorem primitive_checked (ctx : PrimitiveContext) (wordContract : Calls.WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage)
    (firstScalar : Bool) (memory : Memory) (input : Reference)
    (argument : CIL.Value) (word : BitVec 64)
    (numeric : numericValue argument = true) (prefixProof : ConversionPrefix ctx argument word)
    (code0 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[0]? = some (.arg (if firstScalar then 0 else 1)))
    (code3 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[3]? = some (if firstScalar then .localAddr 0 else .arg 0))
    (code4 : (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex).code[4]? = some (if firstScalar then .arg 1 else .localAddr 0))
    (call : CallingConditions ctx.program memory [input] []) :
    ∃ fuel final,
      InvocationCertificate ctx.program ctx.wrapperIndex
        (scalarOperatorArguments firstScalar input argument) memory fuel final
        [.scalar (encoded (inputValue memory input * BitVec.ofNat 256 word.toNat))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, operand, output, setup, slots, privateOperand, ordered, writable, enteredCall, before⟩ :=
    primitive_frame_setup ctx memory input (scalarOperatorArguments firstScalar input argument) call
  have lookup : ctx.program[ctx.wrapperIndex]? = some (primitiveBody ctx.profile ctx.firstScalar ctx.indices.entry ctx.conversionIndex) := ctx.wrapper
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
  obtain ⟨fuel, final, finished, cells⟩ := primitive_body ctx wordContract top firstScalar
    entered input operand output argument word frame memory.nextIdentity numeric prefixProof slots
    enteredCall writable older privateOperand ordered (fun id member => (fresh.2 id member).1) code0 code3 code4
  have sameInput : inputValue entered input = inputValue memory input := by
    simp only [inputValue, before.cells _ bound]
  rw [sameInput] at finished
  refine ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  intro id old offset
  exact (cells id old offset).trans (before.cells id old offset)

#print axioms primitive_checked
end UInt256Proof.Multiply.Entry


namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety

theorem conversion_prefix64 (ctx : PrimitiveContext) (narrow : ctx.narrow = false)
    (word : BitVec 64) : ConversionPrefix ctx (.i64 word) word := by
  intro memory frame post continuation
  have found := ctx.conversion
  simp only [narrow, Bool.false_eq_true, ↓reduceIte] at continuation
  iterate 7
    apply run_next_exists post found (by simp only [conversionBody, narrow]; rfl)
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation

theorem conversion_prefix32 (ctx : PrimitiveContext) (narrow : ctx.narrow = true)
    (word : BitVec 32) : ConversionPrefix ctx (.i32 word) (word.setWidth 64) := by
  intro memory frame post continuation
  have found := ctx.conversion
  simp only [narrow, ↓reduceIte] at continuation
  iterate 8
    apply run_next_exists post found (by simp only [conversionBody, narrow]; rfl)
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation

theorem primitive64_with_contracts (ctx : PrimitiveContext) (narrow : ctx.narrow = false)
    (wordContract : Calls.WordContract ctx.program ctx.indices.word)
    (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) :
    OrderedScalarContract ctx.firstScalar CIL.Value.i64
      (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) ctx.program ctx.wrapperIndex := by
  intro memory input word call
  exact primitive_checked ctx wordContract top
    ctx.firstScalar memory input (.i64 word) word rfl (conversion_prefix64 ctx narrow word)
    (by rfl) (by rfl) (by rfl) call

theorem primitive32_with_contracts (ctx : PrimitiveContext) (narrow : ctx.narrow = true)
    (wordContract : Calls.WordContract ctx.program ctx.indices.word)
    (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) :
    OrderedScalarContract ctx.firstScalar CIL.Value.i32
      (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) ctx.program ctx.wrapperIndex := by
  intro memory input word call
  have result := primitive_checked ctx wordContract top
    ctx.firstScalar memory input (.i32 word) (word.setWidth 64) rfl (conversion_prefix32 ctx narrow word)
    (by rfl) (by rfl) (by rfl) call
  simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans word.isLt (by decide : 2^32 < 2^64))] using result
theorem primitive64_correctness (ctx : PrimitiveContext) (narrow : ctx.narrow = false)
    (wordFound : ctx.program[ctx.indices.word]? = some (scalarWordBody ctx.profile))
    (bmi : ctx.profile.bmi2 = false) (arm : ctx.profile.armBase64 = false)
    (avx512 : ctx.profile.avx512DQVL = false) (avx2 : ctx.profile.avx2 = false) :
    OrderedScalarContract ctx.firstScalar CIL.Value.i64
      (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) ctx.program ctx.wrapperIndex :=
  primitive64_with_contracts ctx narrow (scalar_word_contract ctx.toContext wordFound bmi arm)
    (Full.scalar_top_contract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage ctx.full avx512 avx2)

theorem primitive32_correctness (ctx : PrimitiveContext) (narrow : ctx.narrow = true)
    (wordFound : ctx.program[ctx.indices.word]? = some (scalarWordBody ctx.profile))
    (bmi : ctx.profile.bmi2 = false) (arm : ctx.profile.armBase64 = false)
    (avx512 : ctx.profile.avx512DQVL = false) (avx2 : ctx.profile.avx2 = false) :
    OrderedScalarContract ctx.firstScalar CIL.Value.i32
      (fun input word => encoded (input * BitVec.ofNat 256 word.toNat)) ctx.program ctx.wrapperIndex :=
  primitive32_with_contracts ctx narrow (scalar_word_contract ctx.toContext wordFound bmi arm)
    (Full.scalar_top_contract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage ctx.full avx512 avx2)

#print axioms conversion_prefix64
#print axioms conversion_prefix32
#print axioms primitive64_correctness
#print axioms primitive32_correctness
end UInt256Proof.Multiply.Entry
