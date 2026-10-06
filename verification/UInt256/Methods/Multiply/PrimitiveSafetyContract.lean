import UInt256.Methods.Multiply.PrimitiveSafetyBody
import UInt256.Methods.Multiply.PrimitiveSafetySetup

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
