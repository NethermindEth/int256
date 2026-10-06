import UInt256.Methods.Bitwise.ScalarSafetyConstruct
import UInt256.Methods.Bitwise.Lemmas
import UInt256.Methods.Bitwise.Contract
import UInt256.Safety.LimbAccess

namespace UInt256Proof.Bitwise.ScalarSafety
open CIL.Safety UInt256Model.Safety

def scalarOperation : UInt256Model.Bitwise.Binary :=
  if scalarBody.code.any (fun op => match op with | .band => true | _ => false) then .and
  else if scalarBody.code.any (fun op => match op with | .bor => true | _ => false) then .or else .xor

def applyWord (operation : UInt256Model.Bitwise.Binary) (left right : BitVec 64) : BitVec 64 :=
  match operation with | .and => left &&& right | .or => left ||| right | .xor => left ^^^ right

theorem packed_operation (operation : UInt256Model.Bitwise.Binary) (memory : Memory) (left right : Reference) :
    packed (applyWord operation (inputLimb memory left 0) (inputLimb memory right 0))
      (applyWord operation (inputLimb memory left 1) (inputLimb memory right 1))
      (applyWord operation (inputLimb memory left 2) (inputLimb memory right 2))
      (applyWord operation (inputLimb memory left 3) (inputLimb memory right 3)) =
      UInt256Model.Bitwise.applyBinary operation (inputValue memory left) (inputValue memory right) := by
  have input (reference : Reference) : UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
    UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset
  cases operation with
  | and => exact (value_and (inputLimb memory left) (inputLimb memory right)).trans (by simp only [input, UInt256Model.Bitwise.applyBinary])
  | or => exact (value_or (inputLimb memory left) (inputLimb memory right)).trans (by simp only [input, UInt256Model.Bitwise.applyBinary])
  | xor => exact (value_xor (inputLimb memory left) (inputLimb memory right)).trans (by simp only [input, UInt256Model.Bitwise.applyBinary])

theorem scalar_initialized : InitializedBinaryContract (UInt256Model.Bitwise.applyBinary scalarOperation)
    Extracted.program scalarIndex := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have setup : enterFrame scalarBody (binaryArguments left right output) memory = .ok (frame, memory) := by rfl
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have checked : (binaryArguments left right output).mapM (checkedValue memory) = .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  let word := fun index => applyWord scalarOperation (inputLimb memory left index) (inputLimb memory right index)
  obtain ⟨fuel, final, tail, readback, writable, outside⟩ :=
    construct_result memory [left, right] output (binaryArguments left right output)
      (word 0) (word 1) (word 2) (word 3) call
  have arithmetic := packed_operation scalarOperation memory left right
  change packed (word 0) (word 1) (word 2) (word 3) = _ at arithmetic
  rw [arithmetic] at readback
  have selected : scalarOperation = scalarOperation := rfl
  conv at selected => rhs; cbv
  have index : scalarIndex = scalarIndex := rfl
  conv at index => rhs; cbv
  have pc : constructPC = 28 := by rfl
  simp only [index, pc, words, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, word, selected, applyWord] at tail
  have finished : run Extracted.program (fuel + 23) scalarIndex 0 (binaryArguments left right output) frame [] memory =
      .ok (final, []) := by
    conv in scalarIndex => cbv
    iterate 23
      apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo, hl, hr,
              pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.FeatureProfile.evaluate, CIL.truth,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, cil_code]
          try (exact ⟨rfl, rfl, rfl, rfl⟩)
          done
    exact tail
  exact ⟨fuel + 23, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    readback, writable, outside⟩

theorem scalar_checked : WrappingBinaryContract (UInt256Model.Bitwise.applyBinary scalarOperation)
    Extracted.program scalarIndex := scalar_initialized.to_wrapping

#print axioms packed_operation
#print axioms scalar_initialized
#print axioms scalar_checked
end UInt256Proof.Bitwise.ScalarSafety
