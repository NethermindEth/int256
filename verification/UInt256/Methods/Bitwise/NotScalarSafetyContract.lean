import UInt256.Methods.Bitwise.ScalarSafetyConstruct
import UInt256.Methods.Bitwise.Lemmas
import UInt256.Safety.UnaryOutput
import UInt256.Safety.LimbAccess

namespace UInt256Proof.Bitwise.ScalarSafety
open CIL.Safety UInt256Model.Safety

theorem packed_not (memory : Memory) (input : Reference) :
    packed (~~~inputLimb memory input 0) (~~~inputLimb memory input 1)
      (~~~inputLimb memory input 2) (~~~inputLimb memory input 3) = ~~~inputValue memory input := by
  have same : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  exact (value_not (inputLimb memory input)).trans (by rw [same])

theorem not_initialized : InitializedUnaryContract (fun input => ~~~input)
    Extracted.program scalarIndex := by
  intro memory input output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have setup : enterFrame scalarBody (unaryArguments input output) memory = .ok (frame, memory) := by rfl
  have fl := call.input_formed (reference := input) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := input) (by simp) index rest
  have checked : (unaryArguments input output).mapM (checkedValue memory) = .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, fl, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  let word := fun index => ~~~inputLimb memory input index
  obtain ⟨fuel, final, tail, readback, writable, outside⟩ :=
    construct_result memory [input] output (unaryArguments input output)
      (word 0) (word 1) (word 2) (word 3) call
  have arithmetic := packed_not memory input
  change packed (word 0) (word 1) (word 2) (word 3) = _ at arithmetic
  rw [arithmetic] at readback
  have index : scalarIndex = scalarIndex := rfl
  conv at index => rhs; cbv
  have pc : constructPC = 19 := by rfl
  simp only [index, pc, words, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, word] at tail
  have finished : run Extracted.program (fuel + 15) scalarIndex 0 (unaryArguments input output) frame [] memory =
      .ok (final, []) := by
    conv in scalarIndex => cbv
    iterate 15
      apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [step, unaryArguments, checkedValue, numericValue, formValue, fl, fo, hl,
              pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate, CIL.truth,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, cil_code]
          try (exact ⟨rfl, rfl, rfl, rfl⟩)
          done
    exact tail
  exact ⟨fuel + 15, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    readback, writable, outside⟩

#print axioms packed_not
#print axioms not_initialized
end UInt256Proof.Bitwise.ScalarSafety
