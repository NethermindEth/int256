import UInt256.Methods.Bitwise.NotVectorSafetyContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Bitwise.NotSafety
open CIL.Safety UInt256Model.Safety

def unaryIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .call callee 2 => callee == vectorIndex | _ => false

def unaryBody : CIL.Method := Extracted.program[unaryIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem vector_entry_initialized : InitializedUnaryContract (fun input => ~~~input)
    Extracted.program unaryIndex := by
  intro memory input output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[unaryIndex]? = some unaryBody := by rfl
  have kinds : unaryBody.localKinds = [] := by rfl
  have values : unaryBody.locals = [] := by rfl
  have arguments : unaryBody.aggregateArgs = [] := by rfl
  have setup : enterFrame unaryBody (unaryArguments input output) memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, values, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fl := call.input_formed (reference := input) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have checked : (unaryArguments input output).mapM (checkedValue memory) =
      .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, fl, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨fuel, final, certificate, value, authority, outside⟩ := vector_initialized memory input output call
  have fetched : unaryBody.code[4]? = some (.call vectorIndex 2) := by rfl
  have returned : unaryBody.code[5]? = some .ret := by rfl
  have returns : unaryBody.returnsValue = false := by rfl
  have stepped : step unaryBody (.call vectorIndex 2) 4 (unaryArguments input output) frame
      (unaryArguments input output).reverse memory =
      .ok (.call vectorIndex (unaryArguments input output) [] memory) := by
    simp [step, unaryArguments, checkedValue, formValue, fl, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run Extracted.program 1 unaryIndex 5 (unaryArguments input output) frame [] final =
      .ok (final, []) := by
    simp [run, found, returned, returns, step, leaveFrame, frame, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨fuel, certificate.1⟩ ⟨1, tail⟩
  have index : unaryIndex = unaryIndex := rfl
  conv at index => rhs; cbv
  simp only [index] at tail
  have finished : run Extracted.program (tailFuel + 4) unaryIndex 0
      (unaryArguments input output) frame [] memory = .ok (final, []) := by
    conv in unaryIndex => cbv
    iterate 4
      apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, unaryArguments, checkedValue, formValue, numericValue, fl, fo,
              pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, CIL.truth,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩)
          done
    exact tail
  exact ⟨tailFuel + 4, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    value, authority, outside⟩

#print axioms vector_entry_initialized
end UInt256Proof.Bitwise.NotSafety
