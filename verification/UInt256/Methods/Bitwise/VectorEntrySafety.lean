import UInt256.Methods.Bitwise.VectorSafetyContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Bitwise.Safety
open CIL.Safety UInt256Model.Safety

def binaryIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .call callee 3 => callee == vectorIndex | _ => false

def binaryBody : CIL.Method := Extracted.program[binaryIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem vector_entry_initialized : InitializedBinaryContract (UInt256Model.Bitwise.applyBinary vectorOperation)
    Extracted.program binaryIndex := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[binaryIndex]? = some binaryBody := by rfl
  have kinds : binaryBody.localKinds = [] := by rfl
  have values : binaryBody.locals = [] := by rfl
  have arguments : binaryBody.aggregateArgs = [] := by rfl
  have setup : enterFrame binaryBody (binaryArguments left right output) memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, values, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
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
              pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, CIL.truth,
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
