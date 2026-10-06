import UInt256.Methods.Equality.ScalarOperatorSafety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem scalar_operator_checked {α : Type} (encode : α → CIL.Value)
    (equal : BitVec 256 → α → Bool) (numeric : ∀ right, numericValue (encode right) = true)
    (child : ReadOnlyScalarContract encode
      (fun left right => .i32 (if equal left right then 1 else 0)) Extracted.program operatorCallee) :
    ScalarOperatorContract operatorScalarFirst operatorNegate encode equal Extracted.program Extracted.entryIndex := by
  intro memory left right call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have setup : enterFrame Extracted.entryBody (scalarOperatorArguments operatorScalarFirst left (encode right)) memory =
      .ok (frame, memory) := by
    simp [enterFrame, cil_code, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have lookup : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have formed := call.input_formed (reference := left) (by simp)
  have checked : (scalarOperatorArguments operatorScalarFirst left (encode right)).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments operatorScalarFirst left (encode right)) := by
    cases order : operatorScalarFirst <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, childFinal, certificate, cells⟩ := child memory left right call
  have fetched : Extracted.entryBody.code[operatorCall]? = some (.call operatorCallee 2) := by rfl
  have stepped : step Extracted.entryBody (.call operatorCallee 2) operatorCall
      (scalarOperatorArguments operatorScalarFirst left (encode right)) frame
      [.scalar (encode right), .reference (.address left)] memory =
      .ok (.call operatorCallee (scalarArguments left (encode right)) [] memory) := by
    simp [step, scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, certificate.1⟩ ⟨3, scalar_operator_return _ _ frame childFinal⟩
  let post : Memory → List Value → Prop := fun result values =>
    result = leaveFrame frame childFinal ∧ values = [.scalar (.i32
      (if equal (inputValue memory left) right != operatorNegate then 1 else 0))]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    scalar_operator_prefix memory left (encode right) frame (numeric right) call post
      ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  simpa only [leaveFrame, frame, List.foldl_nil] using cells

#print axioms scalar_operator_checked

end UInt256Proof.Equality.Safety
