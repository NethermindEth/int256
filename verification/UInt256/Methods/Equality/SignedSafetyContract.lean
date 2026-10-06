import UInt256.Methods.Equality.SignedSafetyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem signed_checked (memory : Memory) (left : Reference) (argument : CIL.Value) (bits : BitVec 256)
    (negative : Bool) (numeric : numericValue argument = true)
    (child : SignedChild argument bits)
    (negativeExecution : negative = true → SignedNegative argument)
    (positiveExecution : negative = false → SignedPositive argument)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program signedIndex (scalarArguments left argument)
        memory fuel final [.scalar (.i32
          (if negative then 0 else if inputValue memory left = bits then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have setup : enterFrame signedBody (scalarArguments left argument) memory = .ok (frame, memory) := by
    conv in signedBody => cbv
    simp [enterFrame, cil_code, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have lookup : Extracted.program[signedIndex]? = some signedBody := by rfl
  have formed := call.input_formed (reference := left) (by simp)
  have checked : (scalarArguments left argument).mapM (checkedValue memory) =
      .ok (scalarArguments left argument) := by
    simp [scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  cases sign : negative
  · simp only [Bool.false_eq_true, ite_false]
    obtain ⟨childFuel, childFinal, certificate, cells⟩ :=
      child memory left call
    have fetched : signedBody.code[signedCall]? = some (.call signedCallee 2) := by rfl
    have stepped : step signedBody (.call signedCallee 2) signedCall
        (scalarArguments left argument) frame [.scalar argument, .reference (.address left)] memory =
        .ok (.call signedCallee (scalarArguments left argument) [] memory) := by
      simp [step, scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
      ⟨childFuel, certificate.1⟩ ⟨1, signed_return _ _ frame childFinal⟩
    let post : Memory → List Value → Prop := fun result values =>
      result = leaveFrame frame childFinal ∧ values = [.scalar (.i32
        (if inputValue memory left = bits then 1 else 0))]
    obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
      positiveExecution sign memory left frame call post ⟨tailFuel, _, _, tail, rfl, rfl⟩
    subst final
    subst values
    refine ⟨fuel, leaveFrame frame childFinal, ?_, ?_⟩
    · exact certify_invocation Extracted.program signedIndex signedBody
        (scalarArguments left argument) memory frame memory fuel _ _ lookup checked setup live finished
    · simpa only [leaveFrame, frame, List.foldl_nil] using cells
  · simp only [ite_true]
    obtain ⟨fuel, finished⟩ := negativeExecution sign memory left frame call
    refine ⟨fuel, leaveFrame frame memory, ?_, ?_⟩
    · exact certify_invocation Extracted.program signedIndex signedBody
        (scalarArguments left argument) memory frame memory fuel _ _ lookup checked setup live finished
    · simp [leaveFrame, frame]

#print axioms signed_checked

end UInt256Proof.Equality.Safety
