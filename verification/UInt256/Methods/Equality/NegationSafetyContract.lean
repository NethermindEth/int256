import UInt256.Methods.Equality.NegationSafety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem inequality_entry_checked
    (child : EqualityInvocation (wrapperIndex true)) (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program Extracted.entryIndex (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left ≠ inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  have lookup : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have fits : FrameSetupFits Extracted.entryBody (readOnlyArguments [left, right]) := by
    simp [cil_code, FrameSetupFits, InitializersFit, AggregateArgumentsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.readOnly_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ := child entered left right enteredCall
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fetched : Extracted.entryBody.code[negationCall]? = some (.call (wrapperIndex true) 2) := by rfl
  have stepped : step Extracted.entryBody (.call (wrapperIndex true) 2) negationCall
      (readOnlyArguments [left, right]) frame [.reference (.address right), .reference (.address left)] entered =
      .ok (.call (wrapperIndex true) (readOnlyArguments [left, right]) [] entered) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨3, negation_return _ _ frame childFinal⟩
  let flag : BitVec 32 := if inputValue entered left = inputValue entered right then 1 else 0
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 (if flag = 0 then 1 else 0))]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    negation_prefix left right frame entered enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have initialFlag : (if flag = 0 then (1 : BitVec 32) else 0) =
      (if inputValue memory left ≠ inputValue memory right then 1 else 0) := by
    simp only [flag, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])]
    split <;> simp_all
  rw [initialFlag] at finished
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have leftFormed := call.input_formed (reference := left) (by simp)
    have rightFormed := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, leftFormed, rightFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame childFinal memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((childCells id (Nat.lt_of_lt_of_le bound fresh.1.next) offset).trans (before.cells id bound offset))

theorem inequality_readOnly_contract
    (child : EqualityInvocation (wrapperIndex true)) :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 ≠ values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  intro memory inputs arity call
  cases inputs with
  | nil => simp at arity
  | cons left rest =>
    cases rest with
    | nil => simp at arity
    | cons right tail =>
      cases tail with
      | cons _ _ => simp at arity
      | nil =>
        simpa only [List.map_cons, List.map_nil, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] using inequality_entry_checked child memory left right call

#print axioms inequality_readOnly_contract
#print axioms inequality_entry_checked

end UInt256Proof.Equality.Safety
