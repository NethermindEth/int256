import UInt256.Methods.Equality.WrapperSafety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def EqualityInvocation (method : Nat) : Prop :=
  ∀ (memory : Memory) (left right : Reference),
    CallingConditions Extracted.program memory [left, right] [] →
    ∃ fuel final,
      InvocationCertificate Extracted.program method (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

def wrapperCallee (outer : Bool) : Nat :=
  match (wrapperBody outer).code[wrapperCall outer]? with
  | some (.call callee _) => callee
  | _ => Extracted.program.length

theorem wrapper_checked (outer : Bool)
    (forwarding : (wrapperBody outer).code[wrapperCall outer + 1]? = some .ret)
    (child : EqualityInvocation (wrapperCallee outer)) :
    EqualityInvocation (wrapperIndex outer) := by
  intro memory left right call
  have lookup : Extracted.program[wrapperIndex outer]? = some (wrapperBody outer) := by
    cases outer <;> rfl
  have fits : FrameSetupFits (wrapperBody outer) (readOnlyArguments [left, right]) := by
    cases outer
    all_goals
      conv in (wrapperBody _) => cbv
      simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.readOnly_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ := child entered left right enteredCall
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fetched : (wrapperBody outer).code[wrapperCall outer]? = some (.call (wrapperCallee outer) 2) := by
    cases outer <;> rfl
  have stepped : step (wrapperBody outer) (.call (wrapperCallee outer) 2) (wrapperCall outer)
      (readOnlyArguments [left, right]) frame [.reference (.address right), .reference (.address left)] entered =
      .ok (.call (wrapperCallee outer) (readOnlyArguments [left, right]) [] entered) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨1, wrapper_return outer _ _ frame childFinal forwarding⟩
  let flag : BitVec 32 := if inputValue entered left = inputValue entered right then 1 else 0
  let post : Memory → List Value → Prop :=
    fun final values => final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 flag)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    wrapper_prefix outer left right frame entered enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have initialFlag : flag = (if inputValue memory left = inputValue memory right then 1 else 0) := by
    simp only [flag, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])]
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

theorem equality_readOnly_contract
    (entry : EqualityInvocation Extracted.entryIndex) :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
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
          List.getElem?_cons_succ, Option.getD_some] using entry memory left right call

#print axioms equality_readOnly_contract
#print axioms wrapper_checked

end UInt256Proof.Equality.Safety
