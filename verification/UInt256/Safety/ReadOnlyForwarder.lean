import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition

namespace UInt256Model.Safety
open CIL.Safety

/-- A binary read-only invocation with its independent initial-value result. -/
def BinaryReadOnlyInvocation (operation : BitVec 256 → BitVec 256 → CIL.Value)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ memory left right, CallingConditions program memory [left, right] [] →
    ∃ fuel final,
      InvocationCertificate program method (readOnlyArguments [left, right]) memory fuel final
        [.scalar (operation (inputValue memory left) (inputValue memory right))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

/-- Expose a binary invocation through the public list-based contract. -/
theorem BinaryReadOnlyInvocation.to_contract
    {operation : BitVec 256 → BitVec 256 → CIL.Value} {program : CIL.Program} {method : Nat}
    (entry : BinaryReadOnlyInvocation operation program method) :
    ReadOnlyContract (fun values => operation (values[0]?.getD 0) (values[1]?.getD 0))
      program method 2 := by
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

/-- Reordering read-only inputs preserves every calling requirement, including
shared or partially overlapping storage. -/
theorem CallingConditions.swap_binary_inputs {program : CIL.Program}
    {memory : Memory} {left right : Reference} {outputs : List Reference}
    (call : CallingConditions program memory [left, right] outputs) :
    CallingConditions program memory [right, left] outputs := by
  refine ⟨⟨call.1.1, ?_, call.1.2.2⟩, call.2⟩
  intro view member
  apply call.1.2.1 view
  simpa [or_comm] using member

#print axioms CallingConditions.swap_binary_inputs

/-- Compose a checked prefix, child invocation and proved post-call execution.
The post-call execution preserves memory except for retiring the parent frame. -/
theorem compose_readOnly_binary (program : CIL.Program) (method pc callee : Nat) (body : CIL.Method)
    (operation childOperation : BitVec 256 → BitVec 256 → CIL.Value)
    (childArguments : Reference → Reference → List Value)
    (lookup : program[method]? = some body)
    (fetched : body.code[pc]? = some (.call callee 2))
    (fits : ∀ left right, FrameSetupFits body (readOnlyArguments [left, right]))
    (length : ∀ left right, (childArguments left right).length = 2)
    (child : ∀ memory left right, CallingConditions program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate program callee (childArguments left right) memory fuel final
          [.scalar (childOperation (inputValue memory left) (inputValue memory right))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset)
    (suffixProof : ∀ memory left right frame x y,
      ∃ fuel, run program fuel method (pc + 1) (readOnlyArguments [left, right]) frame
        [.scalar (childOperation x y)] memory =
          .ok (leaveFrame frame memory, [.scalar (operation x y)]))
    (prefixProof : ∀ memory left right frame,
      CallingConditions program memory [left, right] [] →
      ∀ post : Memory → List Value → Prop,
      (∃ fuel final values,
        run program fuel method pc (readOnlyArguments [left, right]) frame
          (childArguments left right).reverse memory = .ok (final, values) ∧ post final values) →
      ∃ fuel final values,
        run program fuel method 0 (readOnlyArguments [left, right]) frame [] memory =
          .ok (final, values) ∧ post final values) :
    BinaryReadOnlyInvocation operation program method := by
  intro memory left right call
  obtain ⟨frame, entered, setup, live⟩ := call.readOnly_setup_succeeds (fits left right)
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ := child entered left right enteredCall
  have checkedChild : (childArguments left right).mapM (checkedValue entered) =
      .ok (childArguments left right) := by
    obtain ⟨_, _, _, _, checked, _⟩ := childCertificate.2
    exact checked
  have stepped : step body (.call callee 2) pc (readOnlyArguments [left, right]) frame
      (childArguments left right).reverse entered =
      .ok (.call callee (childArguments left right) [] entered) := by
    have count := length left right
    simp only [step, List.length_reverse, count]
    simp only [Nat.lt_irrefl, ite_false]
    have take : List.take 2 (childArguments left right).reverse = (childArguments left right).reverse := by
      apply List.take_of_length_le
      simp [count]
    have drop : List.drop 2 (childArguments left right).reverse = [] := by
      apply List.drop_eq_nil_of_le
      simp [count]
    simp [take, drop, checkedChild, Bind.bind, Except.bind, Pure.pure, Except.pure]
  let value := operation (inputValue entered left) (inputValue entered right)
  obtain ⟨suffixFuel, tail⟩ := suffixProof childFinal left right frame
    (inputValue entered left) (inputValue entered right)
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨suffixFuel, tail⟩
  let post : Memory → List Value → Prop :=
    fun final values => final = leaveFrame frame childFinal ∧ values = [.scalar value]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    prefixProof entered left right frame enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have initialValue : value = operation (inputValue memory left) (inputValue memory right) := by
    simp only [value, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])]
  rw [initialValue] at finished
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame childFinal memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((childCells id (Nat.lt_of_lt_of_le bound fresh.1.next) offset).trans (before.cells id bound offset))


/-- Compose a proved dispatch prefix, actual child invocation and direct return.
The child may receive reordered arguments, but its supplied checked theorem must
establish the parent's stated result for those exact arguments. -/
theorem forward_readOnly_binary (program : CIL.Program) (method pc callee : Nat) (body : CIL.Method)
    (operation : BitVec 256 → BitVec 256 → CIL.Value)
    (childArguments : Reference → Reference → List Value)
    (lookup : program[method]? = some body)
    (fetched : body.code[pc]? = some (.call callee 2))
    (forwarding : body.code[pc + 1]? = some .ret) (returns : body.returnsValue = true)
    (fits : ∀ left right, FrameSetupFits body (readOnlyArguments [left, right]))
    (length : ∀ left right, (childArguments left right).length = 2)
    (numeric : ∀ left right, numericValue (operation left right) = true)
    (child : ∀ memory left right, CallingConditions program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate program callee (childArguments left right) memory fuel final
          [.scalar (operation (inputValue memory left) (inputValue memory right))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset)
    (prefixProof : ∀ memory left right frame,
      CallingConditions program memory [left, right] [] →
      ∀ post : Memory → List Value → Prop,
      (∃ fuel final values,
        run program fuel method pc (readOnlyArguments [left, right]) frame
          (childArguments left right).reverse memory = .ok (final, values) ∧ post final values) →
      ∃ fuel final values,
        run program fuel method 0 (readOnlyArguments [left, right]) frame [] memory =
          .ok (final, values) ∧ post final values) :
    BinaryReadOnlyInvocation operation program method := by
  apply compose_readOnly_binary program method pc callee body operation operation childArguments
    lookup fetched fits length child
  · intro memory left right frame x y
    refine ⟨1, ?_⟩
    simp [run, lookup, forwarding, step, returns, checkedValue, numeric,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · exact prefixProof

#print axioms compose_readOnly_binary
#print axioms forward_readOnly_binary
end UInt256Model.Safety
