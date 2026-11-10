import CIL.Safety.Forwarders
import CIL.Safety.Equations
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition
import CIL.Safety.GuardNormalization

/-! Read-only UInt256 wrappers compose checked prefixes, child invocations and suffixes. -/

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
  refine ⟨⟨call.1.1, ?_, call.1.writable⟩, call.2⟩
  intro view member
  apply call.1.readable view
  simpa [or_comm] using member

/-- Compose a checked prefix, child invocation and proved post-call execution.
The post-call execution preserves memory except for retiring the parent frame. -/
theorem compose_readOnly_binary (program : CIL.Program) (method pc callee : Nat) (body : CIL.Method)
    (operation childOperation : BitVec 256 → BitVec 256 → CIL.Value)
    (childArguments : Reference → Reference → List Value)
    (lookup : program[method]? = some body)
    (fetched : body.code[pc]? = some (.call callee 2))
    (fits : ∀ left right, FrameSetupFits body (readOnlyArguments [left, right]))
    (length : ∀ left right, (childArguments left right).length = 2)
    (known : ∀ left right, (childArguments left right).any Value.hasUnspecified = false)
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
  obtain ⟨frame, entered, setup, _⟩ := call.readOnly_setup_succeeds (fits left right)
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ := child entered left right enteredCall
  have checkedChild : (childArguments left right).mapM (checkedValue entered) =
      .ok (childArguments left right) := by
    obtain ⟨_, _, _, _, checked, _⟩ := childCertificate.2
    exact checked
  have stepped : step body (.call callee 2) pc (readOnlyArguments [left, right]) frame
      (childArguments left right).reverse entered =
      .ok (.call callee (childArguments left right) [] entered) := by
    have valid := (checkedValues_valid _ _ _ checkedChild).2
    simpa only [length left right] using step_call_loaded (body := body)
      (callee := callee) (pc := pc) (args := readOnlyArguments [left, right])
      (frame := frame) valid (known left right)
  let value := operation (inputValue entered left) (inputValue entered right)
  have finished : WP (Execution (fun fuel =>
      invoke program fuel method (readOnlyArguments [left, right]) memory))
      (fun result => result = (leaveFrame frame childFinal, [.scalar value])) := by
    apply WP.enter lookup (checkedValues_of_valid call.readOnly_arguments_valid) setup
    apply WP.adequate.mpr
    apply prefixProof entered left right frame enteredCall
    apply WP.exists_execution
    apply WP.call lookup fetched stepped
      (helperPost := fun result => result =
        (childFinal, [.scalar (childOperation (inputValue entered left) (inputValue entered right))]))
      (WP.exact_iff.mpr ⟨childFuel, childCertificate.1⟩)
    intro final values same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact WP.exact_iff.mpr (suffixProof final left right frame
      (inputValue entered left) (inputValue entered right))
  obtain ⟨fuel, invoked⟩ := WP.exact_iff.mp finished
  have initialValue : value = operation (inputValue memory left) (inputValue memory right) := by
    simp only [value, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])]
  rw [initialValue] at invoked
  refine ⟨fuel, _, InvocationCertificate.of_invoke call.1.1 call.2 invoked, ?_⟩
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
    (forwarding : body.code[pc + 1]? = some (.ret (some .unsigned8))) (returns : body.returnsValue = true)
    (fits : ∀ left right, FrameSetupFits body (readOnlyArguments [left, right]))
    (length : ∀ left right, (childArguments left right).length = 2)
    (known : ∀ left right, (childArguments left right).any Value.hasUnspecified = false)
    (numeric : ∀ left right, numericValue (operation left right) = true)
    (normalized : ∀ left right, ∃ flag, operation left right = .i32 flag ∧
      CIL.NarrowKind.unsigned8.extend flag = flag)
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
    lookup fetched fits length known child
  · intro memory left right frame x y
    apply (WP.exact_iff (execution := Execution _)).mp
    obtain ⟨flag, result, normalizedFlag⟩ := normalized x y
    rw [result]
    apply WP.returned lookup forwarding
    · apply step_return_unchanged
      · simp [returns]
      · rfl
      · rfl
      · exact ⟨flag, rfl, normalizedFlag⟩
    · rfl
    · rfl
  · exact prefixProof

end UInt256Model.Safety
