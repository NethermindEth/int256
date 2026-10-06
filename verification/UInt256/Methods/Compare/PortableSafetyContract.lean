import UInt256.Methods.Compare.PortableSafetyExecution
import UInt256.Safety.ReadOnlyForwarder

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

theorem portable_result_math (memory : Memory) (left right : Reference) :
    maskResult (portableEqual (inputValue memory left) (inputValue memory right))
      (portableLess (inputValue memory left) (inputValue memory right)) =
      if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  simp only [portableEqual, portableLess, portableEqualityMask, portableLessMask, mask_result_math]

theorem portable_checked : BinaryReadOnlyInvocation
    (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0))
    Extracted.program portableIndex := by
  intro memory left right call
  obtain ⟨frame, entered, setup, homes, enteredCall, before⟩ := portable_setup memory left right call
  obtain ⟨fuel, final, finished, preserved⟩ := portable_run entered left right frame memory.nextIdentity homes enteredCall
  rw [portable_result_math, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
    call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished
  have found : Extracted.program[portableIndex]? = some portableBody := by rfl
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame final memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((preserved.cells id bound offset).trans (before.cells id bound offset))

#print axioms portable_result_math
#print axioms portable_checked
end UInt256Proof.Compare.Safety
