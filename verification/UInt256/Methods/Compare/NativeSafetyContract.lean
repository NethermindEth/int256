import UInt256.Methods.Compare.NativeSafetyExecution
import UInt256.Safety.ReadOnlyForwarder

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def nativePredicate (left right : BitVec 256) : Prop :=
  if nativeUsesLess then
    if nativeInclusive then right.toNat ≤ left.toNat else right.toNat < left.toNat
  else
    if nativeInclusive then left.toNat ≤ right.toNat else left.toNat < right.toNat

instance (left right : BitVec 256) : Decidable (nativePredicate left right) := by
  unfold nativePredicate
  infer_instance

theorem native_result_math (memory : Memory) (left right : Reference) :
    nativeResult (inputValue memory left) (inputValue memory right) =
      if nativePredicate (inputValue memory left) (inputValue memory right) then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  cases direction : nativeUsesLess <;> cases inclusive : nativeInclusive
  all_goals
    simp only [nativeResult, nativeEqual, nativeComparison, nativePredicate, direction, inclusive,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
      show (170 : BitVec 8) = BitVec.ofNat 8 170 from rfl,
      nativeOrderingMask, nativeOrderingReverseMask]
  all_goals
    simp only [show (85 : BitVec 32) = BitVec.ofNat 32 85 from rfl,
      show (86 : BitVec 32) = BitVec.ofNat 32 86 from rfl,
      mask_sub_negative (orderingMask (inputLimb memory left) (inputLimb memory right)) 85
        (orderingMask_bound _ _) (by decide) (by decide),
      mask_sub_negative (orderingMask (inputLimb memory right) (inputLimb memory left)) 85
        (orderingMask_bound _ _) (by decide) (by decide),
      mask_sub_negative (orderingMask (inputLimb memory left) (inputLimb memory right)) 86
        (orderingMask_bound _ _) (by decide) (by decide),
      mask_sub_negative (orderingMask (inputLimb memory right) (inputLimb memory left)) 86
        (orderingMask_bound _ _) (by decide) (by decide), orderingMask_lt, orderingMask_le]

theorem native_checked : BinaryReadOnlyInvocation
    (fun left right => .i32 (if nativePredicate left right then 1 else 0))
    Extracted.program nativeIndex := by
  intro memory left right call
  obtain ⟨frame, entered, setup, homes, enteredCall, before⟩ := native_setup memory left right call
  obtain ⟨fuel, final, finished, preserved⟩ := native_run entered left right frame memory.nextIdentity homes enteredCall
  rw [native_result_math, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
    call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished
  have found : Extracted.program[nativeIndex]? = some nativeBody := by rfl
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

#print axioms native_result_math
#print axioms native_checked
end UInt256Proof.Compare.Safety
