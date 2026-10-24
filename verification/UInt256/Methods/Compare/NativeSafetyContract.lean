import UInt256.Methods.Compare.NativeSafetyExecution
import UInt256.Safety.ReadOnlyForwarder
namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety
def nativePredicate (usesLess inclusive : Bool) (left right : BitVec 256) : Prop :=
  if usesLess then
    if inclusive then right.toNat ≤ left.toNat else right.toNat < left.toNat
  else
    if inclusive then left.toNat ≤ right.toNat else left.toNat < right.toNat

instance (usesLess inclusive : Bool) (left right : BitVec 256) : Decidable (nativePredicate usesLess inclusive left right) := by
  unfold nativePredicate
  infer_instance

theorem native_result_math (usesLess inclusive : Bool) (memory : Memory) (left right : Reference) :
    nativeResult usesLess inclusive (inputValue memory left) (inputValue memory right) =
      if nativePredicate usesLess inclusive (inputValue memory left) (inputValue memory right) then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  cases direction : usesLess <;> cases mode : inclusive
  all_goals
    simp only [nativeResult, nativeEqual, nativeComparison, nativePredicate, direction, mode,
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

theorem native_checked (profile : CIL.FeatureProfile) (usesLess inclusive : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (nativeBody profile usesLess inclusive))
    (native : profile.avx512FVL = true) (nativeF : profile.avx512F = true)
    (avx2 : profile.avx2 = true) (avx : profile.avx = true) : BinaryReadOnlyInvocation
    (fun left right => .i32 (if nativePredicate usesLess inclusive left right then 1 else 0))
    program index := by
  intro memory left right call
  obtain ⟨frame, entered, setup, homes, enteredCall, before⟩ := native_setup profile usesLess inclusive program memory left right call
  obtain ⟨fuel, final, finished, preserved⟩ := native_run profile usesLess inclusive program index found native nativeF avx2 avx entered left right frame memory.nextIdentity homes enteredCall
  rw [native_result_math, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
    call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished

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
