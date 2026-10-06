import UInt256.Safety.ReadOnlyScalarContract
import UInt256.Safety.CallerSetup
import CIL.Safety.ReturnMemory

namespace UInt256Model.Safety

open CIL.Safety

theorem certify_readOnly_scalar {α : Type} (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (encode : α → CIL.Value) (operation : BitVec 256 → α → CIL.Value)
    (lookup : program[method]? = some body)
    (numeric : ∀ right, numericValue (encode right) = true)
    (fits : ∀ left right, FrameSetupFits body (scalarArguments left (encode right)))
    (executes : ∀ memory left right frame, CallingConditions program memory [left] [] →
      ∃ fuel, run program fuel method 0 (scalarArguments left (encode right)) frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (operation (inputValue memory left) right)])) :
    ReadOnlyScalarContract encode operation program method := by
  intro memory left right call
  have checked : (scalarArguments left (encode right)).mapM (checkedValue memory) =
      .ok (scalarArguments left (encode right)) := by
    have formed := call.input_formed (reference := left) (by simp)
    simp [scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨frame, entered, setup⟩ := enterFrame_succeeds body _ memory call.1.1 (fits left right)
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨fuel, finished⟩ := executes entered left right frame (call.after_frame_setup setup)
  rw [call.input_value_after_setup setup (by simp : left ∈ [left])] at finished
  refine ⟨fuel, leaveFrame frame entered,
    certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame entered memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans (before.cells id bound offset)

#print axioms certify_readOnly_scalar

end UInt256Model.Safety
