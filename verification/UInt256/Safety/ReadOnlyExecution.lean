import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.CallerSetup
import CIL.Safety.ReturnMemory

namespace UInt256Model.Safety

open CIL.Safety

/-- Lift a proved read-only body execution to an invocation certificate. This
    consumes an execution theorem, not a caller assumption about future success. -/
theorem certify_readOnly_binary_frame (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (operation : BitVec 256 → BitVec 256 → CIL.Value)
    (lookup : program[method]? = some body)
    (fits : ∀ left right, FrameSetupFits body (readOnlyArguments [left, right]))
    (frameCondition : Frame → Prop)
    (frameSetup : ∀ memory left right frame entered,
      enterFrame body (readOnlyArguments [left, right]) memory = .ok (frame, entered) →
      frameCondition frame)
    (executes : ∀ memory left right frame,
      frameCondition frame → CallingConditions program memory [left, right] [] →
      ∃ fuel, run program fuel method 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (operation (inputValue memory left) (inputValue memory right))]))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program method (readOnlyArguments [left, right]) memory fuel final
        [.scalar (operation (inputValue memory left) (inputValue memory right))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, setup, live⟩ := call.readOnly_setup_succeeds (fits left right)
  obtain ⟨fuel, finished⟩ := executes entered left right frame (frameSetup memory left right frame entered setup)
    (call.after_frame_setup setup)
  rw [call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, leaveFrame frame entered,
    certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame entered memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans (before.cells id bound offset)

theorem certify_readOnly_binary (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (operation : BitVec 256 → BitVec 256 → CIL.Value)
    (lookup : program[method]? = some body)
    (fits : ∀ left right, FrameSetupFits body (readOnlyArguments [left, right]))
    (executes : ∀ memory left right frame,
      CallingConditions program memory [left, right] [] →
      ∃ fuel, run program fuel method 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (operation (inputValue memory left) (inputValue memory right))]))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program method (readOnlyArguments [left, right]) memory fuel final
        [.scalar (operation (inputValue memory left) (inputValue memory right))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary_frame program method body operation lookup fits (fun _ => True)
    (fun _ _ _ _ _ _ => True.intro)
    (fun memory left right frame _ => executes memory left right frame) memory left right call

#print axioms certify_readOnly_binary_frame
#print axioms certify_readOnly_binary

end UInt256Model.Safety
