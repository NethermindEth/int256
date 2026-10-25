import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.ReferenceOperator
open CIL.Safety UInt256Model.Safety

abbrev body (profile : CIL.FeatureProfile) (negate : Bool) (callee : Nat) := PrimitiveOperator.body profile false negate callee

theorem checked (equal : BitVec 256 → BitVec 256 → Bool)
    (profile : CIL.FeatureProfile) (negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body profile negate callee))
    (child : ∀ memory left right, CallingConditions program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate program callee (readOnlyArguments [left, right]) memory fuel final
          [.scalar (.i32 (if equal (inputValue memory left) (inputValue memory right) then 1 else 0))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset)
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program entry (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if equal (inputValue memory left) (inputValue memory right) != negate then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  have setup : enterFrame (body profile negate callee) (readOnlyArguments [left, right]) memory =
      .ok (frame, memory) := by
    simp [enterFrame, body, PrimitiveOperator.body, makeSelectedLocals, makeLocals, makeArgumentHomes, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, final, certificate, cells⟩ := child memory left right call
  have fetched : (body profile negate callee).code[2]? = some (.call callee 2) := by rfl
  have stepped : step (body profile negate callee) (.call callee 2) 2
      (readOnlyArguments [left, right]) frame [.reference (.address right), .reference (.address left)] memory =
      .ok (.call callee (readOnlyArguments [left, right]) [] memory) := by
    simp [step, cil_guard, observerCount, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩
    ⟨3, PrimitiveOperator.returned profile false negate program entry callee found _ _ frame final⟩
  have executed : run program (tailFuel + 2) entry 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame final,
        [.scalar (.i32 (if equal (inputValue memory left) (inputValue memory right) != negate then 1 else 0))]) := by
    cil_checked_steps 2 [body, PrimitiveOperator.body, readOnlyArguments, fl, fr]
    exact tail
  refine ⟨tailFuel + 2, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live executed, ?_⟩
  simpa only [leaveFrame, frame, List.foldl_nil] using cells

theorem readOnly_contract (equal : BitVec 256 → BitVec 256 → Bool) (program : CIL.Program) (entry : Nat)
    (child : ∀ memory left right, CallingConditions program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate program entry (readOnlyArguments [left, right]) memory fuel final
          [.scalar (.i32 (if equal (inputValue memory left) (inputValue memory right) then 1 else 0))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset) :
    ReadOnlyContract (fun values => .i32 (if equal (values[0]?.getD 0) (values[1]?.getD 0) then 1 else 0))
      program entry 2 := by
  intro memory inputs length call
  rcases inputs with _ | ⟨left, tail⟩
  · simp at length
  rcases tail with _ | ⟨right, tail⟩
  · simp at length
  have empty : tail = [] := by simpa using length
  subst tail
  simpa using child memory left right call

#print axioms checked
#print axioms readOnly_contract
end UInt256Proof.Equality.ReferenceOperator
