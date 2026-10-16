import UInt256.Methods.Multiply.Calls
import CIL.Safety.CallComposition
namespace UInt256Proof.Multiply.Calls
open CIL.Safety UInt256Model.Safety

def forwardingBody (profile : CIL.FeatureProfile) (child : Nat) : CIL.Method :=
  {profile := profile, returnsValue := true, locals := [],
   code := [.arg 0, .arg 1, .arg 2, .call child 3, .ret]}

theorem forward_word_contract (profile : CIL.FeatureProfile) (program : CIL.Program)
    (wrapper child : Nat) (found : program[wrapper]? = some (forwardingBody profile child))
    (contract : WordContract program child) : WordContract program wrapper := by
  intro memory a b output wf writable
  obtain ⟨childFuel, final, invoked, valid, loaded, authority, outside⟩ := contract memory a b output wf writable
  let args : List Value := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have formed := access_reference_valid _ _ _ _ _ writable
  have fetched : (forwardingBody profile child).code[3]? = some (.call child 3) := rfl
  have stepped : step (forwardingBody profile child) (.call child 3) 3 args frame
      [.reference (.address output), .scalar (.i64 b), .scalar (.i64 a)] memory =
      .ok (.call child args [] memory) := by
    simp [step, args, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run program 1 wrapper 4 args frame [.scalar (.i64 (highProduct a b))] final =
      .ok (final, [.scalar (.i64 (highProduct a b))]) := by
    simp [run, found, forwardingBody, step, checkedValue, numericValue, frame, leaveFrame,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩ ⟨1, returned⟩
  have prefixRun : ∃ fuel after values,
      run program fuel wrapper 0 args frame [] memory = .ok (after, values) ∧
      after = final ∧ values = [.scalar (.i64 (highProduct a b))] := by
    iterate 3
      apply run_next_exists (fun after values => after = final ∧ values = [.scalar (.i64 (highProduct a b))]) found (by rfl)
      simp [step, args, checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨tailFuel, final, _, tail, rfl, rfl⟩
  obtain ⟨fuel, after, values, executed, rfl, rfl⟩ := prefixRun
  refine ⟨fuel, after, ?_, valid, loaded, authority, outside⟩
  simpa [invoke, found, forwardingBody, args, checkedValue, numericValue, formValue,
    formed, checkedAt, enterFrame, makeLocals, makeParameterHomes, makeArgumentHomes, frame,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] using executed
#print axioms forward_word_contract
end UInt256Proof.Multiply.Calls