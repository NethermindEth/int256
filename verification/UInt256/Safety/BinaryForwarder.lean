import UInt256.Safety.Contract
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Model.Safety
open CIL.Safety

theorem forward_wrapping_binary (program : CIL.Program) (wrapperIndex childIndex : Nat)
    (wrapperBody : CIL.Method) (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (found : program[wrapperIndex]? = some wrapperBody)
    (code : wrapperBody.code = [.arg 0, .arg 1, .arg 2, .call childIndex 3, .ret])
    (returns : wrapperBody.returnsValue = false)
    (kinds : wrapperBody.localKinds = []) (locals : wrapperBody.locals = [])
    (aggregates : wrapperBody.aggregateArgs = [])
    (child : WrappingBinaryContract operation program childIndex) :
    WrappingBinaryContract operation program wrapperIndex := by
  intro memory left right output call
  obtain ⟨childFuel, final, certificate, value, writable, footprint⟩ :=
    child memory left right output call
  let args := binaryArguments left right output
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fl := call.input_formed (by simp : left ∈ [left, right])
  have fr := call.input_formed (by simp : right ∈ [left, right])
  have fo := call.output_formed (by simp : output ∈ [output])
  have fetched : wrapperBody.code[3]? = some (.call childIndex 3) := by simp [code]
  have stepped : step wrapperBody (.call childIndex 3) 3 args frame
      [.reference (.address output), .reference (.address right), .reference (.address left)] memory =
      .ok (.call childIndex args [] memory) := by
    simp [args, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run program 1 wrapperIndex 4 args frame [] final =
      .ok (final, []) := by
    have fetch : wrapperBody.code[4]? = some .ret := by simp [code]
    simp [run, found, fetch, returns, step, frame, leaveFrame,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩ ⟨1, returned⟩
  have prefixRun : ∃ fuel after returned,
      run program fuel wrapperIndex 0 args frame [] memory = .ok (after, returned) ∧
      after = final ∧ returned = [] := by
    iterate 3
      apply run_next_exists (fun after returned => after = final ∧ returned = []) found (by rw [code]; rfl)
      simp [step, args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨tailFuel, final, [], tail, rfl, rfl⟩
  obtain ⟨fuel, after, returned, executed, rfl, rfl⟩ := prefixRun
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame wrapperBody args memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, locals, aggregates, makeLocals, makeArgumentHomes, frame,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, after, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live executed,
    value, writable, footprint⟩


#print axioms forward_wrapping_binary
end UInt256Model.Safety
