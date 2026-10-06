import UInt256.Methods.Shift.ContextSafetyContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

def wrapperIndex : Nat := Extracted.program.findIdx fun body =>
  match body.code with
  | [.arg 0, .arg 1, .arg 2, .call _ 3, .ret] => true
  | _ => false

def wrapperBody : CIL.Method := Extracted.program[wrapperIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- The instance wrapper forwards the original references and count to the
    checked shift body; its empty frame neither copies nor separates aliases. -/
theorem checked_wrapper_context (memory : Memory) (input : Reference) (count : BitVec 32) (output : Reference)
    (call : CallingConditions Extracted.program memory [input] [output])
    (allowed : InitializationAllowed input output) :
    ShiftInvocation shiftDirection Extracted.program wrapperIndex memory input count output := by
  obtain ⟨childFuel, final, certificate, value, writable, readable, footprint⟩ :=
    checked_shift_context memory input count output call allowed
  let args := shiftArguments input count output
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fi := call.input_formed (by simp : input ∈ [input])
  have fo := call.output_formed (by simp : output ∈ [output])
  have found : Extracted.program[wrapperIndex]? = some wrapperBody := by rfl
  have fetched : wrapperBody.code[3]? = some (.call shiftIndex 3) := by rfl
  have stepped : step wrapperBody (.call shiftIndex 3) 3 args frame
      [.reference (.address output), .scalar (.i32 count), .reference (.address input)] memory =
      .ok (.call shiftIndex args [] memory) := by
    simp [args, shiftArguments, step, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run Extracted.program 1 wrapperIndex 4 args frame [] final =
      .ok (final, []) := by
    have fetch : wrapperBody.code[4]? = some .ret := by rfl
    have returns : wrapperBody.returnsValue = false := by rfl
    simp [run, found, fetch, returns, step, frame, leaveFrame,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩ ⟨1, returned⟩
  have prefixRun : ∃ fuel after returned,
      run Extracted.program fuel wrapperIndex 0 args frame [] memory = .ok (after, returned) ∧
      after = final ∧ returned = [] := by
    iterate 3
      apply run_next_exists (fun after returned => after = final ∧ returned = []) found (by rfl)
      simp [step, args, shiftArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨tailFuel, final, [], tail, rfl, rfl⟩
  obtain ⟨fuel, after, returned, executed, rfl, rfl⟩ := prefixRun
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, shiftArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame wrapperBody args memory = .ok (frame, memory) := by
    have kinds : wrapperBody.localKinds = [] := by rfl
    have locals : wrapperBody.locals = [] := by rfl
    have aggregates : wrapperBody.aggregateArgs = [] := by rfl
    simp [enterFrame, kinds, locals, aggregates, makeLocals, makeArgumentHomes, frame,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, after, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live executed,
    value, writable, readable, footprint⟩


#print axioms checked_wrapper_context
end UInt256Proof.Shift.Safety
