import UInt256.Methods.Add.EntrySafetySetup
import UInt256.Methods.Add.ScalarChecked

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

def entryScalarCall : Nat :=
  Extracted.entryBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.addScalarIndex
    | _ => false

theorem entry_scalar_prefix (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex entryScalarCall (binaryArguments left right output)
        frame [.scalar (.i32 0), .reference (.address output), .reference (.address right),
          .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output)
        frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  conv at continuation in entryScalarCall => cbv
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo,
            pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem entry_scalar_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory) :
    run Extracted.program 2 Extracted.entryIndex (entryScalarCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, []) := by
  conv in entryScalarCall => cbv
  simp only [Nat.reduceAdd]
  apply Eq.trans
  · apply run_next
    · simp only [cil_code]; rfl
    · simp only [cil_code]; rfl
    · simp [step, pureArity, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [run]
    simp [cil_code, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

structure PublicAddResult (original final : CIL.Safety.Memory) (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original left + inputValue original right
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

theorem entry_run_checked (memory entered : CIL.Safety.Memory) (frame : Frame) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame Extracted.entryBody (binaryArguments left right output) memory = .ok (frame, entered)) :
    ∃ fuel final,
      run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, []) ∧ PublicAddResult memory final left right output := by
  let post := fun final (values : List Value) => values = [] ∧ PublicAddResult memory final left right output
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have executed : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, values) ∧ post final values := by
    apply entry_scalar_prefix left right output frame entered enteredCall post
    obtain ⟨childFuel, after, values, invoked, result⟩ := scalar_checked entered left right output enteredCall
    rw [result.flag] at invoked
    have mf : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
    have fetched : Extracted.entryBody.code[entryScalarCall]? = some (.call Extracted.addScalarIndex 4) := by
      conv in entryScalarCall => cbv
      simp only [cil_code]
    have stepped : step Extracted.entryBody (.call Extracted.addScalarIndex 4) entryScalarCall
        (binaryArguments left right output) frame
        [.scalar (.i32 0), .reference (.address output), .reference (.address right), .reference (.address left)]
        entered = .ok (.call Extracted.addScalarIndex (scalarArguments left right output) [] entered) := by
      have fl := enteredCall.input_formed (reference := left) (by simp)
      have fr := enteredCall.input_formed (reference := right) (by simp)
      have fo := enteredCall.output_formed (reference := output) (by simp)
      simp [step, scalarArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨fuel, finished⟩ := run_call_exists mf fetched stepped ⟨childFuel, invoked⟩
      ⟨2, entry_scalar_return _ (addOverflow entered left right) frame after⟩
    have retained := leaveFrame_preserves_memory_below frame after memory.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    have bytes : (fun offset => ((leaveFrame frame after).cells output.allocation offset).bits) =
        (fun offset => (after.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    have inputSame : ∀ reference ∈ [left, right], inputValue entered reference = inputValue memory reference := by
      intro reference member
      simp only [inputValue, call.input_bytes_of_memory_below preserved member]
    refine ⟨fuel, leaveFrame frame after, [], finished, rfl, ?_⟩
    refine ⟨leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_, ?_, ?_⟩
    · have math := result.value
      rw [inputSame left (by simp), inputSame right (by simp)] at math
      simpa only [inputValue, bytes] using math
    · exact (retained.access output outputOld 32 1 true).trans result.writable
    · intro id old offset outside
      exact (retained.cells id old offset).trans
        ((result.footprint id (Nat.lt_of_lt_of_le old fresh.1.next) offset outside).trans (preserved.cells id old offset))
  obtain ⟨fuel, final, values, finished, equal, result⟩ := executed
  subst values
  exact ⟨fuel, final, finished, result⟩

#print axioms entry_scalar_prefix
#print axioms entry_scalar_return
#print axioms entry_run_checked

end UInt256Proof.Safety
