import UInt256.Methods.Subtract.ScalarSmallFinish

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem input_small_value (memory : CIL.Safety.Memory) (reference : Reference)
    (small : inputLimb memory reference 1 ||| inputLimb memory reference 2 |||
      inputLimb memory reference 3 = 0) :
    inputValue memory reference = BitVec.ofNat 256 (inputLimb memory reference 0).toNat := by
  obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
  have initial : UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
    UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory reference) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

theorem scalar_private_next (original entered current : CIL.Safety.Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) : original.nextIdentity ≤ current.nextIdentity := by
  have specified : scalarLocalSpecs[0]? = some (some 0) := by rfl
  obtain ⟨reference, _, fresh, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have currentWrite := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements currentWrite
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

theorem scalar_right_small_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (small : inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3 = 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ SubtractResult memory final values left right output := by
  let post := fun final values => SubtractResult memory final values left right output
  obtain ⟨frame, entered, setup, homes, _, enteredWF⟩ :=
    scalar_frame_setup memory (binaryArguments left right output) call.1.1
  have executed := scalar_right_prefix_checked memory entered left right output
    frame call setup homes post (by
      intro home current slot loaded preserved currentCall authority
      rw [small]
      apply scalar_small_prefix left right output home (inputLimb memory right 0) frame current
        (currentCall.input_formed (by simp)) (currentCall.output_formed (by simp)) slot loaded post
      have next := scalar_private_next memory entered current frame homes enteredWF currentCall.1.1 authority
      have smallValue := input_small_value memory right small
      have kept : inputValue current left = inputValue memory left := by
        simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
      have wide : (inputLimb memory right 0).toNat < 2^256 :=
        Nat.lt_trans (inputLimb memory right 0).isLt (by decide)
      apply scalar_small_finish memory entered current frame left right output (inputLimb memory right 0)
        call setup currentCall preserved next
      · rw [kept, smallValue]
      · rw [kept, smallValue]
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide])
  obtain ⟨fuel, final, values, finished, result⟩ := executed
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, values, ?_, result⟩
  change run Extracted.program fuel scalarIndex 0
    (binaryArguments left right output) frame [] entered = .ok (final, values) at finished
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished

#print axioms scalar_right_small_checked
end UInt256Proof.Subtract.Safety
