import UInt256.Methods.Subtract.ScalarSafetyPrefix
import UInt256.Methods.Subtract.SmallSafetyFinish
import UInt256.Methods.Subtract.SafetyResult

namespace UInt256Proof.Subtract.Safety

open CIL.Safety

def scalarSmallCall : Nat := scalarBody.code.findIdx fun op => match op with
  | .call callee _ => callee == Extracted.subtractScalarUInt64Index | _ => false

theorem scalar_small_prefix (left right output home : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory)
    (formed : form memory left = .ok left)
    (outputFormed : form memory output = .ok output)
    (slot : frame.locals[0]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarSmallCall
        (UInt256Model.Safety.binaryArguments left right output) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address left)] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarFirstDecision
        (UInt256Model.Safety.binaryArguments left right output) frame [.scalar (.i64 0)] memory = .ok (result, returned) ∧
      post result returned := by
  have reading := load_local_word64_of_read loaded
  conv in scalarFirstDecision => cbv
  conv at continuation in scalarSmallCall => cbv
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · rfl
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, UInt256Model.Safety.binaryArguments, UInt256Model.Safety.binaryArguments, step,
            checkedValue, numericValue, formValue, formed, outputFormed, slot, reading,
            pureArity, scalars, CIL.step, CIL.truth, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_small_return (args : List Value) (flag : BitVec 32)
    (frame : Frame) (memory : Memory) :
    run Extracted.program 1 scalarIndex (scalarSmallCall + 1)
      args frame [.scalar (.i32 flag)] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have fetched : scalarBody.code[scalarSmallCall + 1]? = some .ret := by rfl
  have returning : scalarBody.returnsValue = true := by rfl
  rw [run]
  simp [found, fetched, returning, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_small_prefix
#print axioms scalar_small_return

end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

theorem scalar_small_finish (original entered current : CIL.Safety.Memory)
    (frame : Frame) (left right output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original =
      .ok (frame, entered))
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (sum : inputValue current left - BitVec.ofNat 256 word.toNat =
      inputValue original left - inputValue original right)
    (underflow : ((inputValue current left).toNat < word.toNat) ↔
      ((inputValue original left).toNat < (inputValue original right).toNat)) :
    ∃ fuel final values,
      run Extracted.program fuel scalarIndex scalarSmallCall
        (binaryArguments left right output) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address (left))] current = .ok (final, values) ∧
      SubtractResult original final values left right output := by
  have member : left ∈ [left, right] := by
    simp
  have selected : CallingConditions Extracted.program current [left] [output] := by
    refine ⟨⟨currentCall.1.1, ?_, currentCall.1.2.2⟩, currentCall.2⟩
    intro view included
    have same : view = wordView (left) := by simpa using included
    subst view
    exact currentCall.1.2.1 _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  have inputFormed := currentCall.input_formed member
  have outputFormed := currentCall.output_formed (by simp : output ∈ [output])
  obtain ⟨childFuel, after, values, invoked, result⟩ :=
    small_checked current (left) output word selected
  rw [result.underflow] at invoked
  have methodFound : Extracted.program[scalarIndex]? = some scalarBody := by
    rfl
  have instructionFound : scalarBody.code[scalarSmallCall]? =
      some (.call Extracted.subtractScalarUInt64Index 3) := by
    rfl
  have stepped : step scalarBody (.call Extracted.subtractScalarUInt64Index 3)
      scalarSmallCall (binaryArguments left right output) frame
      [.reference (.address output), .scalar (.i64 word),
        .reference (.address (left))] current =
        .ok (.call Extracted.subtractScalarUInt64Index
          (smallArguments (left) output word) [] current) := by
    simp [step, smallArguments, checkedValue, numericValue, formValue, inputFormed, outputFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned := scalar_small_return (binaryArguments left right output)
    (if (inputValue current left).toNat < word.toNat then 1 else 0) frame after
  obtain ⟨fuel, finished⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, invoked⟩ ⟨1, returned⟩
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retained := leaveFrame_preserves_memory_below frame after original.nextIdentity
    (fun id included => (fresh.2 id included).1)
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  have bytes : (fun offset => ((leaveFrame frame after).cells output.allocation offset).bits) =
      (fun offset => (after.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨fuel, leaveFrame frame after,
    [.scalar (.i32 (if (inputValue current left).toNat < word.toNat then 1 else 0))], finished,
    ⟨leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [inputValue, bytes] using result.modular_difference.trans sum
  · simp only [underflow, subtractUnderflow]
  · exact (retained.access output outputOld 32 1 true).trans result.writable
  · intro id old offset outside
    exact (retained.cells id old offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le old next) offset outside).trans (preserved.cells id old offset))

#print axioms scalar_small_finish

end UInt256Proof.Subtract.Safety

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
