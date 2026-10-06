import UInt256.Methods.Subtract.ScalarSmallPrefix
import UInt256.Methods.Subtract.SafetyResult

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
