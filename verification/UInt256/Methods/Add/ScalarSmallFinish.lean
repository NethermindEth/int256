import UInt256.Methods.Add.ScalarSmallPrefix
import UInt256.Methods.Add.SafetyResult

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem scalar_small_finish (swapped : Bool) (original entered current : CIL.Safety.Memory)
    (frame : Frame) (left right output : Reference) (word : BitVec 64) {flag : BitVec 32}
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) original =
      .ok (frame, entered))
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (sum : inputValue current (scalarSmallSource swapped left right) + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right)
    (naturalSum : (inputValue current (scalarSmallSource swapped left right)).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarIndex (scalarSmallCall swapped)
        (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address (scalarSmallSource swapped left right))] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  have member : scalarSmallSource swapped left right ∈ [left, right] := by
    cases swapped <;> simp [scalarSmallSource]
  have selected : CallingConditions Extracted.program current [scalarSmallSource swapped left right] [output] := by
    refine ⟨⟨currentCall.1.1, ?_, currentCall.1.2.2⟩, currentCall.2⟩
    intro view included
    have same : view = wordView (scalarSmallSource swapped left right) := by simpa using included
    subst view
    exact currentCall.1.2.1 _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  have inputFormed := currentCall.input_formed member
  have outputFormed := currentCall.output_formed (by simp : output ∈ [output])
  obtain ⟨childFuel, after, values, invoked, result⟩ :=
    small_checked current (scalarSmallSource swapped left right) output word selected
  rw [result.flagValue] at invoked
  have methodFound : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by
    simp only [cil_code]
  have instructionFound : Extracted.addScalarBody.code[scalarSmallCall swapped]? =
      some (.call Extracted.addScalarUInt64Index 3) := by
    cases swapped
    all_goals conv in (scalarSmallCall _) => cbv
    all_goals simp only [cil_code]
  have stepped : step Extracted.addScalarBody (.call Extracted.addScalarUInt64Index 3)
      (scalarSmallCall swapped) (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame
      [.reference (.address output), .scalar (.i64 word),
        .reference (.address (scalarSmallSource swapped left right))] current =
        .ok (.call Extracted.addScalarUInt64Index
          (smallArguments (scalarSmallSource swapped left right) output word) [] current) := by
    simp [step, smallArguments, checkedValue, numericValue, formValue, inputFormed, outputFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned := scalar_small_return swapped (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)])
    (smallOverflow current (scalarSmallSource swapped left right) word) frame after
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
    [.scalar (.i32 (smallOverflow current (scalarSmallSource swapped left right) word))], finished,
    ⟨leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [inputValue, bytes] using result.value.trans sum
  · simp only [smallOverflow, naturalSum, addOverflow]
  · exact (retained.access output outputOld 32 1 true).trans result.writable
  · intro id old offset outside
    exact (retained.cells id old offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le old next) offset outside).trans (preserved.cells id old offset))

#print axioms scalar_small_finish

end UInt256Proof.Safety
