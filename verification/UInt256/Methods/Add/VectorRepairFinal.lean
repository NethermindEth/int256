import UInt256.Methods.Add.VectorRepairOutput

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Checked correction store through normal return, preserving the caller's
    initialized writable output when the helper's private frame expires. -/
theorem repair_final (original entered current : Memory)
    (inputs outputs : List Reference) (output sumHome correctionHome : Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame repairBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (sumValue correctionValue : BitVec 256) (sum : BitVec 32)
    (outputArgument : args[3]? = some (.reference (.address output)))
    (sumArgument : args[0]? = some (.scalar (.v256 sumValue)))
    (sumSlot : frame.locals[0]? = some (.bytes .word32 sumHome))
    (correctionSlot : frame.locals[2]? = some (.bytes .vector256 correctionHome))
    (sumRead : read current sumHome 4 1 = .ok (numberBytes sum.toNat 4))
    (correctionRead : read current correctionHome 32 1 = .ok (numberBytes correctionValue.toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel repairIndex 32 args frame [] current =
        .ok (final, [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel repairIndex 32 args frame [] current = .ok (final, returned) ∧ post final returned := by
    apply repair_output_checked original entered current inputs outputs output correctionHome frame args
      call currentCall outputMember authority outputArgument sumValue correctionValue sumArgument
      correctionSlot correctionRead post
    intro after _ readback afterCall _ outside privateReads _
    have retainedSum := privateReads _ _ _ _ (homes.home_bound 0 _ _ sumSlot) sumRead
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    refine ⟨6, leaveFrame frame after, _, repair_return after frame args sumHome sum sumSlot retainedSum,
      rfl, ?_, ?_, ?_⟩
    · exact (teardown.read output old 32 1).trans readback
    · exact (teardown.access output old 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
    · intro id offset old notOutput
      exact (teardown.cells id old offset).trans (outside id offset notOutput)
  obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms repair_final
end UInt256Proof.Add.Safety
