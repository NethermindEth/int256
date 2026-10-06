import UInt256.Methods.Subtract.VectorSafetyCorrection
import UInt256.Methods.Subtract.VectorSafetyCascadeMath
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- Correct the output and return the mathematical underflow flag. Frame expiry
    preserves the output and every other caller allocation. -/
theorem vector_cascade_final (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (differenceHome sumHome correctionHome : Reference) (a b : Limbs)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (sumSlot : frame.locals[6]? = some (.bytes .word32 sumHome))
    (correctionSlot : frame.locals[8]? = some (.bytes .vector256 correctionHome))
    (differenceRead : read current differenceHome 32 1 =
      .ok (numberBytes (zip256 (· - ·) (value a) (value b)).toNat 32))
    (sumRead : read current sumHome 4 1 = .ok (numberBytes
      (moveMask64 (equalLanes (value a) (value b)) +
        2 * moveMask64 (generatedBorrow (value a) (value b))).toNat 4))
    (correctionRead : read current correctionHome 32 1 = .ok (numberBytes
      (cascadeVector (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b))))).toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex (vectorTestStart + 34) args frame [] current =
        .ok (final, [.scalar (.i32 (if (value a).toNat < (value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (value a - value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (value a).toNat < (value b).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (value a - value b).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 34) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_correction_output_checked original entered current inputs outputs output frame args
      call currentCall outputMember authority outputArgument differenceHome correctionHome
      (zip256 (· - ·) (value a) (value b))
      (cascadeVector (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b)))))
      differenceSlot correctionSlot differenceRead correctionRead post
    intro after readback afterCall _ outside privateReads _
    have retainedSum := privateReads _ _ _ _ (homes.home_bound 6 _ _ sumSlot) sumRead
    have executed := vector_cascade_return after frame args sumHome _ sumSlot retainedSum
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨vectorCascadeFuel, leaveFrame frame after, _, executed, ?_, ?_, ?_, ?_⟩
    · rw [vector_cascade_underflow]
    · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
      have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
      rw [teardown.read output old 32 1]
      rw [vector_cascade_difference] at readback
      exact readback
    · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
      have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
      exact (teardown.access output old 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
    · intro id offset old notOutput
      exact (teardown.cells id old offset).trans (outside id offset notOutput)
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_cascade_final
end UInt256Proof.Subtract.Safety
