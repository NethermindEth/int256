import UInt256.Methods.Subtract.VectorSafetyReturn
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete the no-propagation suffix after the early output write. All reads
    use saved private values; the caller's current bytes are preserved. -/
theorem vector_fast_tail (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftHome rightHome maskHome incomingHome : Reference) (a b : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (maskSlot : frame.locals[3]? = some (.bytes .vector256 maskHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (maskRead : read current maskHome 32 1 = .ok (numberBytes (generatedBorrow a b).toNat 32))
    (incomingRead : read current incomingHome 32 1 =
      .ok (numberBytes (incomingBorrow (generatedBorrow a b)).toNat 32))
    (fast : equalLanes a b &&& incomingBorrow (generatedBorrow a b) = 0) :
    ∃ fuel after,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] current =
        .ok (leaveFrame frame after, [.scalar (.i32 (vectorFastFlag (generatedBorrow a b)))]) ∧
      MemoryBelow original.nextIdentity current (leaveFrame frame after) := by
  let post : Memory → List Value → Prop := fun final returned => ∃ after,
    final = leaveFrame frame after ∧ returned = [.scalar (.i32 (vectorFastFlag (generatedBorrow a b)))] ∧
    MemoryBelow original.nextIdentity current after
  have finish : ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
    apply vector_propagation_checked original entered current inputs outputs frame args currentCall
      enteredWF homes authority leftHome rightHome incomingHome a b
      (incomingBorrow (generatedBorrow a b)) leftSlot rightSlot incomingSlot leftRead rightRead incomingRead post
    intro equalHome after equalSlot _ preserved earlier _ _ _
    have order := homes.ordered 3 5 .vector256 .vector256 maskHome equalHome (by decide) maskSlot equalSlot
    have retainedMask := (earlier.read maskHome order 32 1).trans maskRead
    simp only [fast, ite_true]
    exact ⟨8, leaveFrame frame after, [.scalar (.i32 (vectorFastFlag (generatedBorrow a b)))],
      vector_fast_return after frame args maskHome (generatedBorrow a b) maskSlot retainedMask,
      after, rfl, rfl, preserved⟩
  obtain ⟨fuel, final, returned, executed, after, sameFinal, sameReturned, preserved⟩ := finish
  subst final returned
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
    (fun id member => (fresh.2 id member).1)
  exact ⟨fuel, after, executed, preserved.trans teardown⟩

#print axioms vector_fast_tail

/-- From saved operands through the early output and fast return: exact modular
    subtraction and underflow, with caller-byte preservation outside output. -/
theorem vector_fast_output (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (leftHome rightHome differenceHome maskHome incomingHome : Reference) (a b : UInt256Model.Limbs)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (maskSlot : frame.locals[3]? = some (.bytes .vector256 maskHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes (UInt256Model.value a).toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes (UInt256Model.value b).toNat 32))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes
      (CIL.Vector.zip256 (· - ·) (UInt256Model.value a) (UInt256Model.value b)).toNat 32))
    (maskRead : read current maskHome 32 1 = .ok (numberBytes
      (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)).toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes
      (incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b))).toNat 32))
    (fast : equalLanes (UInt256Model.value a) (UInt256Model.value b) &&&
      incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) = 0) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (final, [.scalar (.i32 (if (UInt256Model.value a).toNat < (UInt256Model.value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (UInt256Model.value a - UInt256Model.value b).toNat 32) ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (UInt256Model.value a).toNat < (UInt256Model.value b).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (UInt256Model.value a - UInt256Model.value b).toNat 32) ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_early_output_checked original entered current inputs outputs output frame args call currentCall
      outputMember authority outputArgument differenceHome incomingHome
      (CIL.Vector.zip256 (· - ·) (UInt256Model.value a) (UInt256Model.value b))
      (incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)))
      differenceSlot incomingSlot differenceRead incomingRead post
    intro after readback afterCall afterAuthority outside privateReads _
    obtain ⟨fuel, last, executed, preserved⟩ := vector_fast_tail original entered after inputs outputs frame args
      afterCall setup enteredWF homes afterAuthority leftHome rightHome maskHome incomingHome
      (UInt256Model.value a) (UInt256Model.value b) leftSlot rightSlot maskSlot incomingSlot
      (privateReads _ _ _ _ (homes.home_bound 0 _ _ leftSlot) leftRead)
      (privateReads _ _ _ _ (homes.home_bound 1 _ _ rightSlot) rightRead)
      (privateReads _ _ _ _ (homes.home_bound 3 _ _ maskSlot) maskRead)
      (privateReads _ _ _ _ (homes.home_bound 4 _ _ incomingSlot) incomingRead) fast
    refine ⟨fuel, leaveFrame frame last, _, executed, ?_, ?_, ?_⟩
    · rw [vector_fast_branch_underflow a b fast]
    · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
      have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
      rw [preserved.read output old 32 1]
      rw [vector_fast_difference a b fast] at readback
      exact readback
    · intro id offset old notOutput
      exact (preserved.cells id old offset).trans (outside id offset notOutput)
  obtain ⟨fuel, final, returned, executed, flag, result, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, footprint⟩

#print axioms vector_fast_output
end UInt256Proof.Subtract.Safety
