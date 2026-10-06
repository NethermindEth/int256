import UInt256.Methods.Subtract.VectorSafetyCascadeExecution

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Model

/-- Both actual propagation branches preserve checked execution and return
    the same full-width subtraction and exact mathematical underflow. -/
theorem vector_branches_final (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (enteredWF : entered.WellFormed)
    (advanced : entered.nextIdentity ≤ current.nextIdentity)
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
    (outputRead : read current output 32 1 = .ok (numberBytes
      (CIL.Vector.zip256 (· + ·) (CIL.Vector.zip256 (· - ·) (UInt256Model.value a) (UInt256Model.value b))
        (incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)))).toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] current =
        .ok (final, [.scalar (.i32 (if (UInt256Model.value a).toNat < (UInt256Model.value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (UInt256Model.value a - UInt256Model.value b).toNat 32) ∧
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
      run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_propagation_checked original entered current inputs outputs frame args currentCall
      enteredWF homes authority leftHome rightHome incomingHome (value a) (value b)
      (incomingBorrow (generatedBorrow (value a) (value b))) leftSlot rightSlot incomingSlot
      leftRead rightRead incomingRead post
    intro equalHome after equalSlot equalRead preserved earlier afterCall afterAuthority next
    have maskOrder := homes.ordered 3 5 .vector256 .vector256 maskHome equalHome
      (by decide) maskSlot equalSlot
    have retainedMask := (earlier.read maskHome maskOrder 32 1).trans maskRead
    by_cases fast : equalLanes (value a) (value b) &&& incomingBorrow (generatedBorrow (value a) (value b)) = 0
    · simp only [fast, ite_true]
      have executed := vector_fast_return after frame args maskHome _ maskSlot retainedMask
      have fresh := enterFrame_fresh _ _ _ _ _ setup
      have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
        (fun id member => (fresh.2 id member).1)
      have retained := preserved.trans teardown
      refine ⟨8, leaveFrame frame after, _, executed, ?_, ?_, ?_, ?_⟩
      · rw [vector_fast_branch_underflow a b fast]
      · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
        have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
        rw [retained.read output old 32 1]
        rw [vector_fast_difference a b fast] at outputRead
        exact outputRead
      · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
        have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
        exact (teardown.access output old 32 1 true).trans
          (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
      · intro id offset old _
        exact retained.cells id old offset
    · simp only [fast, ite_false]
      have differenceOrder := homes.ordered 2 5 .vector256 .vector256 differenceHome equalHome
        (by decide) differenceSlot equalSlot
      have retainedDifference := (earlier.read differenceHome differenceOrder 32 1).trans differenceRead
      obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_cascade_execution original entered after
        inputs outputs output frame args call afterCall outputMember setup enteredWF
        (Nat.le_trans advanced next) homes afterAuthority outputArgument differenceHome maskHome equalHome a b
        differenceSlot maskSlot equalSlot retainedDifference retainedMask equalRead
      refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
      intro id offset old notOutput
      exact (footprint id offset old notOutput).trans (preserved.cells id old offset)
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_branches_final
end UInt256Proof.Subtract.Safety
